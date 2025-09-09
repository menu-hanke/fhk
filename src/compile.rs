//! Compiler pipeline.

use core::fmt::Display;
use core::iter::zip;
use core::mem::{transmute, ManuallyDrop};

use enumset::EnumSet;

use crate::bump::Bump;
use crate::emit::Emit;
use crate::host::HostCtx;
use crate::image::{Image, ImageBuilder};
use crate::index::IndexSet;
use crate::intern::{Intern, Interned};
use crate::ir::{InsId, IR};
use crate::layout::ComputeLayout;
use crate::lex::Token;
use crate::lower::Lower;
use crate::mem::Layout;
use crate::obj::Objects;
use crate::optimize::{OptFlag, Optimize};
use crate::parser::Parser;
use crate::typeinfer::TypeInfer;
use crate::typestate::{typestate_union, Absent, Access, R, RW};

pub type Result<T=()> = core::result::Result<T, ()>;

pub trait Stage: Sized {
    fn new(ccx: &mut Ccx<Absent>) -> Result<Self>;
    fn run(_: &mut Ccx<Self>) -> Result { Ok(()) }
}

macro_rules! define_stages {
    ($( $name:ident $data:ty; )*) => {
        typestate_union! {
            pub union StageData:_StageData {
                $($name: $data),*
            }
        }
        $( unsafe impl StageMarker for $data {} )*
    };
}

pub unsafe trait StageMarker: Stage {}

define_stages! {
    // special "pseudo"-stages
    ABSENT      Absent;       // no stage data, can create a new one
    // actual stages
    PARSE       Parser;
    TYPE        TypeInfer;
    LOWER       Lower;
    OPTIMIZE    Optimize;
    LAYOUT      ComputeLayout;
    EMIT        Emit;
}

impl Stage for Absent { fn new(_: &mut Ccx<Absent>) -> Result<Self> { Ok(Self) } }
impl Stage for () { fn new(_: &mut Ccx<Absent>) -> Result<Self> { unreachable!() } }

#[repr(C)] // need repr(C) for transmuting references.
pub struct Ccx<P=(), O=RW, I=RW> {
    // current stage data
    pub data: StageData<P>,
    // object graph
    pub objs: Access<Objects, O>,
    // IR
    pub ir: Access<IR, I>,
    // memory for miscellaneous allocs that must live until the end of the compilation
    pub perm: Bump,
    // memory for temporary function-local allocs
    // user should always reset this before returning
    // idiom:
    //   let base = tmp.end()
    //   /* ... use tmp ... */
    //   tmp.truncate(base)
    pub tmp: Bump,
    // interned byte strings (names, templates, extfuncs etc)
    pub intern: Intern,
    // host state
    pub host: HostCtx,
    // image state
    pub image: ImageBuilder,
    // memory layout
    pub layout: Layout,
    // optimization flags
    pub flags: EnumSet<OptFlag>,
    // markers for algorithms
    pub mark1: IndexSet<InsId>,
    pub mark2: IndexSet<InsId>
}

pub struct CompileStage<'a, P, T: StageMarker> {
    pub ccx: &'a mut Ccx<P, RW, RW>,
    pub data: ManuallyDrop<T>
}

impl Ccx<Absent> {

    pub const SEQ_GLOBAL: Interned<[u8]> = Interned::small_from_raw_parts(6, 5);
    pub const SEQ_STATE: Interned<[u8]> = Interned::small_from_raw_parts(16, 5);
    pub const SEQ_QUERY: Interned<[u8]> = Interned::small_from_raw_parts(26, 5);

    pub fn new(host: HostCtx) -> Self {
        let mut intern = Intern::default();
        const BUILTIN_NAMES: &[&[u8]] = &[b"global", b"state", b"query"];
        const BUILTIN_SEQS: &[Interned<[u8]>] = &[Ccx::SEQ_GLOBAL, Ccx::SEQ_STATE, Ccx::SEQ_QUERY];
        for (&name, &seq) in zip(BUILTIN_NAMES, BUILTIN_SEQS) {
            let name_intern = intern.intern(name);
            let name_intern: [u8; 4] = zerocopy::transmute!(name_intern);
            let seq_intern: Interned<[u8]> = intern.intern(&[Token::Ident as u8, name_intern[0],
                name_intern[1], name_intern[2], name_intern[3]]);
            debug_assert!(seq_intern == seq);
        }
        Self {
            host,
            ir: Default::default(),
            objs: Default::default(),
            perm: Default::default(),
            tmp: Default::default(),
            intern,
            data: Default::default(),
            image: Default::default(),
            layout: Default::default(),
            flags: EnumSet::all(),
            mark1: Default::default(),
            mark2: Default::default()
        }
    }

}

impl<P: StageMarker> Ccx<P, RW, RW> {

    pub fn begin<PP: StageMarker>(&mut self) -> Result<CompileStage<'_, PP, P>> {
        // safety: transmute to absent, new can't do anything to data.
        let new = ManuallyDrop::new(PP::new(unsafe { transmute(&mut *self) })?);
        // safety: self.data contains a valid P
        let data = ManuallyDrop::new(unsafe { core::ptr::read(&self.data as *const _  as *const P) });
        // safety: StageData is a repr(C) union containing PP
        let ccx: &mut Ccx<PP> = unsafe {
            core::ptr::write(&mut self.data as *mut _ as _, new);
            transmute(self)
        };
        Ok(CompileStage { ccx, data })
    }

}

impl<P,G> Ccx<P, G, RW> {

    pub fn freeze_ir<F,T>(&mut self, func: F) -> T
        where for<'a> F: FnOnce(&mut Ccx<P, G, R<'a>>) -> T
    {
        // safety: `func` can not safely construct a value that could be written into self.ir
        // (or self, of course)
        func(unsafe { transmute(self) })
    }

}

impl<P,I> Ccx<P, RW, I> {

    pub fn freeze_graph<F,T>(&mut self, func: F) -> T
        where for<'a> F: FnOnce(&mut Ccx<P, R<'a>, I>) -> T
    {
        // safety: `func` can not safely construct a value that could be written into self.graph
        func(unsafe { transmute(self) })
    }

}

pub trait CompileError<P=()> {
    fn report(self, ccx: &mut Ccx<P, R, R>);
}

#[repr(transparent)]
pub struct FFIError([u8]);

impl<T,P> CompileError<P> for T where T: Display {
    fn report(self, ccx: &mut Ccx<P, R, R>) {
        ccx.host.set_error(format_args!("{}", self));
    }
}

impl FFIError {

    pub fn from_bytes(bytes: &[u8]) -> &Self {
        unsafe { core::mem::transmute(bytes) }
    }

    pub fn from_cstr(s: &core::ffi::CStr) -> &Self {
        Self::from_bytes(s.to_bytes())
    }

}

impl Display for FFIError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match str::from_utf8(&self.0) {
            Ok(message) => f.write_str(message),
            Err(err) => write!(f, "bad utf-8: {} (raw bytes: {:?})", err, &self.0)
        }
    }
}

impl<P,G,I> Ccx<P,G,I> {

    pub fn erase(&mut self) -> &mut Ccx<(), G, I> {
        // safety: caller cannot (safely) overwrite current stage data:
        //   * `()` doesn't implement StageMarker so they can't call begin()
        //   * there is no way to safely obtain an instance of StageData<()>, so they can't set
        //     it directly
        unsafe { transmute(self) }
    }

    #[cold]
    pub fn error<T,E>(&mut self, e: E) -> Result<T>
        where E: CompileError<P>
    {
        // safety: this is basically the same as calling erase+freeze_ir+freeze_graph but without
        // the necessary type acrobatics
        e.report(unsafe { transmute(self) });
        Err(())
    }

}

impl<'a, P, T: StageMarker> CompileStage<'a, P, T> {

    pub fn leak(self) -> &'a mut Ccx<P, RW, RW> {
        let ccx = self.ccx as *mut _;
        core::mem::forget(self);
        unsafe { &mut *ccx }
    }

}

impl<'a, P, T: StageMarker> Drop for CompileStage<'a, P, T> {
    fn drop(&mut self) {
        // safety: ccx.data contains a valid P and we have a valid T,
        // which is a field in the repr(C) union ccx.data
        unsafe {
            core::ptr::drop_in_place(&mut self.ccx.data);
            core::ptr::write(
                &mut self.ccx.data as *mut _ as _,
                ManuallyDrop::take(&mut self.data)
            )
        }
    }
}

fn run<P: StageMarker>(ccx: &mut Ccx<Absent>) -> Result {
    P::run(ccx.begin::<P>()?.ccx)
}

impl Ccx<Absent> {

    pub fn compile(&mut self) -> Result<Image> {
        run::<TypeInfer>(self)?;
        run::<Lower>(self)?;
        run::<Optimize>(self)?;
        run::<ComputeLayout>(self)?;
        run::<Emit>(self)?;
        self.image.build()
    }

}
