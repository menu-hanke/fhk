//! Compiler pipeline.

use core::mem::{transmute, ManuallyDrop};

use enumset::EnumSet;

use crate::bump::Bump;
use crate::emit::Emit;
use crate::finalize::FinalizerBuilder;
use crate::host::HostCtx;
use crate::image::Image;
use crate::index::IndexSet;
use crate::intern::{Intern, Interned};
use crate::ir::{InsId, IR};
use crate::layout::ComputeLayout;
use crate::lex::Token;
use crate::link::Link;
use crate::lower::Lower;
use crate::mcode::MCode;
use crate::mem::{Layout, ResetSeq};
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
    LINK        Link;
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
    // reset id allocation
    pub resets: ResetSeq,
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
    // finalizers
    pub fin: FinalizerBuilder,
    // vmctx memory layout information
    pub layout: Layout,
    // mcode functions and data
    pub mcode: MCode,
    // host state
    pub host: HostCtx,
    // compilation result
    pub image: Option<Image>,
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

    pub fn new(host: HostCtx) -> Self {
        let mut intern = Intern::default();
        let global_str: Interned<[u8]> = intern.intern(b"global");
        debug_assert!(global_str == Interned::small_from_raw_parts(0, 6));
        let global_str: [u8; 4] = zerocopy::transmute!(global_str);
        let global_seq: Interned<[u8]> = intern.intern(&[Token::Ident as u8, global_str[0],
            global_str[1], global_str[2], global_str[3]]);
        debug_assert!(global_seq == Self::SEQ_GLOBAL);
        Self {
            host,
            ir: Default::default(),
            objs: Default::default(),
            resets: Default::default(),
            perm: Default::default(),
            tmp: Default::default(),
            intern,
            fin: Default::default(),
            data: Default::default(),
            mcode: Default::default(),
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
    #[cold]
    fn write(self, ccx: &mut Ccx<P, R, R>);
}

// shorthand so that you don't have to write ccx.erase().error(...) for generic errors.
impl<T,P> CompileError<P> for T where T: CompileError<()>, P: StageMarker {
    fn write(self, ccx: &mut Ccx<P, R, R>) {
        self.write(ccx.erase())
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

    #[inline(never)]
    #[cold]
    fn do_error<E>(&mut self, e: E)
        where E: CompileError<P>
    {
        self.host.buf.clear();
        // safety: this is basically the same as calling erase+freeze_ir+freeze_graph but without
        // the necessary type acrobatics
        e.write(unsafe { transmute(self) });
    }

    // this is split to avoid monomorphization for each T
    #[inline(always)]
    pub fn error<T,E>(&mut self, e: E) -> Result<T>
        where E: CompileError<P>
    {
        self.do_error(e);
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

    pub fn compile(&mut self) -> Result {
        run::<TypeInfer>(self)?;
        run::<Lower>(self)?;
        run::<Optimize>(self)?;
        run::<ComputeLayout>(self)?;
        run::<Emit>(self)?;
        run::<Link>(self)?;
        Ok(())
    }

}
