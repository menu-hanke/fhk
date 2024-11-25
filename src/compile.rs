//! Compiler pipeline.

use core::mem::{transmute, ManuallyDrop};

use zerocopy::IntoBytes;

use crate::bump::{Bump, BumpRef};
use crate::dl::DynLibs;
use crate::emit::Emit;
use crate::finalize::FinalizerBuilder;
use crate::host::HostCtx;
use crate::image::Image;
use crate::intern::{Intern, IRef};
use crate::ir::IR;
use crate::layout::ComputeLayout;
use crate::lex::Token;
use crate::link::Link;
use crate::lower::Lower;
use crate::mcode::MCode;
use crate::mem::{Layout, ResetSeq};
use crate::obj::Objects;
use crate::optimize::Optimize;
use crate::parser::Parser;
use crate::typeinfer::TypeInfer;
use crate::typestate::{typestate_union, Absent, Access, R, RW};

pub type Result<T=()> = core::result::Result<T, ()>;

pub trait Phase: Sized {
    fn new(ccx: &mut Ccx<Absent>) -> Result<Self>;
    fn run(_: &mut Ccx<Self>) -> Result { Ok(()) }
}

impl Phase for Absent {
    fn new(_: &mut Ccx<Absent>) -> Result<Self> { Ok(Self) }
}

pub unsafe trait PhaseMarker: Phase {}

macro_rules! define_phases {
    ($( $name:ident $data:ty; )*) => {
        typestate_union! {
            pub union PhaseData:_PhaseData {
                $( $name: $data ),*
            }
        }
        $( unsafe impl PhaseMarker for $data {} )*
    };
}

define_phases! {
    ABSENT      Absent;
    PARSE       Parser;
    TYPE        TypeInfer;
    LOWER       Lower;
    OPTIMIZE    Optimize;
    LAYOUT      ComputeLayout;
    EMIT        Emit;
    LINK        Link;
}

#[repr(C)] // need repr(C) for transmuting references.
pub struct Ccx<P=Absent, O=RW, I=RW> {
    // current phase data
    pub data: PhaseData<P>,
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
    // dynamic library handles
    pub dynlibs: DynLibs,
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
}

pub struct CompilePhase<'a, P, T: PhaseMarker> {
    pub ccx: &'a mut Ccx<P, RW, RW>,
    pub data: ManuallyDrop<T>
}

impl Ccx {

    pub const SEQ_GLOBAL: IRef<[u8]> = IRef::small_from_end_size(11, 5);

    pub fn new(host: HostCtx) -> Self {
        let mut intern = Intern::default();
        let global_str = intern.intern("global");
        debug_assert!(global_str == IRef::small_from_end_size(6, 6));
        intern.write(&(Token::Ident as u8));
        intern.write(global_str.as_bytes()); // must be unaligned
        let global_seq = intern.intern_consume_from(BumpRef::from_offset(6));
        debug_assert!(global_seq == Self::SEQ_GLOBAL);
        Self {
            host,
            ir: Default::default(),
            objs: Default::default(),
            resets: Default::default(),
            perm: Default::default(),
            tmp: Default::default(),
            intern,
            dynlibs: Default::default(),
            fin: Default::default(),
            data: Default::default(),
            mcode: Default::default(),
            image: Default::default(),
            layout: Default::default(),
        }
    }

}

impl<P: PhaseMarker> Ccx<P, RW, RW> {

    pub fn begin<PP: PhaseMarker>(&mut self) -> Result<CompilePhase<'_, PP, P>> {
        // safety: transmute to absent, new can't do anything to data.
        let new = ManuallyDrop::new(PP::new(unsafe { transmute(&mut *self) })?);
        // safety: self.data contains a valid P
        let data = ManuallyDrop::new(unsafe { core::ptr::read(&self.data as *const _  as *const P) });
        // safety: PhaseData is a repr(C) union containing PP
        let ccx: &mut Ccx<PP> = unsafe {
            core::ptr::write(&mut self.data as *mut _ as _, new);
            transmute(self)
        };
        Ok(CompilePhase { ccx, data })
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

impl<'a, P, T: PhaseMarker> CompilePhase<'a, P, T> {

    pub fn leak(self) -> &'a mut Ccx<P, RW, RW> {
        let ccx = self.ccx as *mut _;
        core::mem::forget(self);
        unsafe { &mut *ccx }
    }

}

impl<'a, P, T: PhaseMarker> Drop for CompilePhase<'a, P, T> {
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

fn run<P: PhaseMarker>(ccx: &mut Ccx) -> Result {
    P::run(ccx.begin::<P>()?.ccx)
}

impl Ccx {

    pub fn compile(&mut self) -> Result {
        run::<TypeInfer>(self)?;
        run::<Lower>(self)?;
        run::<Optimize>(self)?;
        // run::<RemoveFx>(self)?;
        run::<ComputeLayout>(self)?;
        run::<Emit>(self)?;
        run::<Link>(self)?;
        Ok(())
    }

}
