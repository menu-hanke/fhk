//! Runtime support functions.

use alloc::collections::vec_deque::VecDeque;
use alloc::vec::Vec;
use cranelift_codegen::ir::{AbiParam, InstBuilder};
use cranelift_codegen::isa::CallConv;
use enumset::EnumSetType;
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;

use crate::bump::{self, Aligned, Bump, BumpRef};
use crate::emit::{self, block2cl, irt2cl, Ecx, NATIVE_CALLCONV};
use crate::hash::fxhash;
use crate::image::Instance;
use crate::index::InvalidValue;
use crate::ir::Type;
use crate::mcode::{Label, MCode};
use crate::schedule::BlockId;

// type or vmctx
#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct Arg(u8);

impl Arg {

    pub const VMCTX: Self = Self(!0);

    pub fn param(type_: Type) -> Self {
        Self(type_ as _)
    }

}

// see https://github.com/google/zerocopy/issues/170
// (this can be replaced with a raw pointer when the above issue is resolved)
pub type FuncPtr = usize;

// marker for type bounds
pub trait SuppFuncType: Aligned + bump::FromBytes + bump::IntoBytes + bump::Immutable {}

#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C,align(4))]
pub struct Supp {
    pub label: Label,
    pub sf: u8, // enum SuppFunc
    _pad: u8,
    // data follows
}

impl SuppFuncType for Supp {}

macro_rules! define_suppfuncs {
    (@new ($($args:tt)*) ($($body:tt)*)) => {
        pub fn new($($args)*) -> Self {
            Self { label: Label::INVALID.into(), $($body)* }
        }
    };
    (@new ($($args:tt)*) ($($body:tt)*) pub $field:ident: $type:ty $(,$($rest:tt)*)?) => {
        define_suppfuncs!(@new ($($args)* $field: $type,) ($($body)* $field,) $($($rest)*)? );
    };
    (@new ($($args:tt)*) ($($body:tt)*) $field:ident: $type:ty $(,$($rest:tt)*)?) => {
        define_suppfuncs!(@new ($($args)*) ($($body)* $field: Default::default(),) $($($rest)*)?);
    };
    (@struct $name:ident $($fields:tt)*) => {
        #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
        #[repr(C,align(4))]
        pub struct $name {
            pub label: Label,
            pub sf: u8,
            $($fields)*
        }
        impl SuppFuncType for $name {}
    };
    ($($name:ident { $($fields:tt)* };)*) => {
        #[derive(EnumSetType)]
        pub enum SuppFunc {
            $( $name ),*
        }
        // impl Supp {
        //     $( pub const $name: u8 = SuppFunc::$name as _; )*
        // }
        $(
            define_suppfuncs!(@struct $name $($fields)*);
            impl $name {
                define_suppfuncs!(@new () (sf: SuppFunc::$name as _,) $($fields)*);
            }
        )*
    };
}

define_suppfuncs! {
    DSINIT { _pad: u8 };
    ALLOC { _pad: u8 };
    SWAP { _pad: u8 };
    // TRAMPOLINE { pub n: u8, _pad: u16, pub args: BumpRef<[Arg]>, pub func: FuncPtr };
    // TODO: vector arithmetic, memcpy, traps, etc.
}

impl SuppFunc {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

}

// marker for bumpref in supp.bump
pub type SuppRef<T=Supp> = BumpRef<T>;

struct Signature<T: ?Sized = [Type]> {
    cc: CallConv,
    ret: u8,
    sig: T
}

macro_rules! signature {
    ($cc:expr, $($arg:ident)* $(-> $($ret:ident)*)?) => {
        Signature {
            cc: $cc,
            ret: 0 $( $(+ {let $ret = 1; $ret})* )?,
            sig: [
                $($($crate::ir::Type::$ret,)*)?
                $($crate::ir::Type::$arg,)*
            ]
        }
    };
    ($cc:ident $($arg:ident)* $(-> $($ret:ident)*)?) => {
        signature!(cranelift_codegen::isa::CallConv::$cc, $($arg)* $(-> $($ret)*)?)
    };
}

#[derive(Default)]
pub struct SupportFuncs {
    bump: Bump<u32>,
    hash: HashTable<SuppRef>,
    pub work: VecDeque<SuppRef>,
}

fn suppbytes<T>(supp: &T) -> &[u8]
    where T: SuppFuncType
{
    // first two bytes are label, which does not affect hash or equality
    let bytes = unsafe {
        core::slice::from_raw_parts(supp as *const T as *const u8, size_of_val(supp))
    };
    &bytes[2..]
}

impl SupportFuncs {

    pub fn instantiate<T: SuppFuncType>(&mut self, mcode: &mut MCode, supp: &T) -> SuppRef<T> {
        let bytes = suppbytes(supp);
        match self.hash.entry(
            fxhash(bytes),
            |&s| suppbytes(&self.bump[s]) == bytes,
            |&s| fxhash(suppbytes(&self.bump[s]))
        ) {
            Entry::Occupied(e) => e.get().cast(),
            Entry::Vacant(e) => {
                let sr = self.bump.write(supp);
                self.bump[sr.cast::<Supp>()].label = mcode.labels.push(0);
                self.work.push_back(sr.cast());
                e.insert(sr.cast());
                sr
            }
        }
    }

}

const SIG_DSINIT: &Signature = &signature!(Fast PTR I32 I32); // (slots, num, size)
const SIG_ALLOC: &Signature = &signature!(Fast I64 I64 -> PTR); // (bytes, align) -> mem
const SIG_SWAP: &Signature = &signature!(emit::NATIVE_CALLCONV, PTR I64 -> I64);

fn ty2param(param: &mut Vec<AbiParam>, ty: &[Type]) {
    param.extend(ty.iter().map(|&t| AbiParam::new(irt2cl(t))));
}

fn sig2cl(sig: &mut cranelift_codegen::ir::Signature, si: &Signature) {
    sig.call_conv = si.cc;
    ty2param(&mut sig.returns, &si.sig[..si.ret as usize]);
    ty2param(&mut sig.params, &si.sig[si.ret as usize..]);
}

fn newsig(si: &Signature) -> cranelift_codegen::ir::Signature {
    let mut sig = cranelift_codegen::ir::Signature::new(CallConv::Fast);
    sig2cl(&mut sig, si);
    sig
}

impl SupportFuncs {

    pub fn signature(&self, sig: &mut cranelift_codegen::ir::Signature, supp: SuppRef) {
        use SuppFunc::*;
        let si = match SuppFunc::from_u8(self[supp].sf) {
            DSINIT => SIG_DSINIT,
            ALLOC  => SIG_ALLOC,
            SWAP   => SIG_SWAP
        };
        sig2cl(sig, si);
    }

}

impl<T: SuppFuncType> core::ops::Index<SuppRef<T>> for SupportFuncs {
    type Output = T;
    fn index(&self, index: SuppRef<T>) -> &T {
        &self.bump[index]
    }
}

impl<T: SuppFuncType> core::ops::IndexMut<SuppRef<T>> for SupportFuncs {
    fn index_mut(&mut self, index: SuppRef<T>) -> &mut T {
        &mut self.bump[index]
    }
}

/* ---- DSINIT -------------------------------------------------------------- */

/*
 * +--------+------+------+
 * |  31..5 | 4..1 |   0  |
 * +========+======+======+
 * | offset | size | zero |
 * +--------+------+------+
 */
#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct DynSlot(u32);

impl DynSlot {

    pub fn new(ofs: u32, type_: Type) -> Self {
        Self(
            (ofs << 5)
            | ((type_.size() as u32) << 1)
            | ((type_ == Type::B1) as u32)
        )
    }

    fn offset(self) -> u32 {
        self.0 >> 5
    }

    fn size(self) -> u32 {
        (self.0 >> 1) & 0xf
    }

    fn zero(self) -> bool {
        (self.0 & 1) != 0
    }

}

const SIG_DSINIT_FF: &Signature = &signature!(NATIVE_CALLCONV, PTR PTR I32 I32);
unsafe extern "C" fn sfunc_dsinit(
    vmctx: &mut Instance,
    slots: *const DynSlot,
    num: u32,
    size: u32
) {
    let raw = vmctx as *mut _ as *mut u8;
    let slots = core::slice::from_raw_parts(slots, num as _);
    for &slot in slots {
        // TODO: store colocated bit in dynslot
        let colo = slot.zero();
        let pptr = raw.add(slot.offset() as _) as *mut *mut u8;
        if colo && !(*pptr).is_null() { continue; }
        let elemsize = slot.size();
        let slotsize = size*elemsize;
        let ptr = vmctx.host.alloc(slotsize as _, elemsize as _);
        if slot.zero() { core::ptr::write_bytes(ptr, 0, slotsize as _); }
        *pptr = ptr;
    }
}

fn supp_dsinit(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    let &[slots, num, size] = emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START))
        else { unreachable!() };
    let sigref = emit.fb.ctx.func.import_signature(newsig(SIG_DSINIT_FF));
    let fptr = emit.fb.ins().iconst(irt2cl(Type::PTR), sfunc_dsinit as i64);
    let vmctx = emit.fb.vmctx();
    // would be nice if this could be a tail call, but i don't think cranelift can tail call native
    // functions
    emit.fb.ins().call_indirect(sigref, fptr, &[vmctx, slots, num, size]);
    emit.fb.ins().return_(&[]);
}

/* ---- ALLOC --------------------------------------------------------------- */

// TODO: host should compile this function

const SIG_ALLOC_FF: &Signature = &signature!(NATIVE_CALLCONV, PTR I64 I64 -> PTR);
unsafe extern "C" fn sfunc_alloc(vmctx: &mut Instance, size: usize, align: usize) -> *mut u8 {
    vmctx.host.alloc(size, align)
}

fn supp_alloc(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    let &[size, align] = emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START))
        else { unreachable!() };
    let sigref = emit.fb.ctx.func.import_signature(newsig(SIG_ALLOC_FF));
    let fptr = emit.fb.ins().iconst(irt2cl(Type::PTR), sfunc_alloc as i64);
    let vmctx = emit.fb.vmctx();
    let call = emit.fb.ins().call_indirect(sigref, fptr, &[vmctx, size, align]);
    let ptr = emit.fb.ctx.func.dfg.inst_results(call)[0];
    emit.fb.ins().return_(&[ptr]);
}

/* -------------------------------------------------------------------------- */

pub fn emitsupport(ecx: &mut Ecx, supp: SuppRef) {
    use SuppFunc::*;
    let emit = &mut *ecx.data;
    match SuppFunc::from_u8(emit.supp[supp].sf) {
        DSINIT => supp_dsinit(ecx),
        ALLOC  => supp_alloc(ecx),
        SWAP   => unreachable!() // asm function
    }
}
