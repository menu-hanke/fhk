//! Runtime support functions.

use alloc::vec::Vec;
use cranelift_codegen::ir::{AbiParam, InstBuilder, TrapCode};
use cranelift_codegen::isa::CallConv;
use enumset::EnumSetType;

use crate::emit::{block2cl, irt2cl, Ecx, NATIVE_CALLCONV};
use crate::image::{fhk_vmexit, Instance};
use crate::ir::Type;
use crate::schedule::BlockId;

struct Signature<T: ?Sized=[Type]> {
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

fn ty2param(param: &mut Vec<AbiParam>, ty: &[Type]) {
    param.extend(ty.iter().map(|&t| AbiParam::new(irt2cl(t))));
}

fn sig2cl(sig: &mut cranelift_codegen::ir::Signature, si: &Signature) {
    sig.call_conv = si.cc;
    ty2param(&mut sig.returns, &si.sig[..si.ret as usize]);
    ty2param(&mut sig.params, &si.sig[si.ret as usize..]);
}

macro_rules! define_suppfuncs {
    ($(
        $name:ident
        $(($cc:expr))?
        $($arg:ident)*
        $(-> $ret:ident)?
        ;
    )*) => {
        #[derive(EnumSetType, Debug)]
        pub enum SuppFunc {
            $($name),*
        }

        const SUPPFUNC_SIGNATURE: &[&Signature] = &[
            $(
                &signature!(
                    [$($cc,)? cranelift_codegen::isa::CallConv::Fast][0],
                    $($arg)*
                    $(-> $ret)?
                )
            ),*
        ];
    };
}

macro_rules! define_nativefuncs {
    ($(
        $name:ident
        [$fp:expr]
        $($arg:ident)*
        $(-> $ret:ident)?
        ;
    )*) => {
        #[derive(EnumSetType)]
        pub enum NativeFunc {
            $($name),*
        }

        const NATIVEFUNC_PTR: &[*const ()] = &[
            $($fp as _),*
        ];

        const NATIVEFUNC_SIGNATURE: &[&Signature] = &[
            $( &signature!(NATIVE_CALLCONV, $($arg)* $(-> $ret)?)),*
        ];
    };
}

// note: all native functions must be defined before emitted functions.
define_suppfuncs! {
    INIT  PTR I32 I32;
    ALLOC I64 I64 -> PTR;
    ABORT;
    SWAP  (NATIVE_CALLCONV) PTR I64 -> I64;
}

define_nativefuncs! {
    POWF64[pow]     F64 F64 -> F64;
    EXPF64[exp]     F64 -> F64;
    LOGF64[log]     F64 -> F64;
    INIT[rt_init]   PTR PTR I32 I32;
    ALLOC[rt_alloc] PTR I64 I64 -> PTR;
    ABORT[rt_abort] PTR;
}

impl SuppFunc {

    // FIXME replace with core::mem::variant_count when it stabilizes
    pub const COUNT: usize = <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _;

    pub fn from_u8(raw: u8) -> Self {
        assert!(raw < Self::COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn signature(self, sig: &mut cranelift_codegen::ir::Signature) {
        sig2cl(sig, &SUPPFUNC_SIGNATURE[self as usize])
    }

}

impl NativeFunc {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn ptr(self) -> *const () {
        NATIVEFUNC_PTR[self as usize]
    }

    pub fn signature(self, sig: &mut cranelift_codegen::ir::Signature) {
        sig2cl(sig, &NATIVEFUNC_SIGNATURE[self as usize])
    }

}

/* ---- Math ---------------------------------------------------------------- */

#[link(name="m")]
extern "C" {
    fn pow(x: f64, y: f64) -> f64;
    fn exp(x: f64) -> f64;
    fn log(x: f64) -> f64;
}

/* ---- Init ---------------------------------------------------------------- */

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

unsafe extern "C" fn rt_init(
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

fn supp_init(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    let &[slots, num, size] = emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START))
        else { unreachable!() };
    let vmctx = emit.fb.vmctx();
    let init = emit.fb.importnative(NativeFunc::INIT);
    // would be nice if this could be a tail call, but i don't think cranelift can tail call native
    // functions
    emit.fb.ins().call(init, &[vmctx, slots, num, size]);
    emit.fb.ins().return_(&[]);
}

/* ---- Alloc --------------------------------------------------------------- */

// TODO: host should compile this function

unsafe extern "C" fn rt_alloc(vmctx: &mut Instance, size: usize, align: usize) -> *mut u8 {
    vmctx.host.alloc(size, align)
}

fn supp_alloc(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    let &[size, align] = emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START))
        else { unreachable!() };
    let alloc = emit.fb.importnative(NativeFunc::ALLOC);
    let vmctx = emit.fb.vmctx();
    let call = emit.fb.ins().call(alloc, &[vmctx, size, align]);
    let ptr = emit.fb.ctx.func.dfg.inst_results(call)[0];
    emit.fb.ins().return_(&[ptr]);
}

/* ---- Abort --------------------------------------------------------------- */

unsafe extern "C" fn rt_abort(vmctx: &mut Instance) -> ! {
    vmctx.host.set_error(b"query aborted (no suitable model)");
    fhk_vmexit(vmctx)
}

fn supp_abort(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    let abort = emit.fb.importnative(NativeFunc::ABORT);
    let vmctx = emit.fb.vmctx();
    emit.fb.ins().call(abort, &[vmctx]);
    // the call_indirect doesn't return. this trap is here just to satisfy cranelift.
    emit.fb.ins().trap(TrapCode::User(0));
}

/* -------------------------------------------------------------------------- */

pub fn emitsupport(ecx: &mut Ecx, supp: SuppFunc) {
    use SuppFunc::*;
    match supp {
        INIT   => supp_init(ecx),
        ALLOC  => supp_alloc(ecx),
        ABORT  => supp_abort(ecx),
        SWAP   => unreachable!() // asm function
    }
}
