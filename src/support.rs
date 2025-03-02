//! Runtime support functions.

use core::mem::replace;

use cranelift_codegen::ir::{InstBuilder, TrapCode};
use enumset::EnumSetType;

use crate::controlflow::BlockId;
use crate::emit::{block2cl, signature, Ecx, Signature, NATIVE_CALLCONV};
use crate::image::{fhk_vmexit, DupHeader, Instance};
use crate::ir::Type;
use crate::mem::Offset;

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

// TODO: consider language-specific suppfuncs (and nativefuncs), similar to ir::LangOp.
// probably not needed currently since it's only used by R and only for one function,
// but if eg. python needs it in the future it should probably go here rather than doing it
// inside each lang.
// add the suppfunc and nativefunc tables as constants in the Language trait?
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

    pub fn signature(self) -> &'static Signature {
        SUPPFUNC_SIGNATURE[self as usize]
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

    pub fn signature(self) -> &'static Signature {
        NATIVEFUNC_SIGNATURE[self as usize]
    }

}

/* ---- Math ---------------------------------------------------------------- */

#[link(name="m")]
unsafe extern "C" {
    fn pow(x: f64, y: f64) -> f64;
    fn exp(x: f64) -> f64;
    fn log(x: f64) -> f64;
}

/* ---- Init ---------------------------------------------------------------- */

/*
 *         +--------+---+-----+------+
 *         |  31..5 | 4 |  3  | 2..0 |
 *         +========+===+=====+======+
 * data    | offset | 0 |    size    |
 *         +--------+---+-----+------+
 * bitmap  | offset | 1 | dup |  bit |
 *         +--------+---+-----+------+
 */
#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct DynSlot(u32);

impl DynSlot {

    pub fn new_data(ofs: Offset, size: u32) -> Self {
        debug_assert!((ofs as usize) & (Type::PTR.size() - 1) == 0);
        Self((ofs << 5) | size)
    }

    pub fn new_bitmap(ofs: Offset, dup: bool, bit: u32) -> Self {
        debug_assert!((ofs as usize) & (Type::PTR.size() - 1) == 0);
        Self((ofs << 5) | (1 << 4) | ((dup as u32) << 3) | bit)
    }

    fn offset(self) -> Offset {
        self.0 >> 5
    }

    fn is_bitmap(self) -> bool {
        self.0 & (1 << 4) != 0
    }

    fn size(self) -> u32 {
        debug_assert!(!self.is_bitmap());
        self.0 & 0xf
    }

    fn bit(self) -> u32 {
        debug_assert!(self.is_bitmap());
        self.0 & 0x7
    }

    fn is_dup(self) -> bool {
        debug_assert!(self.is_bitmap());
        self.0 & (1 << 3) != 0
    }

}

unsafe extern "C" fn rt_init(vmctx: &mut Instance, slots: *const DynSlot, num: u32, size: u32) {
    let slots = unsafe { core::slice::from_raw_parts(slots, num as _) };
    for &slot in slots {
        let ofs = slot.offset();
        let ptr = unsafe { (vmctx as *mut _ as *mut u8).add(ofs as _) } as *mut *mut u8;
        let data = match slot.is_bitmap() {
            true => {
                // round to 8 so that it can be cleared one 64-bit word at a time.
                let size = (size + 7) & !7;
                if !(unsafe { *ptr }).is_null() {
                    let words = unsafe {
                        core::slice::from_raw_parts_mut(*ptr as *mut u64, (size>>3) as _)
                    };
                    let mask = 0x0101010101010101 * 0xfeu8.rotate_left(slot.bit()) as u64;
                    for word in words { *word &= mask; }
                    continue
                }
                let data = match slot.is_dup() {
                    true => {
                        debug_assert!(size_of::<DupHeader>() == 8); // must match alignment
                        let data = vmctx.host.alloc((size+8) as _, 8) as *mut DupHeader;
                        unsafe {
                            *data = DupHeader {
                                size,
                                next: replace(&mut vmctx.dup, ofs)
                            };
                            data.add(1) as _
                        }
                    },
                    false => vmctx.host.alloc(size as _, 8)
                };
                unsafe { core::ptr::write_bytes(data, 0, size as _); }
                data
            },
            false => {
                let ss = slot.size();
                vmctx.host.alloc((ss*size) as _, ss as _)
            }
        };
        unsafe {
            // *don't* use `ptr` here, it's UB because we access the vmctx reference in between.
            *((vmctx as *mut _ as *mut u8).add(ofs as _) as *mut *mut u8) = data;
        }
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
    unsafe { fhk_vmexit(vmctx) }
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
