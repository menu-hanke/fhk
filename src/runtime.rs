//! Runtime functions.

use core::arch::global_asm;
use core::marker::PhantomData;
use core::mem::{offset_of, replace, MaybeUninit};
use core::ptr::NonNull;

use cfg_if::cfg_if;
use cranelift_codegen::ir::{InstBuilder, TrapCode};
use enumset::EnumSetType;

use crate::bump::Bump;
use crate::controlflow::BlockId;
use crate::emit::{block2cl, signature, Ecx, Signature, NATIVE_CALLCONV};
use crate::image::{Image, Instance};
use crate::ir::Type;
use crate::mem::Offset;
use crate::obj::{ObjRef, ObjectRef, Objects, TPRI, TTEN};
use crate::typing::Primitive;

// integer types to use for indexing.
pub const PRI_IDX: Primitive = Primitive::I32;
pub const IRT_IDX: Type = PRI_IDX.to_ir();
pub type Idx = u32;

/* ---- VM call/exit -------------------------------------------------------- */

#[cfg(all(target_arch="x86_64", unix))]
global_asm!("
.hidden fhk_vmcall_sysv
.hidden fhk_vmexit
");

#[cfg(target_arch="x86_64")]
global_asm!("
.p2align 4
.global fhk_vmcall_sysv
.global fhk_vmexit
// (result[rdi], mcode[rsi], vmctx[rdx]) -> status[rax]
fhk_vmcall_sysv:
    push r12                            // save all callee-save regs for fhk_vmexit
    push r13
    push r14
    push r15
    push rbx
    push rbp
    mov [rdx+{vmctx_rsp}], rsp          // save stack for fhk_vmexit
    push rcx                            // align stack for call
    mov r15, rdx                        // pinned reg = vmctx
    call rsi                            // call mcode(result)
    pop rcx                             // realign stack
    xor eax, eax                        // status = 0
1:
    pop rbp
    pop rbx
    pop r15
    pop r14
    pop r13
    pop r12
    ret
fhk_vmexit:
    mov rsp, [r15+{vmctx_rsp}]          // restore stack
    mov eax, 1                          // status = 1
    jmp 1b
",
    vmctx_rsp = const offset_of!(Instance, sp),
);

#[allow(improper_ctypes)]
unsafe extern "sysv64" {
    pub fn fhk_vmcall_sysv(result: *mut u8, mcode: *const u8, vmctx: *mut Instance) -> i32;
    #[cold]
    pub fn fhk_vmexit(vmctx: *mut Instance) -> !;
}

cfg_if! {
    if #[cfg(any(windows, all(target_os="macos", target_arch="aarch64")))] {
        pub unsafe extern "C" fn fhk_vmcall(
            result: *mut u8,
            mcode: *const u8,
            vmctx: *mut Instance
        ) -> i32 {
            unsafe { fhk_vmcall_sysv(result, mcode, vmctx) }
        }
    } else {
        pub use fhk_vmcall_sysv as fhk_vmcall;
    }
}

/* ---- Stack swapping ------------------------------------------------------ */

// NOTE: cranelift has a `stack_switch` implementation which currently only supports x64 linux.
// eventually this whole thing should be replaced by that.

#[cfg(all(target_arch="x86_64", unix))]
global_asm!("
.p2align 4
.hidden fhk_swap
.global fhk_swap
// (coro[rdi], ret_out[rsi]) -> ret_in[rax]
fhk_swap:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    mov rax, [rdi]    // rax = coro.sp
    mov [rdi], rsp    // coro.sp = rsp
    mov rsp, rax      // swap to coro stack
    mov rax, rsi      // rax = return value on coro stack
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret

.hidden fhk_swap_exit
.global fhk_swap_exit
// coro[rdi] -> ret[rax]
fhk_swap_exit:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    mov rax, [rdi]        // rax = coro.sp
    mov [rdi], rsp        // coro.sp = rsp
    mov r15, [rax]        // r15 = vmctx
    jmp fhk_vmexit

.hidden fhk_swap_init
.global fhk_swap_init
// swap[rdi]
fhk_swap_init:
    mov rax, [rdi+0x08]   // rax = sp
    lea rsi, [rip+1f]     // rsi = label 1f
    mov [rax-0x08], rsi   // return address = label 1f
    mov rcx, rdi          // rcx = swap
    mov rdi, [rdi]        // rdi = coro
    sub rax, 56           // 6 gprs + return addr = 56 bytes
    mov [rdi], rax        // coro.sp = stack
    jmp fhk_swap
1:
    mov rdi, [rcx+0x18]   // rdi = swap.ctx
    call [rcx+0x10]       // call swap.func
    ud2                   // (must never return)

.hidden fhk_swap_instance
.global fhk_swap_instance
// coro[rdi] -> vmctx[rax]
fhk_swap_instance:
    mov rax, [rdi]
    mov rax, [rax]
    ret
");

#[cfg(all(target_arch="x86_64", windows))]
global_asm!("
.p2align 4
.global fhk_swap
// (coro[rcx], ret_out[rdx]) -> ret_in[rax]
fhk_swap:
    mov rax, gs:0x30
    mov r8, [rax+0x08]
    push r8
    mov r8, [rax+0x10]
    push r8
    push rbx
    sub rsp, 160
    vmovaps [rsp],     xmm6
    vmovaps [rsp+16],  xmm7
    vmovaps [rsp+32],  xmm8
    vmovaps [rsp+48],  xmm9
    vmovaps [rsp+64],  xmm10
    vmovaps [rsp+80],  xmm11
    vmovaps [rsp+96],  xmm12
    vmovaps [rsp+112], xmm13
    vmovaps [rsp+128], xmm14
    vmovaps [rsp+144], xmm15
    push rbp
    push rdi
    push rsi
    push r12
    push r13
    push r14
    push r15
    mov rax, [rcx]   // rax = coro.sp
    mov [rcx], rsp   // coro.sp = rsp
    mov rsp, rax     // swap to coro stack
    mov rax, rdx     // rax = return value on coro stack
    pop r15
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rdi
    pop rbp
    vmovaps xmm6,  [rsp]
    vmovaps xmm7,  [rsp+16]
    vmovaps xmm8,  [rsp+32]
    vmovaps xmm9,  [rsp+48]
    vmovaps xmm10, [rsp+64]
    vmovaps xmm11, [rsp+80]
    vmovaps xmm12, [rsp+96]
    vmovaps xmm13, [rsp+112]
    vmovaps xmm14, [rsp+128]
    vmovaps xmm15, [rsp+144]
    add rsp, 160
    pop rbx
    mov rcx, gs:0x30
    pop rdx
    mov [rcx+0x10], rdx
    pop rdx
    mov [rcx+0x08], rdx
    ret

.global fhk_swap_exit
// coro[rcx] -> ret[rax]
fhk_swap_exit:
    mov rax, gs:0x30
    mov rdx, [rax+0x08]
    push rdx
    mov rdx, [rax+0x10]
    push rdx
    push rbx
    sub rsp, 160
    vmovaps [rsp],     xmm6
    vmovaps [rsp+16],  xmm7
    vmovaps [rsp+32],  xmm8
    vmovaps [rsp+48],  xmm9
    vmovaps [rsp+64],  xmm10
    vmovaps [rsp+80],  xmm11
    vmovaps [rsp+96],  xmm12
    vmovaps [rsp+112], xmm13
    vmovaps [rsp+128], xmm14
    vmovaps [rsp+144], xmm15
    push rbp
    push rdi
    push rsi
    push r12
    push r13
    push r14
    push r15
    mov rax, [rcx]   // rax = coro.sp
    mov [rcx], rsp   // coro.sp = rsp
    mov r15, [rax]   // r15 = vmctx
    mov rcx, gs:0x30 // fhk_vmexit restores registers, but we have to restore TIB
    mov rdx, [rax+224]
    mov [rcx+0x10], rdx
    mov rdx, [rax+232]
    mov [rcx+0x08], rdx
    jmp fhk_vmexit

.global fhk_swap_init
// swap[rcx]
fhk_swap_init:
    mov rdx, [rcx+0x08]   // rdx = stack high address
    mov [rdx-0x10], rdx   // save stack top
    mov rax, [rcx+0x20]   // rax = stack low address
    mov [rdx-0x18], rax   // save stack bottom
    lea rax, [rip+1f]     // rax = label 1f
    mov [rdx-0x8], rax    // return address = label 1f
    mov r9, rcx           // r9 = swap
    mov rcx, [rcx]        // rcx = coro
    sub rdx, 248          // 64 (gpr) + 160 (xmm) + 16 (tib) + 8 (return addr) = 248
    mov [rcx], rdx        // coro.sp = stack
    jmp fhk_swap
1:
    mov rcx, [r9+0x18]    // rcx = swap.ctx
    call [r9+0x10]        // call swap.func (this must not return!)
    ud2

.global fhk_swap_instance
// coro[rcx] -> vmctx[rax]
fhk_swap_instance:
    mov rax, [rcx]
    mov rax, [rax]
    ret
");

#[repr(C)]
pub struct SwapInit {
    pub coro: usize,
    pub stack: usize,
    pub func: unsafe extern "C" fn(*mut ()) -> !,
    pub ctx: *mut (),
    #[cfg(windows)]
    pub bottom: usize
}

unsafe extern "C" {
    // `stack` is a pointer to the address of the stack pointer.
    // this function stores regs on the current stacks, swaps stacks, and returns `ret` on the
    // swapped stack.
    pub fn fhk_swap(coro: usize, ret: i64) -> i64;
    // suspends this stack and jumps to fhk_vmexit.
    // THIS MUST NOT BE CALLED ON THE SAME STACK THAT CALLED fhk_vmcall.
    pub fn fhk_swap_exit(coro: usize) -> i64;
    // initialize a coroutine.
    pub fn fhk_swap_init(SwapInit: &SwapInit);
    // get instance pointer from coroutine.
    // this is safe to call **only** when the main coroutine has been swapped out via fhk_swap().
    // this is an asm function to hide the int->ptr cast.
    #[allow(improper_ctypes)]
    pub fn fhk_swap_instance(coro: usize) -> *mut Instance;
}

pub fn fhk_swap_bytes() -> &'static [u8] {
    // ideally you would write this as a constant:
    //   pub const FHK_SWAP_BYTES: &'static [u8] = unsafe {
    //       core::slice::from_raw_parts(
    //           fhk_swap as *const u8,
    //           (fhk_swap_exit as *const u8).offset_from(fhk_swap as *const u8) as usize
    //       )
    //   };
    // but rust says: "`ptr_offset_from` called on pointers into different allocations".
    // so i guess we're not writing it as a constant then.
    unsafe {
        core::slice::from_raw_parts(
            fhk_swap as *const u8,
            fhk_swap_exit as usize - fhk_swap as usize
        )
    }
}

/* ---- Instance creation --------------------------------------------------- */

// header for duplicated dynamic slots
//   +-----------+--------------+
//   | DupHeader | ... data ... |
//   +-----------+--------------+
// order of fields doesn't matter, but size must be 8.
#[repr(C)]
struct DupHeader {
    size: Offset, // alloc size, not including header
    next: Offset, // slot of next dup data
}

pub unsafe fn newinstance<UnsafeAlloc>(
    image: &Image,
    template: *const Instance,
    reset: u64,
    mut alloc: UnsafeAlloc
) -> *mut Instance
    where UnsafeAlloc: FnMut(usize, usize) -> *mut u8
{
    let inst = alloc(image.size as _, align_of::<Instance>()) as *mut Instance;
    if !template.is_null() {
        unsafe {
            core::ptr::copy_nonoverlapping(
                template as *const u8,
                inst as *mut u8,
                image.size as _
            );
        }
    }
    unsafe { (*inst).dup = 0; }
    // reset new instance
    // special case 0 and -1 to avoid shift by 64.
    match reset {
        0 => {},
        u64::MAX => unsafe { core::ptr::write_bytes(inst as *mut u8, 0, image.size as _) },
        mut mask => {
            let mut idx = 0;
            while mask != 0 {
                let num0 = mask.trailing_zeros() as usize;
                mask >>= num0;
                let num1 = mask.trailing_ones() as usize;
                mask >>= num1;
                unsafe {
                    let start = *image.breakpoints.raw.get_unchecked(idx+num0) as usize;
                    let end = *image.breakpoints.raw.get_unchecked(idx+num0+num1) as usize;
                    idx += num0+num1;
                    core::ptr::write_bytes((inst as *mut u8).add(start), 0, end-start);
                }
            }
        }
    }
    // copy dup list
    if !template.is_null() {
        let mut dup = unsafe { (*template).dup };
        while dup != 0 {
            let newptr = unsafe { (inst as *mut u8).add(dup as usize) } as *mut *mut DupHeader;
            let new = unsafe { *newptr };
            if new.is_null() {
                dup = unsafe {
                    (*(*((template as *const u8).add(dup as usize) as *const *const DupHeader))
                    .sub(1)).next
                };
            } else {
                unsafe {
                    let DupHeader { size, next } = *new.sub(1);
                    debug_assert!(size_of::<DupHeader>() == 8);
                    let copy = alloc((size+8) as _, 8) as *mut DupHeader;
                    *copy = DupHeader {
                        size,
                        next: core::ptr::replace(&raw mut (*inst).dup, dup)
                    };
                    *newptr = copy.add(1);
                    core::ptr::copy_nonoverlapping(
                        new as *const u8,
                        copy.add(1) as *mut u8,
                        size as _
                    );
                    dup = next;
                }
            }
        }
    }
    inst
}

/* ---- Array functions ----------------------------------------------------- */

// the point of this enum is to elide bound checks for ArrayType
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Nest { Scalar, Tensor, _2, _3, _4, X5 }

impl Nest {

    unsafe fn outer_unchecked(self) -> Nest {
        unsafe { core::mem::transmute((self as u8) + 1) }
    }

    fn outer(self) -> Nest {
        if self == Nest::X5 { unreachable!() }
        unsafe { self.outer_unchecked() }
    }

    unsafe fn inner_unchecked(self) -> Nest {
        unsafe { core::mem::transmute((self as u8) - 1) }
    }

    // fn inner(self) -> Nest {
    //     if self == Nest::Scalar { unreachable!() }
    //     unsafe { self.inner_unchecked() }
    // }

    fn inner_or_scalar(self) -> Nest {
        match self {
            Nest::Scalar => Nest::Scalar,
            _ => unsafe { self.inner_unchecked() }
        }
    }

}

// TODO: use this in lower
// NOTE: layout here is important. if you change it, update [un]pack, too.
#[derive(Clone, Copy)]
#[repr(C, align(8))]
pub struct ArrayType {
    pri: Primitive,
    nest: Nest,
    deco: [u8; 6] // let me guess, you *need* more indirection?
}

impl ArrayType {

    fn new_scalar(pri: Primitive) -> Self {
        Self {
            pri,
            nest: Nest::Scalar,
            deco: [1, 0, 0, 0, 0, 0]
        }
    }

    fn new_array(mut element: ArrayType, dim: u8) -> Self {
        let nest = element.nest.outer();
        element.deco[nest as usize] = element.deco[element.nest as usize] + dim;
        element.nest = nest;
        element
    }

    pub fn from_obj(objs: &Objects, idx: ObjRef) -> Self {
        match objs.get(idx) {
            ObjectRef::TPRI(&TPRI { ty, .. }) => Self::new_scalar(Primitive::from_u8(ty)),
            ObjectRef::TTEN(&TTEN { elem, dim, .. }) => Self::new_array(
                Self::from_obj(objs, elem),
                dim
            ),
            _ => unreachable!()
        }
    }

    // this must be fast
    #[cfg(target_endian="little")]
    pub unsafe fn unpack_unchecked(ptr: &mut *const u8) -> Self {
        let mut this: ArrayType = unsafe {
            core::mem::transmute((*ptr).cast::<u16>().read_unaligned() as u64)
        };
        this.deco[0] = 1;
        unsafe { *ptr = (*ptr).add(2); }
        for i in 1..this.nest as usize+1 {
            unsafe {
                this.deco[i] = **ptr;
                *ptr = (*ptr).add(1);
            }
        }
        this
    }

    pub fn pack_into(self, bump: &mut Bump) {
        bump.push([self.pri as u8, self.nest as u8]);
        bump.write(&self.deco[1..self.nest as usize+1]);
    }

    pub fn is_scalar(self) -> bool {
        self.nest == Nest::Scalar
    }

    pub fn is_tensor(self) -> bool {
        self.nest == Nest::Tensor
    }

    pub fn element(self) -> ArrayType {
        let mut element = self;
        element.nest = element.nest.inner_or_scalar();
        element
    }

    pub fn decomposition_size(self) -> usize {
        self.deco[self.nest as usize] as usize
    }

    pub fn primitive(self) -> Primitive {
        self.pri
    }

    // this must be fast. TODO check asm.
    fn element_decomposition_size(self) -> usize {
        self.element().decomposition_size()
    }

    // this must be fast. TODO check asm.
    pub fn dimension(self) -> usize {
        self.decomposition_size() - self.element_decomposition_size()
    }

    // this must be fast. TODO check asm.
    fn shape_info(self) -> (usize, usize) {
        (self.element_decomposition_size(), self.dimension())
    }

}

#[derive(Clone, Copy)]
pub struct ArrayRef<D> {
    // 0 levels of nesting (scalar):
    //   * scalar value
    // 1 level of nesting (tensor/ndarray):
    //   * pointer to scalar
    //   * shape[0], ..., shape[N-1]
    // 2 levels of nesting (ndarray of tensors):
    //   * pointer to pointer to scalar
    //   * pointer to inner shape[0]
    //   ...
    //   * pointer to inner shape[N-1]
    //   * shape[0], ..., shape[M-1]
    // etc.
    // each additional level of nesting adds a level of indirection to each field of the element.
    data: NonNull<()>,
    type_: ArrayType, // invariant: nest != Scalar
    _marker: PhantomData<D>
}

pub type Array<'a> = ArrayRef<&'a ()>;
pub type ArrayMut<'a> = ArrayRef<&'a mut ()>;

impl<'a> Array<'a> {

    pub unsafe fn new_unchecked(data: NonNull<()>, type_: ArrayType) -> Self {
        Self { data, type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub fn type_(self) -> ArrayType {
        self.type_
    }

    #[inline(always)]
    pub fn shape(self) -> &'a [Idx] {
        let (ofs, dim) = self.type_.shape_info();
        unsafe {
            core::slice::from_raw_parts(
                self.data.as_ptr().cast::<*const ()>().add(ofs).cast(),
                dim
            )
        }
    }

    #[inline(always)]
    pub fn data(self) -> &'a [*const ()] {
        let ds = self.type_.element_decomposition_size();
        unsafe { core::slice::from_raw_parts(self.data.as_ptr().cast(), ds) }
    }

}

impl<'a> ArrayMut<'a> {

    pub unsafe fn new_unchecked_mut(data: NonNull<()>, type_: ArrayType) -> Self {
        Self { data, type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub fn borrow<'b>(&'b self) -> Array<'b> {
        ArrayRef { data: self.data, type_: self.type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub fn borrow_mut<'b>(&'b mut self) -> ArrayMut<'b> {
        ArrayRef { data: self.data, type_: self.type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub unsafe fn shape_mut(self) -> &'a mut [Idx] {
        let (ofs, dim) = self.type_.shape_info();
        unsafe {
            core::slice::from_raw_parts_mut(
                self.data.as_ptr().cast::<*const ()>().add(ofs).cast(),
                dim
            )
        }
    }

    #[inline(always)]
    pub unsafe fn data_mut(self) -> &'a mut [*mut ()] {
        let ds = self.type_.element_decomposition_size();
        unsafe { core::slice::from_raw_parts_mut(self.data.as_ptr().cast(), ds) }
    }

}

#[repr(C)]
union Slot {
    ptr: *mut (),
    idx: [Idx; 2]
}

// on-stack storage suitable for holding an array representation (NOT the data itself)
pub struct ArrayBuf<const K: usize>([MaybeUninit<Slot>; K]);

impl<const K: usize> Default for ArrayBuf<K> {
    fn default() -> Self {
        Self([const { MaybeUninit::uninit() }; K])
    }
}

impl<'a> Array<'a> {

    pub fn get<'b: 'a, const K: usize>(self, _idx: usize, _buf: &'b mut ArrayBuf<K>) -> Array<'b> {
        // TODO: nest>=2
        todo!()
    }

}

impl<'a> ArrayMut<'a> {

    pub fn new_empty<const K: usize>(_type_: ArrayType, _buf: &'a mut ArrayBuf<K>) -> Self {
        // TODO: nest>=2
        todo!()
    }

}

/* ---- String functions ---------------------------------------------------- */

// TODO: string interning goes here

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct RtStr<'a> {
    ptr: *const u8,
    _marker: PhantomData<&'a ()>
}

impl<'a> RtStr<'a> {

    pub unsafe fn from_ptr(ptr: *const u8) -> Self {
        Self { ptr, _marker: PhantomData }
    }

    pub fn data(self) -> *const u8 {
        self.ptr
    }

    pub fn len(self) -> u32 {
        unsafe { (self.ptr.sub(4) as *const u32).read_unaligned() }
    }

}

/* ---- Chunk initialization ------------------------------------------------ */

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

/* ---- Alloc --------------------------------------------------------------- */

// TODO: host should compile this function

unsafe extern "C" fn rt_alloc(vmctx: &mut Instance, size: usize, align: usize) -> *mut u8 {
    vmctx.host.alloc(size, align)
}

/* ---- Abort --------------------------------------------------------------- */

unsafe extern "C" fn rt_abort(vmctx: &mut Instance) -> ! {
    vmctx.host.set_error(b"query aborted (no suitable model)");
    unsafe { fhk_vmexit(vmctx) }
}

/* ---- Runtime function library definitions -------------------------------- */

#[link(name="m")]
unsafe extern "C" {
    fn pow(x: f64, y: f64) -> f64;
    fn exp(x: f64) -> f64;
    fn log(x: f64) -> f64;
}

macro_rules! define_rtfuncs {
    ($(
        $name:ident
        $(($cc:expr))?
        $($arg:ident)*
        $(-> $ret:ident)?
        ;
    )*) => {
        #[derive(EnumSetType, Debug)]
        pub enum RtFunc {
            $($name),*
        }

        const RTFUNC_SIGNATURE: &[&Signature] = &[
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
define_rtfuncs! {
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

impl RtFunc {

    // FIXME replace with core::mem::variant_count when it stabilizes
    pub const COUNT: usize = <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _;

    pub fn from_u8(raw: u8) -> Self {
        assert!(raw < Self::COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn signature(self) -> &'static Signature {
        RTFUNC_SIGNATURE[self as usize]
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

/* ---- Runtime function call emission -------------------------------------- */

fn rtcall_init(ecx: &mut Ecx) {
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

fn rtcall_alloc(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    let &[size, align] = emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START))
        else { unreachable!() };
    let alloc = emit.fb.importnative(NativeFunc::ALLOC);
    let vmctx = emit.fb.vmctx();
    let call = emit.fb.ins().call(alloc, &[vmctx, size, align]);
    let ptr = emit.fb.ctx.func.dfg.inst_results(call)[0];
    emit.fb.ins().return_(&[ptr]);
}

fn rtcall_abort(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    let abort = emit.fb.importnative(NativeFunc::ABORT);
    let vmctx = emit.fb.vmctx();
    emit.fb.ins().call(abort, &[vmctx]);
    // the call_indirect doesn't return. this trap is here just to satisfy cranelift.
    emit.fb.ins().trap(TrapCode::User(0));
}

pub fn emitrtfunc(ecx: &mut Ecx, rtf: RtFunc) {
    use RtFunc::*;
    match rtf {
        INIT   => rtcall_init(ecx),
        ALLOC  => rtcall_alloc(ecx),
        ABORT  => rtcall_abort(ecx),
        SWAP   => unreachable!() // asm function
    }
}
