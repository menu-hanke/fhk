//! Image and instance management.

use core::arch::global_asm;
use core::marker::PhantomPinned;
use core::mem::offset_of;
use core::u64;

use cfg_if::cfg_if;

use crate::finalize::Finalizers;
use crate::host::HostInst;
use crate::mem::{Breakpoints, Offset};
use crate::mmap::Mmap;

pub struct Image {
    pub mem: Mmap,
    pub breakpoints: Breakpoints,
    pub fin: Finalizers,
    pub size: Offset
}

// note: the repr align is redundant here, but (regardless of fields), the compiled code expects
// this to be aligned to 8.
#[repr(align(8))]
pub struct Instance {
    pub host: HostInst,
    pub dup: Offset, // allocations to duplicate when continuing from this state
    sp: *mut u8, // stack pointer just before entering query
    _pin: PhantomPinned
}

// header for duplicated dynamic slots
//   +-----------+--------------+
//   | DupHeader | ... data ... |
//   +-----------+--------------+
// order of fields doesn't matter, but size must be 8.
#[repr(C)]
pub struct DupHeader {
    pub size: Offset, // alloc size, not including header
    pub next: Offset, // slot of next dup data
}

/* ---- Instance creation --------------------------------------------------- */

impl Image {

    pub unsafe fn instantiate<UnsafeAlloc>(
        &self,
        template: *const Instance,
        reset: u64,
        mut alloc: UnsafeAlloc
    ) -> *mut Instance
        where UnsafeAlloc: FnMut(usize, usize) -> *mut u8
    {
        let inst = alloc(self.size as _, align_of::<Instance>()) as *mut Instance;
        if !template.is_null() {
            core::ptr::copy_nonoverlapping(template as *const u8, inst as *mut u8, self.size as _);
        }
        (*inst).dup = 0;
        // reset new instance
        // special case 0 and -1 to avoid shift by 64.
        match reset {
            0 => {},
            u64::MAX => core::ptr::write_bytes(inst as *mut u8, 0, self.size as _),
            mut mask => {
                let mut idx = 0;
                while mask != 0 {
                    let num0 = mask.trailing_zeros() as usize;
                    mask >>= num0;
                    let num1 = mask.trailing_ones() as usize;
                    mask >>= num1;
                    let start = *self.breakpoints.raw.get_unchecked(idx+num0) as usize;
                    let end = *self.breakpoints.raw.get_unchecked(idx+num0+num1) as usize;
                    idx += num0+num1;
                    core::ptr::write_bytes((inst as *mut u8).add(start), 0, end-start);
                }
            }
        }
        // copy dup list
        if !template.is_null() {
            let mut dup = (*template).dup;
            while dup != 0 {
                let newptr = (inst as *mut u8).add(dup as usize) as *mut *mut DupHeader;
                let new = *newptr;
                if new.is_null() {
                    dup = (*(*((template as *const u8).add(dup as usize) as *const *const DupHeader))
                        .sub(1)).next;
                } else {
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
        inst
    }

}

/* ---- Call and exit ------------------------------------------------------- */

#[cfg(all(target_arch="x86_64", unix))]
global_asm!("
.hidden fhk_vmcall
.hidden fhk_vmexit
");

#[cfg(target_arch="x86_64")]
global_asm!("
.p2align 4
.global fhk_vmcall
.global fhk_vmexit
// (vmctx[rdi], result[rsi], mcode[rdx]) -> status[rax]
fhk_vmcall:
    push r12                            // save all callee-save regs for fhk_vmexit
    push r13
    push r14
    push r15
    push rbx
    push rbp
    mov [rdi+{vmctx_rsp}], rsp          // save stack for fhk_vmexit
    push rcx                            // align stack for call
    mov r15, rdi                        // pinned reg = vmctx
    xor rdi, rdi                        // idx = 0 (TODO)
    call rdx                            // call mcode(idx, result)
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
    // vmctx_scratchpad = const offset_of!(host::State, scratchpad)
);

#[allow(improper_ctypes)]
extern "sysv64" {
    pub fn fhk_vmcall(vmctx: *mut Instance, result: *mut u8, mcode: *const u8) -> i32;
    #[cold]
    pub fn fhk_vmexit(vmctx: *mut Instance) -> !;
}

cfg_if! {
    if #[cfg(any(windows, all(target_os="macos", target_arch="aarch64")))] {
        pub unsafe extern "C" fn fhk_vmcall_native(
            vmctx: *mut Instance,
            result: *mut u8,
            mcode: *const u8
        ) -> i32 {
            fhk_vmcall(vmctx, result, mcode)
        }
    } else {
        pub use fhk_vmcall as fhk_vmcall_native;
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

extern "C" {
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

impl Image {

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

}
