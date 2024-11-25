//! Image and instance management.

use core::arch::global_asm;
use core::cell::Cell;
use core::marker::PhantomPinned;
use core::mem::offset_of;
use core::pin::Pin;

use cfg_if::cfg_if;

use crate::host::HostInst;
use crate::lang::{self, LangMap};
use crate::mem::{Breakpoints, Offset};
use crate::mmap::Mmap;

pub struct Image {
    pub mem: Mmap,
    pub lang: LangMap<lang::ImageData>,
    pub breakpoints: Breakpoints,
    pub size: Offset
}

// note: the repr align is redundant here, but (regardless of fields), the compiled code expects
// this to be aligned to 8.
#[repr(align(8))]
pub struct Instance {
    pub host: HostInst,
    sp: Cell<*const u8>,
    _pin: PhantomPinned
}

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
    mov rsp, [rdi+{vmctx_rsp}]          // restore stack
    mov eax, 1                          // status = 1
    jmp 1b
",
    vmctx_rsp        = const offset_of!(Instance, sp),
    // vmctx_scratchpad = const offset_of!(host::State, scratchpad)
);

#[allow(improper_ctypes)]
extern "sysv64" {
    pub fn fhk_vmcall(vmctx: Pin<&Instance>, result: *mut u8, mcode: *const u8) -> i32;
    #[cold]
    pub fn fhk_vmexit(vmctx: Pin<&Instance>) -> !;
}

cfg_if! {
    if #[cfg(any(windows, all(target_os="macos", target_arch="aarch64")))] {
        pub unsafe extern "C" fn fhk_vmcall_native(vmctx: &Pin<Instance>, mcode: *const u8) -> i32 {
            fhk_vmcall(vmctx, mcode)
        }
        pub use fhk_vmcall_native;
    } else {
        pub use fhk_vmcall as fhk_vmcall_native;
    }
}
