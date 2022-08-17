// NOTE: when entering/exiting the solver, S is always in r12
//       this must match the global register defined in solve.c

#include "asmdef.h"
#include "target.h"

#if FHK_WINDOWS
#error "TODO: windows"
#endif

.intel_syntax noprefix
.text

/*
 * solver -> outside world: exit with error (0) and never return.
 * noreturn void fhk_yield_err(fhk_status err)
 */
.globl fhk_yield_err
.hidden fhk_yield_err
.type fhk_yield_err, @function
fhk_yield_err:
	lea rax, [rip+fhk_fail_trampoline]
	mov [rsp], rax                     // swap return address
	mov [r12+OFFSETOF_sref_err], rdi   // srefs(S)->err = rdi
	xor edi, edi                       // return 0
	// -> continue to fhk_yield

/*
 * solver -> outside world.
 * void fhk_yield(int)
 */
.globl fhk_yield
.hidden fhk_yield
.type fhk_yield, @function
.align 16
fhk_yield:
	// save solver registers - we don't need to save r12 here.
	// we'll get the solver as a parameter for fhk_continue.
	push r13
	push r14
	push r15
	push rbx
	push rbp

	// swap to caller's stack.
	mov rcx, rsp
	mov rsp, [r12-SIZEOF_fhk_solver]
	mov [r12-SIZEOF_fhk_solver], rcx

	// restore caller's registers (including r12).
	pop rbp
	pop rbx
	pop r15
	pop r14
	pop r13
	pop r12

	// return idx
	mov eax, edi

	// return to caller.
	// TODO: is it faster to load return address earlier?
	pop rcx
	jmp rcx

/*
 * outside world -> solver.
 * int fhk_continue(fhk_solver *)
 */
.globl fhk_continue
.type fhk_continue, @function
.globl fhk_callback_return
.hidden fhk_callback_return
.align 16
fhk_continue:
	// save outside world registers on outside world stack.
	push r12
	push r13
	push r14
	push r15
	push rbx
	push rbp

	// swap to solver stack.
	mov rax, rsp
	mov rsp, [rdi]
	mov [rdi], rax

	// restore solver registers.
	lea r12, [rdi+SIZEOF_fhk_solver]

	// solver->solver return.
fhk_callback_return:
	pop rbp
	pop rbx
	pop r15
	pop r14
	pop r13

	// return to solver.
	// TODO: is it faster to load return address earlier?
	pop rax
	jmp rax

/*
 * C entry point.
 * this function should *return* when there's no more work to be done.
 * void fhk_solver_main()   (r12 is solver)
 */
.hidden fhk_solver_main

/*
 * asm entry point.
 * this is where fhk_continue jumps when the solver starts.
 * NOTE: stack pointer must be aligned to 16 when jumping here.
 * void fhk_solver_enter()   (r12 is solver)
 */
.globl fhk_enter_trampoline
.hidden fhk_enter_trampoline
fhk_enter_trampoline:
	// note: we don't need to change the stack pointer here. if we have reached this point,
	// then the solver was just initialized, or it returned all the way back up here.
	// either way, sp now points at the top of the shared stack.
	call fhk_solver_main
	mov edi, 1
	call fhk_yield
	jmp fhk_enter_trampoline

/*
 * solver -> outside world after the solver has failed in the outside world.
 * this is a jump target for fhk_continue, not a function.
 */
.globl fhk_fail_trampoline
.hidden fhk_fail_trampoline
fhk_fail_trampoline:
	xor edi, edi
	call fhk_yield
	jmp fhk_fail_trampoline
