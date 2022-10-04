// NOTE: when entering/exiting the solver, S is always in r12
//       this must match the global register defined in solve.c

#include "asmdef.h"
#include "target.h"

#if FHK_WINDOWS
#define CARG1  rcx
#define CARG1d ecx
#else
#define CARG1  rdi
#define CARG1d edi
#endif

#if __ELF__
#define HIDDEN(sym)   .hidden sym
#define FUNCTION(sym) .type sym, @function
#elif FHK_WINDOWS
#define HIDDEN(sym)
#define FUNCTION(sym)
.section .drectve
.asciz "-export:fhk_continue"
#endif

.intel_syntax noprefix
.text

/*
 * solver -> outside world: exit with error (0) and never return.
 * noreturn void fhk_yield_err(fhk_status err)
 */
.globl fhk_yield_err
FUNCTION(fhk_yield_err)
HIDDEN(fhk_yield_err)
fhk_yield_err:
	lea rax, [rip+fhk_fail_trampoline]
	mov [rsp], rax                     // swap return address
	mov [r12+OFFSETOF_sref_err], CARG1 // srefs(S)->err = rdi
	xor CARG1d, CARG1d                 // return 0
	// -> continue to fhk_yield

/*
 * solver -> outside world.
 * void fhk_yield(int)
 */
.globl fhk_yield
FUNCTION(fhk_yield)
HIDDEN(fhk_yield)
.align 16
fhk_yield:
	// save solver registers - we don't need to save r12 here.
	// we'll get the solver as a parameter for fhk_continue.
	push r13
	push r14
	push r15
	push rbx
	push rbp
#if FHK_WINDOWS
	push rdi
	push rsi
#endif

1:
	// swap to caller's stack.
	mov rax, rsp
	mov rsp, [r12-SIZEOF_fhk_solver]
	mov [r12-SIZEOF_fhk_solver], rax

	// restore caller's registers (including r12).
#if FHK_WINDOWS
	pop rsi
	pop rdi
#endif
	pop rbp
	pop rbx
	pop r15
	pop r14
	pop r13
	pop r12

	// return idx
	mov eax, CARG1d

	// return to caller.
	// TODO: is it faster to load return address earlier?
	pop rcx
	jmp rcx

/*
 * outside world -> solver.
 * int fhk_continue(fhk_solver *)
 */
.globl fhk_continue
FUNCTION(fhk_continue)
.globl fhk_callback_return
HIDDEN(fhk_callback_return)
.align 16
fhk_continue:
	// save outside world registers on outside world stack.
	push r12
	push r13
	push r14
	push r15
	push rbx
	push rbp
#if FHK_WINDOWS
	push rdi
	push rsi
#endif

	// swap to solver stack.
	mov rax, rsp
	mov rsp, [CARG1]
	mov [CARG1], rax

	// restore solver registers.
	lea r12, [CARG1+SIZEOF_fhk_solver]

	// solver->solver return.
fhk_callback_return:
#if FHK_WINDOWS
	pop rsi
	pop rdi
#endif
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
 HIDDEN(fhk_solver_main)

/*
 * asm entry point.
 * this is where fhk_continue jumps when the solver starts.
 * NOTE: stack pointer must be aligned to 16 when jumping here.
 * void fhk_solver_enter()   (r12 is solver)
 */
.globl fhk_enter_trampoline
HIDDEN(fhk_enter_trampoline)
fhk_enter_trampoline:
	// note: we don't need to change the stack pointer here. if we have reached this point,
	// then the solver was just initialized, or it returned all the way back up here.
	// either way, sp now points at the top of the shared stack.
	call fhk_solver_main
	mov CARG1d, 1
	call fhk_yield
	jmp fhk_enter_trampoline

/*
 * solver -> outside world debug hook.
 * this is a jump target for fhk_continue, not a function.
 * rbx is the hook index.
 */
.globl fhk_yieldhook
HIDDEN(fhk_yieldhook)
fhk_yieldhook:
	mov CARG1d, ebx
	jmp 1b

/*
 * solver -> outside world after the solver has failed in the outside world.
 * this is a jump target for fhk_continue, not a function.
 */
.globl fhk_fail_trampoline
HIDDEN(fhk_fail_trampoline)
fhk_fail_trampoline:
	xor CARG1d, CARG1d
	call fhk_yield
	jmp fhk_fail_trampoline
