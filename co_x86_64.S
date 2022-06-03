#if FHK_WINDOWS
#error "co/x86_64: unsupported os"
#endif

.text

/* void fhk_yield(fhk_solver *, fhk_status) */
.global fhk_yield
fhk_yield:
	mov %rsi, %rax

/* fhk_status fhk_continue(fhk_solver *) */
.global fhk_continue
fhk_continue:
	// save caller/solver registers
	push %r12
	push %r13
	push %r14
	push %r15
	push %rbx
	push %rbp

	// swap stacks.
	// any scratch register other than rax works here.
	mov %rsp, %rcx
	mov (%rdi), %rsp
	mov %rcx, (%rdi)

	// restore solver/caller registers
	pop %rbp
	pop %rbx
	pop %r15
	pop %r14
	pop %r13
	pop %r12

	// return to where solver/caller was called from
	ret

/* do not call this directly. only jump here via fhk_continue. */
.global fhk_fail_trampoline
fhk_fail_trampoline:
	mov %rbx, %rax

	// fhk_continue() helpfully popped our registers for us.
	// however we want to come back here if fhk_continue() is called again.
	// luckily no one will ever modify the stack any more, so we may swap back the old
	// stack pointer.
	// fhk_continue() popped 6 registers and a return address, so 7*8 = 56 bytes.
	lea -56(%rsp), %rcx
	mov (%rdi), %rsp
	mov %rcx, (%rdi)

	pop %rbp
	pop %rbx
	pop %r15
	pop %r14
	pop %r13
	pop %r12

	ret
