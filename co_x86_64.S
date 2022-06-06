#if FHK_WINDOWS
#error "co/x86_64: unsupported os"
#endif

.text

/* void fhk_yield(fhk_solver *, int) */
.global fhk_yield
fhk_yield:
	mov %esi, %eax

/* int fhk_continue(fhk_solver *) */
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
	// adjust stack back to where it was before fhk_continue popped our registers
	// and swap back to caller stack.
	// (6 registers + 1 return address) * 8 bytes = 56
	lea -56(%rsp), %rcx
	mov (%rdi), %rsp
	mov %rcx, (%rdi)

	// return 0 to caller
	xor %eax, %eax

	pop %rbp
	pop %rbx
	pop %r15
	pop %r14
	pop %r13
	pop %r12

	ret
