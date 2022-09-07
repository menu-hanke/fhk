#pragma once

#include "def.h"
#include "solve.h"
#include "target.h"

NOAPI void fhk_yield(int);
NOAPI void fhk_callback_return(void);
NOAPI ERRFUNC void fhk_yield_err(fhk_status);
NOAPI void fhk_enter_trampoline(void);
NOAPI void fhk_yieldhook(void);
NOAPI void fhk_fail_trampoline(void);

#if FHK_x64

#define ASMREG_S  "r12"

/*
 * fail from _outside_ of the solver.
 * this patches the return address to the fail trampoline.
 * stack layout here must match swap_x64.S
 *
 * +-----+-----+-----+-----+-----+-----+
 * | rbp | rbx | r15 | r14 | r13 | rip |
 * +-----+-----+-----+-----+-----+-----+
 * 0     1     2     3     4     5
 *
 * TODO: maybe a better way to do this would be to redirect the stack pointer to
 * some pre-allocated stack reserved for fail situations and let the trampoline
 * run on that stack. that way the fail status is preserved even when another solver
 * runs on the shared memory.
 */
COLD static inline void fhk_fail(fhk_solver *S, fhk_status err) {
	S->err = err;
	((void **) S->sp)[5] = fhk_fail_trampoline;
}

/*
 * schedule a callback before the solver continues.
 * must be run from outside the solver.
 *
 * before this call the stack looks like this:
 *    sp    sp+1  sp+2  sp+3  sp+4  sp+5
 *   +-----+-----+-----+-----+-----+-----+
 *   | rbp | rbx | r15 | r14 | r13 | rip |
 *   +-----+-----+-----+-----+-----+-----+
 *   ^
 *   16n alignment
 *
 * we schedule the callback by writing a new frame below the swapped one:
 *    sp-7  sp-6  sp-5  sp-4  sp-3  sp-2  sp-1  sp    sp+1  sp+2  sp+3  sp+4  sp+5
 *   +-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+
 *   | /// | /// | /// | /// | /// | cb  | ret | rbp | rbx | r15 | r14 | r13 | rip |
 *   +-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+
 *   ^                             ^     ^
 *   new sp (16n+8 alignment)      |     return handler (16n+8 alignment)
 *                                 callback address (16n alignment)
 */
static inline void fhk_callback(fhk_solver *S, void *cb) {
	void **sp = S->sp;
	sp[-1] = fhk_callback_return;
	sp[-2] = cb;
	S->sp = sp-7;
}

/*
 * schedule a yield before the solver continues.
 * must be run from outside the solver.
 * this is used for debug hooks.
 * see `fhk_callback` for the stack layout: the only difference is that we don't store
 * a return address, instead the driver calls fhk_continue() again.
 * this preserves stack alignment.
 */
static inline void fhk_callhook(fhk_solver *S, int j) {
	void **sp = S->sp;
	sp[-1] = fhk_yieldhook;
	sp[-5] = (void *) (intptr_t) j;
	S->sp = sp-6;
}

/*
 * stack pointer must be aligned to 16 when jumping to the asm entry point.
 * since we pop 6 registers, the original alignment is preserved,
 * so top should be aligned to 16.
 * (refer to the comment above in fhk_fail)
 */
static inline void *fhk_stack_align(void *p) {
	p = (void *) ((intptr_t)p & ~15);
	p -= 6*8;
	return p;
}

/* prepare stack for first call of fhk_continue. */
static inline void fhk_stack_init(void *p) {
	((void **) fhk_stack_align(p))[5] = fhk_enter_trampoline;
}

#else
#error "unsupported arch"
#endif
