#pragma once

#include "conf.h"
#include "def.h"
#include "target.h"

/* coroutine entry point.
 * declared here to avoid circular dependencies with solve.h */
NOAPI void fhk_yf_solver_main(fhk_solver *S);
NOAPI void fhk_yield(fhk_solver *S, int r);

#if FHK_CO == FHK_CO_builtin

/* this is the stack pointer. */
typedef void *fhk_co;

/* co_x86_64.S */
NOAPI void fhk_fail_trampoline();

#if FHK_ARCH == FHK_ARCH_x86_64
#if FHK_WINDOWS
#error "builtin: unsupported os"
#endif

/* this must be called from outside the solver coroutine.
 * the solver stack looks like this:
 *    [0]   [1]   [2]   [3]   [4]   [5]   [6]
 *    [rbp] [rbx] [r15] [r14] [r13] [r12] [rip]
 *    ^
 *    |
 *    fhk_co (stack pointer).
 * this macro will overwrite [rip] to point to the fail handler, so fhk_continue() will
 * jump to the fail trampoline instead of resuming the solver on next call.
 */
#define fhk_fail(S, s) do { \
	(S)->error = (s); \
	((void **)(S)->C)[6] = fhk_fail_trampoline; \
} while(0)

static inline void fhk_co_setup_stack(fhk_co *C, void *sp) {
	/* stack pointer is aligned to 16 just before the `call` instruction,
	 * so on function entry it must be 16n+8.
	 * so our return value is aligned to 16 again so that `fhk_continue` will align
	 * the stack to 16n+8 when it pops it. */
	intptr_t s = (((intptr_t) sp) & ~15) + 8;
	if(s >= (intptr_t)sp) s -= 16;
	((void **)s)[-1] = fhk_yf_solver_main;
	*C = (void *) (s - 7*8);
}

#else
#error "builtin: unsupported arch"
#endif

#elif FHK_CO == FHK_CO_libco

typedef struct {
	void *coro;
	void *caller;
	void *stack;
} fhk_co;

/* co_libco.c */
NOAPI void fhk_co_setup_stack(fhk_co *C, void *sp);
NOAPI COLD void fhk_fail(fhk_solver *S, fhk_status s);

#else
#error "no coroutine backend (FHK_CO incorrectly defined)"
#endif
