#pragma once

#include "conf.h"
#include "def.h"
#include "fhk.h"
#include "target.h"

/* this is the stack pointer. */
typedef void *fhk_co;

/* asm functions */
NOAPI void fhk_yield(fhk_solver *S, fhk_status s);
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
 * this macro will overwrite [rip] to point to the fail handler, and [rbx] to the return value.
 */
#define fhk_fail(S, status) do { \
	((void **)(S)->C)[1] = (void *) (status); \
	((void **)(S)->C)[6] = fhk_fail_trampoline; \
} while(0)

#else
#error "builtin: unsupported arch"
#endif
