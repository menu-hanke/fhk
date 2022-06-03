#include "co.h"
#include "def.h"
#include "solve.h"

#if FHK_ARCH == FHK_ARCH_x86_64
#if FHK_WINDOWS
#error "builtin: unsupported os"
#endif

static inline void *fhk_co_stack_new(fhk_arena *arena){
	// on function entry stack pointer must have the form 0x?????8.
	// fhk_continue() will pop everything all the way to stack top, so we must have
	// stack top at an address of that form.
	void **stack = (void *) (((intptr_t) fhk_alloc(arena, FHK_MAX_COSTACK-8, 16)) + (FHK_MAX_COSTACK-8));
	stack[-1] = fhk_yf_solver_main;
	// stack[-2] to stack[-7] are for registers.
	return &stack[-7];
}

#else
#error "builtin: unsupported arch"
#endif

fhk_solver *fhk_create_solver(fhk_graph *G, fhk_arena *arena){
	void *stack = fhk_co_stack_new(arena);
	struct fhk_solver *S = fhk_solver_new(G, arena);
	S->C = stack;
	return S;
}
