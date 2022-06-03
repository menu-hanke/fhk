#include "conf.h"
#include "co_libco.h"
#include "def.h"
#include "solve.h"

// cygwin doesn't define _WIN32, but libco depends on it to detect windows.
#if defined(__cygwin__) && !defined(_WIN32)
#define _WIN32 1
#endif

#include "libco/libco.c"

// note: this is NOT thread safe.
static union { struct fhk_solver *S; fhk_status status; } fhk_arg;

static void yf_main(){
	fhk_yf_solver_main(fhk_arg.S);
}

ERRFUNC static void yf_error(){
	struct fhk_solver *S = fhk_arg.S;
	fhk_status status = *(fhk_status *) S->C.stack;
	for(;;)
		fhk_yield(S, status);
}

fhk_solver *fhk_create_solver(fhk_graph *G, fhk_arena *arena){
	// libco will not align the stack pointer for us.
	// this is kind of platform dependent, but aligning to 16 should work everywhere.
	void *stack = fhk_alloc(arena, FHK_MAX_COSTACK, 16);
	struct fhk_solver *S = fhk_solver_new(G, arena);
	S->C.stack = stack;
	S->C.coro = co_derive(stack, FHK_MAX_COSTACK, yf_main);
	S->C.caller = co_active();
	return S;
}

fhk_status fhk_continue(struct fhk_solver *S){
	fhk_arg.S = S;
	co_switch(S->C.coro);
	return fhk_arg.status;
}

void fhk_yield(struct fhk_solver *S, fhk_status status){
	fhk_arg.status = status;
	co_switch(S->C.caller);
}

void fhk_fail(struct fhk_solver *S, fhk_status status){
	S->C.coro = co_derive(S->C.stack+sizeof(status), FHK_MAX_COSTACK, yf_error);
	*(fhk_status *)S->C.stack = status;
}
