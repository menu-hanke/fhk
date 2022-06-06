#include "co.h"
#include "conf.h"
#include "def.h"
#include "solve.h"

// cygwin doesn't define _WIN32, but libco depends on it to detect windows.
#if defined(__cygwin__) && !defined(_WIN32)
#define _WIN32 1
#endif

#include "libco/libco.c"

// note: this is NOT thread safe.
static union { struct fhk_solver *S; int r; } fhk_arg;

static void yf_main(){
	fhk_yf_solver_main(fhk_arg.S);
}

ERRFUNC static void yf_error(){
	struct fhk_solver *S = fhk_arg.S;
	for(;;)
		fhk_yield(S, 0);
}

static void *fhk_co_derive(void *sp, void *fp) {
	intptr_t start = ((intptr_t)sp - FHK_MAX_COSTACK + 15) & ~15;
	return co_derive((void *) start, (intptr_t)sp - start, fp);
}

void fhk_co_setup_stack(fhk_co *C, void *sp) {
	C->stack = sp;
	C->coro = fhk_co_derive(sp, yf_main);
	C->caller = co_active();
}

int fhk_continue(struct fhk_solver *S){
	fhk_arg.S = S;
	co_switch(S->C.coro);
	return fhk_arg.r;
}

void fhk_yield(struct fhk_solver *S, int r){
	fhk_arg.r = r;
	co_switch(S->C.caller);
}

void fhk_fail(struct fhk_solver *S, fhk_status error){
	S->C.coro = fhk_co_derive(S->C.stack, yf_error);
	S->error = error;
}
