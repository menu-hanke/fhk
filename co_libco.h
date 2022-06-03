#pragma once

#include "def.h"

#include "libco/libco.h"

typedef struct {
	cothread_t coro;
	cothread_t caller;
	void *stack;
} fhk_co;

NOAPI void fhk_yield(fhk_solver *S, fhk_status s);
NOAPI COLD void fhk_fail(fhk_solver *S, fhk_status s);
