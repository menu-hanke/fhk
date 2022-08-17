#pragma once

#include "build.h"
#include "def.h"
#include "solve.h"

DEBUGFUNC const char *fhk_debug_sym(fhk_Gref G, xidx idx);
DEBUGFUNC const char *fhk_mut_debug_sym(fhk_mut_graph *M, fhk_mref32 ref);
DEBUGFUNC const char *fhk_debug_value(fhk_Sref S, xidx idx, xinst inst);
