#pragma once

#include "def.h"

NOAPI const char *fhk_debug_value(struct fhk_solver *S, xidx idx, xinst inst);
NOAPI const char *fhk_debug_sym(struct fhk_graph *G, xidx idx);
NOAPI const char *fhk_mut_debug_sym(struct fhk_mut_graph *M, fhk_mhandle handle);
NOAPI fhkX_dsym fhk_debug_sym_add(fhkX_dsym_ref *ref, const char *sym);
