#pragma once

// declared here to avoid a circular dependency with solve.h

#define FHK_CO_builtin       1
#define FHK_CO_libco         2
#define CO(impl)             FHK_CO_##impl
#define CO_(impl)            CO(impl)
#define CO_impl              CO_(FHK_CO)

#if CO_impl == CO(builtin)
#include "co_builtin.h"
#elif CO_impl == CO(libco)
#include "co_libco.h"
#else
#error "no coroutine backend (FHK_CO incorrectly defined)"
#endif
