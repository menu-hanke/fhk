#include "target.h"

local ffi = require "ffi"

//-- note: we may not use this for resolving symbols here, use `fhk_clib` instead.
local C = ffi.C

ffi.cdef[[
#include "def.h"
#include "fhk.h"
#include "solve.h"
]]

#define stringify_(x) #x
#define stringify(x)  stringify_(x)

//---- build config ----------------------------------------
local config = {
#ifdef FHK_GITHASH
	version = "fhk commit " .. stringify(FHK_GITHASH),
#else
	version = "fhk (unknown commit)",
#endif
	coro = stringify(FHK_TARGET_CO),
#if FHK_DEBUG
	debug = true,
#else
	debug = false,
#endif
}

//---- error messages ----------------------------------------
#include "errmsg.h"

local errmsg = {
#define ERRMSG(e,m) [C.FHK_ERR_##e] = m,
FHK_ERRMSG(ERRMSG)
#undef ERRMSG
}

local errtag = {
#define ERRTAG(t,m) [C.FHK_ETAG_##t] = m,
FHK_TAGMSG(ERRTAG)
#undef ERRTAG
}

//--------------------------------------------------------------------------------

return {
	config = config,
	errmsg = errmsg,
	errtag = errtag
}
