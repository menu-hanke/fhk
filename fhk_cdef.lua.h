local ffi = require "ffi"
local C = ffi.C

ffi.cdef[[
#include "api.h"
]]

//---- build config ----------------------------------------
local config = {
#ifdef FHK_GITHASH
	version = "fhk-" .. FHK_GITHASH,
#else
	version = "fhk (unknown commit)",
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

//---- build ----------------------------------------

local typeof = ffi.typeof
local otype = {
#define MUTOBJ(name, ctype) [C.MTYPE(name)] = {name=#name, ctype=typeof(#ctype), ctypeptr=typeof(#ctype.."*"), size=ffi.sizeof(#ctype)},
	MUT_OBJDEF(MUTOBJ)
#undef MUTOBJ
}

local predicate = {
#define PREDTYPE(operator, operand) operator = C.PRED(operator),
	FHK_PREDEF(PREDTYPE)
#undef PREDTYPE
}

local mtagmask = {
	V = C.MTYPE(var),
	M = C.MTYPE(model),
	X = C.MTYPE(predicate), /* P, R, D, C and T are already taken... */
	D = C.MTYPE(rcheck),
	C = C.MTYPE(check),
	P = C.MTYPE(edgeP),
	R = C.MTYPE(edgeR),
	T = MTAG_TYPE,
	m = MTAG_MAP,
	g = MTAG_GUARD,
	p = MTAG_PREGRD,
	d = MTAG_DERIVE,
	s = MTAG_SKIP,
	j = MTAG_IDX,
	r = MTAG_RETAIN,
	x = MTAG_MARKREC
}

local function jtabsize(mref)
	local nlc = mref.mp.nlc
	return nlc[LC_KMAPG] + nlc[LC_IMAPG] + nlc[LC_GIVEN] // given variables
		+ nlc[LC_KMAPD] + nlc[LC_IMAPD] + nlc[LC_DERIVE] // derives
		+ nlc[LC_NDMODEL]                                // models
end

//--------------------------------------------------------------------------------

return {
	config    = config,
	errmsg    = errmsg,
	errtag    = errtag,
	otype     = otype,
	predicate = predicate,
	mtagmask  = mtagmask,
	jtabsize  = jtabsize,
#if FHK_DSYM
	debug     = true,
#else
	debug     = false,
#endif
}
