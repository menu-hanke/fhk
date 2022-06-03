#pragma once

#define FHK_ERRMSG(_) \
	_(BOUND,    "index out of bounds") \
	_(INVAL,    "invalid value") \
	_(GIVEN,    "expected given variable") \
	_(NOVALUE,  "no value") \
	_(WRITE,    "attempt to overwrite readonly value") \
	_(MAPASSOC, "group associated with map is not unique") \
	_(UNSET,    "unset value") \
	_(NOLAYOUT, "layout not computed") \
	_(NYI,      "not yet implemented") \
	_(DEPTH,    "solver stack overflow") \
	_(CHAIN,    "no chain with finite cost") \
	_(MEM,      "failed to allocate memory")

#define FHK_TAGMSG(_) \
	_(NODE,     "node") \
	_(MAP,      "map") \
	_(INST,     "instance") \
	_(GROUP,    "group") \
	_(EDGE,     "edge") \
	_(HANDLE,   "handle")
