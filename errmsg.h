#pragma once

#define FHK_ERRMSG(_) \
	_(NYI,      "not yet implemented") \
	_(MEM,      "not enough memory") \
	_(CYCLE,    "chain contains cycle") \
	_(CHAIN,    "no chain with finite cost") \
	_(TYPE,     "invalid object type") \
	_(GROUP,    "invalid group") \
	_(INVERSE,  "nonsymmetric inverse") \
	_(WRITE,    "attempt to overwrite readonly value") \
	_(SIZE,     "exceeded maximum graph size") \
	_(UNSET,    "attempt to use unset value") \
	_(SKIP,     "object is skipped from graph")

#define FHK_TAGMSG(_) \
	_(OBJ,      "obj") \
	_(INST,     "instance") \
	_(EDGE,     "edge") \
	_(HANDLE,   "handle")
