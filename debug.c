/*
 * debug routines.
 *
 * WARNING: this is meant for debugging fhk itself, not programs using fhk.
 * the functions here rotate shared global buffers (non-thread-safely)
 * and do no bounds checking.
 * do not use anything here outside debugging fhk itself.
 */

#include "build.h"
#include "debug.h"
#include "def.h"

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

#if FHK_DSYM

static char *rotatebuf() {
	static char buf[4][128];
	static int64_t idx = 0;
	idx = (idx + 1) & 3;
	return buf[idx];
}

const char *fhk_debug_sym(fhk_Gref G, xidx idx) {
	fhk_mref32 *tab = mrefp(G, grefG(G)->symtab);
	fhk_mref32 sym = tab[idx];
	if(sym) return mrefp(G, sym);
	char *buf = rotatebuf();
	sprintf(buf, "<anon.%d>", (int)idx);
	return buf;
}

const char *fhk_mut_debug_sym(fhk_mut_graph *M, fhk_mref32 ref) {
	static const char *objtag[] = {
#define OBJTAG(name, _) #name,
		MUT_OBJDEF(OBJTAG)
#undef OBJTAG
	};
	fhk_mtag tag = *(fhk_mtag *) mrefp(M, ref);
	if(mtype_isobj(tag & MTAG_TYPE)) {
		fhk_mref32 sym = ((fhk_mut_obj *) mrefp(M, ref))->sym;
		if(sym) return mrefp(M, sym);
	}
	char *buf = rotatebuf();
	sprintf(buf, "<%s.0x%x>", objtag[tag & MTAG_TYPE], ref);
	return buf;
}

const char *fhk_debug_value(fhk_Sref S, xidx idx, xinst inst) {
	static char buf[128];
	typedef union { int32_t i32; float f32; } v32;
	typedef union { int64_t i64; double f64; } v64;
	void *v = srefV(S, idx);
	void *x = srefX(S, ~idx);
	if(!v || !x) return "(none)";
	fhk_Gref G = srefS(S)->G;
	if(grefmeta(G, ~idx).tag & TAG_GIVEN) {
		if(((fhk_bmword *)x)[bitmap_idx(inst)] & (1ULL << bitmap_shift(inst)))
			return "(none)";
	} else {
		if((((fhk_sp *)x)[inst].u8[SP8_FLAGS] & (SPC8|SPV8)) != (SPC8|SPV8))
			return "(none)";
	}
	size_t size = grefmeta(G, ~idx).size;
	v += size*inst;
	switch(size) {
		case 4: sprintf(buf, "u32: 0x%x f32: %f", ((v32*)v)->i32, ((v32*)v)->f32); break;
		case 8: sprintf(buf, "u64: 0x%" PRIx64 " f64: %f", ((v64*)v)->i64, ((v64*)v)->f64); break;
		default:
			strcpy(buf, "hex: 0x");
			for(size_t i=0; i<size; i++)
				sprintf(buf+strlen("hex: 0x")+2*i, "%x", ((uint8_t *)v)[i]);
			buf[strlen("hex: 0x")+2*size] = 0;
	}
	return buf;
}

#endif
