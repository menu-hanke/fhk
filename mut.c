#include "def.h"
#include "mut.h"

#include <stdint.h>

const uint8_t fhkX_mtag_size[] = {
#define OBJSIZE(_, t) sizeof(t),
	MUT_OBJDEF(OBJSIZE)
#undef OBJSIZE
};

void fhk_mut_unflag(struct fhk_mut_graph *M){
	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		fhkX_mtag *tag = mrefp(M, ref);
		ref += mtag_size(*tag);
		*tag &= ~MTAG_AB;
	}
}
