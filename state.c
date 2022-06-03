#include "def.h"
#include "solve.h"

#include <stdalign.h>
#include <stdint.h>
#include <string.h>

struct fhk_solver *fhk_solver_new(fhk_graph *G, fhk_arena *arena){
	struct fhk_solver *S = (void *) (G->nm + (void **) fhk_alloc(
			arena,
			sizeof(struct fhk_solver) + (G->nm+G->nx)*sizeof(void *),
			alignof(void *)
	));

	S->mapstate = G->ni + (fhkX_anymap *) fhk_alloc(
			arena,
			(G->ni+G->nk)*sizeof(fhkX_anymap),
			alignof(fhkX_anymap)
	);

	S->value.m = ALIGN(G->nm, sizeof(void *)) + fhk_alloc(
			arena,
			(ALIGN(G->nm, sizeof(void *)) + G->nv)*sizeof(void *),
			alignof(void *)
	);

	S->G = G;
	S->arena = arena;
	S->root = NULL;

	memset(&S->scratch, 0, sizeof(S->scratch));
	S->scratch.mark = SCRATCH_NOMARK;

	memset(S->stateM - G->nm, 0, G->nm * sizeof(void *));
	memset(S->stateV, 0, G->nx * sizeof(void *));
	memset(S->value.m - G->nm, 0, G->nm + G->nv*sizeof(void *));

	for(int i=-G->ni; i<G->nk; i++)
		S->mapstate[i] = ANYMAP_UNDEF;

	return S;
}

fhk_subset *fhk_solver_newmapI(struct fhk_solver *S, xinst size){
	fhk_subset *ss = fhk_alloc(S->arena, size*sizeof(*ss), alignof(*ss));
	for(xinst i=0;i<size;i++)
		ss[i] = SUBSET_UNDEF;
	return ss;
}

fhkX_sp *fhk_solver_newsp(struct fhk_solver *S, xinst size, fhkX_sp init){
	fhkX_sp *sp = fhk_alloc(S->arena, size*sizeof(*sp), alignof(*sp));
	for(xinst i=0;i<size;i++)
		sp[i] = init;
	return sp;
}

void *fhk_solver_newvalue(struct fhk_solver *S, xinst size, xinst num){
	return fhk_alloc(S->arena, size*num, GUESS_ALIGN(size));
}

fhkX_bitmap fhk_solver_newbitmap(struct fhk_solver *S, xinst size){
	int words = (size+63)/64;
	fhkX_bitmap bm = fhk_alloc(S->arena, 8*words, alignof(*bm));
	uint64_t *r = bitmap_ref64(bm);
	for(int i=0;i<words;i++)
		r[i] = ~(uint64_t)0;
	// fill overflow with zeros
	if(LIKELY(size > 0))
		r[words-1] &= bitmapW_ones64(size%64);
	return bm;
}

fhkX_checkmap fhk_solver_newcheckmap(struct fhk_solver *S, xinst size){
	// 2 64-bit words per each 64 instance block
	int words = 2 * ((size+63)/64);
	fhkX_checkmap cm = fhk_alloc(S->arena, 8*words, alignof(*cm));
	uint64_t *r = bitmap_ref64(cm);
	for(int i=0;i<words;i++)
		r[i] = 0;
	// fill overflow with ones
	if(LIKELY(size > 0)){
		uint64_t mask = bitmapW_zeros64(size%64);
		r[words-1] |= mask; // E
		r[words-2] |= mask; // P
	}
	return cm;
}

struct fhkX_bucket *fhk_solver_newbucket(struct fhk_solver *S, int flags){
	struct fhkX_bucket *b = fhk_alloc(S->arena, bucket_size(flags), alignof(*b));
	b->used = 0;
	b->flags = flags;
	b->next = NULL;

	struct fhkX_bucket **prev = &S->root;
	while(*prev) prev = &(*prev)->next;
	*prev = b;

	return b;
}
