#include "co.h"
#include "conf.h"
#include "def.h"
#include "mem.h"
#include "solve.h"
#include "vm.h"

#include <stdalign.h>
#include <stdint.h>
#include <string.h>

#define _(k) k##0, k##1, k##2, k##3, k##4, k##5, k##6, k##7, k##8, k##9, k##a, k##b, k##c, k##d, k##e, k##f
static fhk_subset IDENT_INTERN[] = {
	_(0x00), _(0x01), _(0x02), _(0x03), _(0x04), _(0x05), _(0x06), _(0x07),
	_(0x08), _(0x09), _(0x0a), _(0x0b), _(0x0c), _(0x0d), _(0x0e), _(0x0f)
};
#undef _
#define IDENT_INTERN_SIZE  (sizeof(IDENT_INTERN)/sizeof(IDENT_INTERN[0]))

struct fhk_mem *fhk_create_mem() {
	fhkX_vmmap map;
	if(!fhk_vm_map(&map, FHK_VMMAP_SIZE))
		return NULL;
	fhk_vm_commit(&map, map->base + sizeof(struct fhk_mem) + MAX_INST*sizeof(fhk_subset));
	struct fhk_mem *mem = (void *) map.base;
	mem->map = map;
	mem->ident = 0;
	mem->ptr = sizeof(*mem);
	return mem;
}

void *fhk_mem_alloc(fhk_mem *mem, size_t size, size_t align) {
	fhk_mem_align(mem, align);
	void *p = mrefp(mem, mem->ptr);
	fhk_mem_bump(mem, size);
	fhk_mem_commit(mem);
	return p;
}

void fhk_destroy_mem(struct fhk_mem *mem) {
	fhk_vm_unmap(&mem->map);
}

void fhk_reset_mem(fhk_mem *mem) {
	mem->ptr = sizeof(*mem);
}

/*
 * +--------+-------------------+--------+---------------+--------------------------+
 * | G->nm  |                   | G->nx  | FHK_WORK_SIZE | G->nm*u8 + G->nv*(void*) |
 * +--------+-------------------+--------+---------------+--------------------------+
 * | stateM | struct fhk_solver | stateV |      work     |            value         |
 * +--------+-------------------+--------+---------------+--------------------------+
 */
struct fhk_solver *fhk_create_solver(fhk_graph *G, fhk_mem *mem) {
	fhk_mem_bump(mem, FHK_MAX_COSTACK);
	fhk_mem_alignT(mem, void *);
	void *sp = mrefp(mem, mem->ptr);
	fhk_mem_bump(mem, G->nm * sizeof(void *));
	struct fhk_solver *S = mrefp(mem, mem->ptr);
	fhk_mem_bumpT(mem, *S);
	fhk_mem_bump(mem, G->nx * sizeof(void *));
	void *work = mrefp(mem, mem->ptr);
	fhk_mem_bump(mem, FHK_WORK_SIZE);
	fhk_mem_bump(mem, G->nm);
	fhk_mem_align(mem, alignof(void *));
	fhkX_valueref value = {.v = mrefp(mem, mem->ptr)};
	fhk_mem_bump(mem, G->nv * sizeof(void *));
	fhk_mem_commit(mem);
	fhk_co_setup_stack(&S->C, sp);
	S->G = G;
	S->value = value;
	S->mem = pmref(S, mem);
	S->bucket = 0;
	S->ident = IDENT_INTERN_SIZE;
	S->work = pmref(S, work);
	// TODO: since most of the map table is usually unused, you can try to fit something
	// else inside it (like the value table).
	for(int i=-G->ni; i<G->nk; i++)
		S->map[map_zext(i)] = ANYMAP_UNDEF;
	anymapI(S->map[map_zext(MAP_IDENT)]) = IDENT_INTERN;
	memset(&S->stateM[-G->nm], 0, G->nm * sizeof(void *));
	memset(S->stateV, 0, G->nx * sizeof(void *));
	memset(&valueM(value, -G->nm), 0, G->nm + G->nv*sizeof(void*));
	return S;
}

fhk_subset *fhk_mem_newmapI(struct fhk_solver *S, int size) {
	fhk_subset *ss = fhk_mem_alloc(mrefp(S, S->mem), size*sizeof(*ss), alignof(*ss));
	for(xinst i=0; i<size; i++)
		ss[i] = SUBSET_UNDEF;
	return ss;
}

fhkX_sp *fhk_mem_newsp(struct fhk_solver *S, int size, fhkX_sp init) {
	fhkX_sp *sp = fhk_mem_alloc(mrefp(S, S->mem), size*sizeof(*sp), alignof(*sp));
	for(xinst i=0;i<size;i++)
		sp[i] = init;
	return sp;
}

void *fhk_mem_newvalue(struct fhk_solver *S, int size, int num) {
	return fhk_mem_alloc(mrefp(S, S->mem), size*num, GUESS_ALIGN(size));
}

fhkX_bitmap fhk_mem_newbitmap(struct fhk_solver *S, int size) {
	// don't return NULL here, or we will come back and try to allocate again.
	if(UNLIKELY(size == 0)) return (fhkX_bitmap) 1;
	int words = (size+63)/64;
	fhkX_bitmap bm = fhk_mem_alloc(mrefp(S, S->mem), 8*words, alignof(*bm));
	uint64_t *r = bitmap_ref64(bm);
	for(int i=0;i<words;i++)
		r[i] = ~(uint64_t)0;
	// fill overflow with zeros
	r[words-1] &= bitmapW_ones64(size%64);
	return bm;
}

fhkX_checkmap fhk_mem_newcheckmap(struct fhk_solver *S, int size) {
	// 2 64-bit words per each 64 instance block
	if(UNLIKELY(size == 0)) return (fhkX_checkmap) 1;
	int words = 2 * ((size+63)/64);
	fhkX_checkmap cm = fhk_mem_alloc(mrefp(S, S->mem), 8*words, alignof(*cm));
	uint64_t *r = bitmap_ref64(cm);
	for(int i=0;i<words;i++)
		r[i] = 0;
	// fill overflow with ones
	uint64_t mask = bitmapW_zeros64(size%64);
	r[words-1] |= mask; // E
	r[words-2] |= mask; // P
	return cm;
}

void fhk_mem_checkident(struct fhk_solver *S, int size) {
	if(LIKELY(S->ident >= size))
		return;
	struct fhk_mem *mem = mrefp(S, S->mem);
	anymapI(S->map[map_zext(MAP_IDENT)]) = mem->ip;
	if(LIKELY(mem->ident >= size)) {
		S->ident = mem->ident;
		return;
	}
	for(xinst i=mem->ident; i<size; i++)
		mem->ip[i] = i;
	mem->ident = size;
}
