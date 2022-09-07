/* solver subroutines. */

#include "debug.h"
#include "def.h"
#include "sub.h"
#include "swap.h"
#include "trace.h"

#include <assert.h>
#include <stdalign.h>
#include <stdint.h>
#include <string.h>

/* static identity map. */
#define _(k) k##0, k##1, k##2, k##3, k##4, k##5, k##6, k##7, k##8, k##9, k##a, k##b, k##c, k##d, k##e, k##f
static const fhk_subset IDENT_INTERN[] = {
	_(0x00), _(0x01), _(0x02), _(0x03), _(0x04), _(0x05), _(0x06), _(0x07),
	_(0x08), _(0x09), _(0x0a), _(0x0b), _(0x0c), _(0x0d), _(0x0e), _(0x0f)
};
#undef _

#define IDENT_INTERN_SIZE  (sizeof(IDENT_INTERN)/sizeof(IDENT_INTERN[0]))
#define IDENT_INTERN_ZNUM  (IDENT_INTERN_SIZE-1)

/* ---- virtual memory mapping ---------------------------------------- */

#if FHK_MMAP

#include <sys/mman.h>

static fhk_mem *vm_map() {
	return mmap(NULL, VM_SIZE, PROT_READ|PROT_WRITE,
			MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);
}

static void vm_unmap(fhk_mem *mem) {
	munmap(mem, VM_SIZE);
}

#elif FHK_WINDOWS

#define WIN32_LEAN_AND_MEAN
#include <windows.h>

static fhk_mem *vm_map() {
	fhk_mem *mem = VirtualAlloc(NULL, VM_SIZE, MEM_RESERVE, PAGE_READWRITE);
	VirtualAlloc((LPVOID)mem, 4096, MEM_COMMIT, PAGE_READWRITE);
	VirtualAlloc((LPVOID)mem_stack(mem), MAX_STACK, MEM_COMMIT, PAGE_READWRITE);
	VirtualAlloc((LPVOID)mem_zeros(mem), MEM_ZEROS, MEM_COMMIT, PAGE_READONLY);
	mem->chead = (intptr_t) mem_W(mem);
	mem->ctail = (intptr_t) mem_zeros(mem);
	return mem;
}

static void vm_unmap(fhk_mem *mem) {
	VirtualFree((LPVOID)mem, 0, MEM_RELEASE);
}

#endif

fhk_mem *fhk_create_mem() {
	fhk_mem *mem = vm_map();
	if(UNLIKELY(!mem)) return NULL;
	mem->tail = (intptr_t) mem_tail(mem);
	mem->ident = 0;
	// mem->ident is znum, so mem->ident=0 means the first index must be initialized.
	*mem_id(mem) = 0;
	fhk_stack_init(mem_stack(mem) + MAX_STACK);
	return mem;
}

void fhk_destroy_mem(fhk_mem *mem) {
	vm_unmap(mem);
}

void fhk_reset_mem(fhk_mem *mem) {
	mem->tail = (intptr_t) mem_tail(mem);
}

/* ---- solver creation ---------------------------------------- */

fhk_solver *fhk_create_solver(fhk_mem *mem, fhk_graph *G) {
	intptr_t tail = mem->tail;
	tail &= ~(alignof(void *) - 1);
	tail -= G->nv * sizeof(void *);
	fhk_Sref S = (fhk_Sref) tail;
	tail -= sizeof(fhk_solver);
	tail -= G->nx * sizeof(void *);
	fhk_mem_commit_tail(mem, tail);
	memset((void *)tail, 0, mem->tail-tail);
	mem->tail = tail;
	srefS(S)->sp = fhk_stack_align(mem_stack(mem) + MAX_STACK);
	srefS(S)->G = G2ref(G);
	srefS(S)->mem = mem;
	srefS(S)->bucket = NULL;
	srefS(S)->ident = IDENT_INTERN_ZNUM;
	srefV(S, OBJ_GLOBAL) = mem_zeros(mem);
	srefX(S, ~OBJ_GLOBAL) = mem_zeros(mem);
	srefV(S, OBJ_IDENT) = (void *) IDENT_INTERN;
	srefX(S, ~OBJ_IDENT) = mem_zeros(mem);
	return srefS(S);
}

/* ---- memory allocation ---------------------------------------- */

void *fhk_mem_alloc(fhk_mem *mem, size_t size, size_t align) {
	intptr_t tail = mem->tail;
	tail -= size;
	tail &= ~(align-1);
	fhk_mem_commit_tail(mem, tail);
	mem->tail = tail;
	return (void *) tail;
}

/* allocate value-> buf. init if type is subset. */
void fhk_mem_newbufV(fhk_Sref S, xidx idx, xinst shape) {
	if(UNLIKELY(!shape)) {
		srefV(S, idx) = (void *) 1;
		return;
	}
	assert(!srefV(S, idx));
	fhk_Gref G = srefS(S)->G;
	fhk_mem *mem = srefS(S)->mem;
	intptr_t tail = mem->tail;
	if(UNLIKELY(grefmeta(G, ~idx).tag & TAG_MAP)) {
		tail -= 8*shape;
		tail &= ~7;
		fhk_mem_commit_tail(mem, tail);
		fhk_subset *ss = (fhk_subset *) tail;
		do { *ss++ = SUBSET_UNDEF; } while(--shape > 0);
	} else {
		size_t size = grefmeta(G, ~idx).size;
		tail -= size*shape;
		tail &= alignmask(size);
		fhk_mem_commit_tail(mem, tail);
	}
	mem->tail = tail;
	srefV(S, idx) = (void *) tail;
}

/* allocate and init <-M.F-> bitmap. */
void fhk_mem_newbitmapV(fhk_Sref S, xidx idx, xinst shape) {
	if(UNLIKELY(!shape)) {
		srefV(S, idx) = (void *) 1;
		return;
	}
	assert(!srefV(S, idx));
	size_t words = (shape + 63) & ~63;
	fhk_mem *mem = srefS(S)->mem;
	intptr_t tail = mem->tail;
	tail -= sizeof(fhk_bmword) * words;
	tail &= ~(alignof(fhk_bmword) - 1);
	fhk_bmword *f = (fhk_bmword *) tail;
	srefV(S, idx) = f;
	size_t i = 0;
	do { *f++ = 0; } while(++i < words);
	tail -= sizeof(fhk_bmword) * words;
	fhk_mem_commit_tail(mem, tail);
	mem->tail = tail;
	fhk_bmword *m = (fhk_bmword *) tail;
	if(LIKELY(shape & 63))
		*m++ = ones(shape & 63);
	while((intptr_t)m < (intptr_t)srefV(S, idx))
		*m++ = ~(fhk_bmword)0;
}

/* allocate and init h.sp-> buf. */
void fhk_mem_newbufX(fhk_Sref S, xidx idx, xinst shape) {
	if(UNLIKELY(!shape)) {
		srefX(S, ~idx) = (void *) 1;
		return;
	}
	assert(!srefX(S, ~idx));
	fhk_mem *mem = srefS(S)->mem;
	intptr_t tail = mem->tail;
	tail -= sizeof(fhk_sp) * shape;
	tail &= ~(alignof(fhk_sp) - 1);
	uint64_t *sp = (uint64_t *) tail;
	srefX(S, ~idx) = sp;
	tail--;
	mem->tail = tail;
	fhk_mem_commit_tail(mem, tail);
	*((uint8_t *) tail) = 0;
	fhk_Gref G = srefS(S)->G;
	uint8_t tag = grefmeta(G, ~idx).tag;
	void *obj = grefobj(G, idx);
	uint64_t init;
	if(tag & TAG_COMPUTED) {
		init = fu32(((fhk_var *) obj)->cost);
	} else {
		init = fu32(((fhk_model *) obj)->k);
		if(tag & TAG_PRESOLVED) {
			init |= SP_FLAGS64(SPC8) | (1ULL << 32);
			xinst i = 0;
			do {
				*sp++ = init | (i << 40);
			} while(++i < shape);
			return;
		}
	}
	xinst i = 0;
	do {
		*sp++ = init;
	} while(++i < shape);
}

/* allocate and init M-> bitmap. */
void fhk_mem_newbitmapX(fhk_Sref S, xidx idx, xinst shape) {
	if(UNLIKELY(!shape)) {
		srefX(S, ~idx) = (void *) 1;
		return;
	}
	assert(!srefX(S, ~idx));
	size_t words = (shape + 63) & ~63;
	fhk_mem *mem = srefS(S)->mem;
	intptr_t tail = mem->tail;
	tail -= sizeof(fhk_bmword) * words;
	tail &= ~(alignof(fhk_bmword) - 1);
	fhk_bmword *m = (fhk_bmword *) tail;
	srefX(S, ~idx) = m;
	mem->tail = tail;
	fhk_mem_commit_tail(mem, tail);
	for(;;) {
		if(!--words) {
			*m = ones(shape & 63);
			break;
		}
		*m++ = ~(fhk_bmword)0;
	}
}

/* grow shared interned ident map to znum. */
void fhk_mem_grow_ident(fhk_Sref S, int32_t znum) {
	fhk_mem *mem = srefS(S)->mem;
	int32_t ident = mem->ident;
	if(znum > ident) {
		fhk_subset *id = mem_id(mem) + ident;
		mem->ident = znum;
		do {
			*++id = ++ident;
		} while(ident < znum);
	}
	srefV(S, OBJ_IDENT) = mem_id(mem);
}

/* ---- setroot ---------------------------------------- */
// TODO: when hot start/branch with precomputed set is implemented,
// this should also be changed to use precomputed sets.
// (ie. something like fhk_setroot(precomputed set)).

static void setroot(fhk_solver *S, xidx idx, fhk_root flags, fhk_selection selection) {
	fhk_bucket *bucket = S->bucket;
	if(UNLIKELY(!bucket))
newbucket:
	{
		fhk_mem *mem = S->mem;
		intptr_t tail = mem->tail;
		tail -= sizeof(*bucket);
		tail &= ~(alignof(*bucket) - 1);
		fhk_mem_commit_tail(mem, tail);
		mem->tail = tail;
		((fhk_bucket *) tail)->next = S->bucket;
		bucket = (fhk_bucket *) tail;
		S->bucket = bucket;
		bucket->num = 0;
	} else if(UNLIKELY(bucket->num == BUCKET_SIZE)) {
		fhk_bucket **prev = &S->bucket;
		for(;;) {
			bucket = bucket->next;
			if(!bucket) goto newbucket;
			if(!bucket->num) {
				*prev = bucket->next;
				bucket->next = S->bucket;
				S->bucket = bucket;
				break;
			}
		}
	}
	fhk_root root = flags;
	if(!(grefmeta(S->G, ~idx).tag & TAG_GIVEN))
		root |= ROOT_COMPUTED;
	root |= root_newidx(idx);
	int64_t num = bucket->num++;
	root |= num;
	bucket->roots[num] = root;
	bucket->sel[num] = selection;
	if(root & ROOT_MAP) {
		trace(SETROOTM, fhk_debug_sym(S->G, idx), fhk_debug_sym(S->G, select_idx(selection)),
					select_inst(selection));
	} else {
		trace(SETROOTSS, fhk_debug_sym(S->G, idx), selection);
	}
}

void fhk_setrootK(fhk_solver *S, int idx, fhk_subset ss) {
	if(UNLIKELY(subset_isE(ss)))
		return;
	setroot(S, idx, ROOT_DEPRIO, ss);
}

void fhk_setrootM(fhk_solver *S, int idx, int map, int inst) {
	setroot(S, idx, ROOT_MAP|ROOT_DEPRIO, root_newselection(map, inst));
	if(map == OBJ_GLOBAL) return;
	xidx group = grefmeta(S->G, ~(xidx)idx).group;
	if(map == group) return;
	setroot(S, map, 0, inst);
}

/* ---- setvalue ---------------------------------------- */

static void vref_clear(fhk_solver *S, int idx, fhk_bmword *bm, xinst start, xinst end) {
	xinst off = start >> 6;
	bm += off;
	uint64_t m;
	if(off == end>>6) {
		uint64_t mask = ones(start & 63) | zeros(end & 63);
		m = ~(*bm | mask);
		*bm &= mask;
		goto tail;
	}
	m = ~(*bm | ones(start & 63));
	*bm &= ones(start & 63);
	for(;;) {
		if(UNLIKELY(m)) goto fail;
		bm++;
		m = *bm;
		if(++off == end>>6) {
			m = ~(m | zeros(end & 63));
			*bm &= zeros(end & 63);
			break;
		} else {
			m = ~m;
			*bm = 0;
		}
	}
tail:
	if(UNLIKELY(m)){
fail:
		fhk_fail(S, ecode(WRITE) | etagA(OBJ, idx) | etagB(INST, 64*off+bitmapW_ffs(m)));
	}
}

static void *vref_prep(fhk_solver *S, xidx idx, fhk_subset ss, void *p) {
	if(UNLIKELY(subset_isE(ss))) return NULL;
	void *vp = srefV(S2ref(S), idx);
	if(vp) return vp;
	xidx group = grefmeta(S->G, ~idx).group;
	fhk_subset *pspace = srefV(S2ref(S), group);
	if(UNLIKELY(!pspace || subset_isU(*pspace))) {
		fhk_fail(S, ecode(UNSET) | etagA(OBJ, group));
		return NULL;
	}
	fhk_subset space = *pspace;
	xinst shape = subsetIE_size(space);
	if(p && ss == space) {
		srefV(S2ref(S), idx) = p;
		if(LIKELY(!srefX(S2ref(S), ~idx)))
			srefX(S2ref(S), ~idx) = mem_zeros(S->mem);
		else
			memset(srefX(S2ref(S), ~idx), 0, bitmap_size(shape));
		trace(SETVALR, fhk_debug_sym(S->G, idx), p, fhk_debug_value(S2ref(S), idx, 0));
		return NULL;
	}
	// invariant: V exists => X (aka bitmap) exists  (for given variables only)
	if(!srefX(S2ref(S), ~idx))
		fhk_mem_newbitmapX(S2ref(S), idx, shape);
	fhk_mem_newbufV(S2ref(S), idx, shape);
	return srefV(S2ref(S), idx);
}

static void vref_copyvalue(fhk_solver *S, xidx idx, fhk_subset ss, void *p, void *px) {
	if(UNLIKELY(grefmeta(S->G, ~idx).tag & TAG_GROUP)) {
		int32_t znum = *(fhk_subset *) p;
		if(UNLIKELY(znum > S->ident))
			fhk_mem_grow_ident(S2ref(S), znum);
	}
	void *vp = vref_prep(S, idx, ss, px);
	if(UNLIKELY(!vp)) return;
	size_t size = grefmeta(S->G, ~idx).size;
	fhk_bmword *bm = srefX(S2ref(S), ~idx);
	if(LIKELY(subset_isI(ss))) {
		xinst start = subsetI_first(ss);
		xinst num = subsetIE_size(ss);
		vref_clear(S, idx, bm, start, start+num);
		memcpy(vp+start*size, p, size*num);
		trace(SETVALI, fhk_debug_sym(S->G, idx), start, num-1, fhk_debug_value(S2ref(S), idx, start));
	} else {
		fhk_pkref pk = subsetC_pk(ss);
		for(;;) {
			xinst start = pkref_first(pk);
			xinst num = pkref_size(pk);
			xinst skip = size*num;
			vref_clear(S, idx, bm, start, start+num);
			memcpy(vp + size*start, p, skip);
			trace(SETVALI, fhk_debug_sym(S->G, idx), start, num-1, fhk_debug_value(S2ref(S), idx, start));
			if(!pkref_more(pk)) return;
			p += skip;
			pk = pkref_next(pk);
		}
	}
}

void fhk_setvalue(fhk_solver *S, int idx, fhk_subset ss, void *p) {
	vref_copyvalue(S, idx, ss, p, p);
}

void fhk_setvalueC(fhk_solver *S, int idx, fhk_subset ss, void *p) {
	vref_copyvalue(S, idx, ss, p, NULL);
}

/* solve.c */
NOAPI void fhk_solver_kmapg_rescan();

void *fhk_setvalueD(fhk_solver *S, int idx, fhk_subset ss) {
	void *vp = vref_prep(S, idx, ss, NULL);
	if(UNLIKELY(!vp)) return NULL;
	size_t size = grefmeta(S->G, ~(xidx)idx).size;
	if(UNLIKELY(grefmeta(S->G, ~(xidx)idx).tag & TAG_GROUP))
		fhk_callback(S, fhk_solver_kmapg_rescan);
	fhk_bmword *bm = srefX(S2ref(S), ~(xidx)idx);
	if(LIKELY(subset_isI(ss))) {
		xinst start = subsetI_first(ss);
		xinst num = subsetIE_size(ss);
		vref_clear(S, idx, bm, start, start+num);
		trace(SETVALD, fhk_debug_sym(S->G, idx), start, num-1);
		return vp + start*size;
	} else {
		fhk_pkref pk = subsetC_pk(ss);
		vp += size*pkref_first(pk);
		for(;;) {
			xinst start = pkref_first(pk);
			xinst num = pkref_size(pk);
			vref_clear(S, idx, bm, start, start+num);
			trace(SETVALD, fhk_debug_sym(S->G, idx), start, num-1);
			if(!pkref_more(pk)) return vp;
			pk = pkref_next(pk);
		}
	}
}

/* ---- getvalue ---------------------------------------- */

void fhk_getvalue(fhk_solver *S, int idx, fhk_subset ss, void *p) {
	size_t size = grefmeta(S->G, ~(xidx)idx).size;
	void *vp = srefV(S2ref(S), (xidx)idx);
	assert(vp);
	if(LIKELY(subset_isIE(ss))) {
		// this is a zero-byte copy for the empty set.
		xinst inst = subsetI_first(ss);
		xinst num = subsetIE_size(ss);
		memcpy(p, vp+inst*size, num*size);
		return;
	}
	fhk_pkref pk = subsetC_pk(ss);
	for(;;) {
		xinst inst = pkref_first(pk);
		xinst num = pkref_size(pk);
		memcpy(p, vp+size*inst, size*num);
		if(!pkref_more(pk)) return;
		p += size*num;
		pk = pkref_next(pk);
	}
}

void *fhk_getvalueD(fhk_solver *S, int idx, fhk_subset ss) {
	size_t size = grefmeta(S->G, ~(xidx)idx).size;
	void *vp = srefV(S2ref(S), (xidx)idx);
	assert(vp);
	if(LIKELY(subset_isIE(ss))) {
		// this will return nonsense for the empty set.
		// which is fine: the caller is not allowed to read it anyway.
		return vp + subsetI_first(ss)*size;
	}
	fhk_pkref pks = subsetC_pk(ss);
	fhk_pkref pk = pks;
	xinst num = 0;
	for(;;) {
		num += pkref_size(pk);
		if(!pkref_more(pk)) break;
		pk = pkref_next(pk);
	}
	fhk_mem *mem = S->mem;
	intptr_t tail = mem->tail;
	tail &= alignmask(size);
	tail -= num*size;
	fhk_mem_commit_tail(mem, tail);
	mem->tail = tail;
	void *ret = (void *) tail;
	pk = pks;
	for(;;) {
		xinst inst = pkref_first(pk);
		xinst n = pkref_size(pk);
		memcpy((void*)tail, vp+inst*size, n*size);
		tail += n*size;
		if(!pkref_more(pk)) break;
		pk = pkref_next(pk);
	}
	return ret;
}

void fhk_sethook(fhk_solver *S, int jidx) {
	fhk_callhook(S, jidx);
}

/* ---- subset routines ---------------------------------------- */

typedef struct pkbuf {
	int32_t start; // start of this interval
	int32_t used;  // num of used intervals
	int32_t cap;   // max of allocated intervals
	// pk intervals 5 bytes ea ->
	// (no trailing zeros)
	int8_t pk[];
} pkbuf;

typedef union ssbuf {
	struct {
		fhk_mref32 pk;
		int32_t end;
	};
	fhk_subset ss;
} ssbuf;

static void invert_put(intptr_t *tail, ssbuf *b, int32_t inst) {
	// can merge?
	if(LIKELY(b->end == inst-1)) {
		b->end = inst;
		return;
	}
	// empty set?
	if(b->end < 0) {
		// alloc 8 intervals
		*tail -= sizeof(pkbuf) + 8*5;
		// TODO: commit
		pkbuf *pk = (pkbuf *) *tail;
		pk->cap = 8;
		pk->used = 0;
		pk->start = inst;
		b->pk = pmref(b, pk);
		b->end = inst;
		return;
	}
	// add interval.
	pkbuf *pk = mrefp(b, b->pk);
	if(UNLIKELY(pk->used == pk->cap)) {
		pk->cap <<= 1;
		*tail -= sizeof(pkbuf) + pk->cap*5;
		// TODO: commit
		memcpy((void *)tail, pk, sizeof(pkbuf)+pk->used*5);
		pk = (pkbuf *) tail;
		b->pk = pmref(b, pk);
	}
	pkref_write(pk->pk+pk->used*5, pk->start, b->end-pk->start);
	pk->used++;
	pk->start = inst;
	b->end = inst;
}

static void invert_putall(intptr_t *tail, ssbuf *bb, int32_t inst, xinst znum) {
	do {
		invert_put(tail, bb++, inst);
	} while(--znum >= 0);
}

/*
 * compute inverse map of `from` to `to`.
 * complex maps are stored on mem.
 */
void fhk_invert(fhk_mem *mem, fhk_subset *from, int fromshape, fhk_subset *to, int toshape) {
	if(UNLIKELY(toshape <= 0)) return;
	ssbuf *b = (ssbuf *) to;
	for(int i=0; i<toshape; i++) b[i].end = -2;
	intptr_t tail = mem->tail;
	tail &= ~(alignof(pkbuf) - 1);
	// step 1: construct inverses.
	for(int i=0; i<fromshape; i++, from++) {
		fhk_subset ss = *from;
		if(LIKELY(subset_isI(ss))) {
			invert_putall(&tail, b+subsetI_first(ss), i, subsetIE_znum(ss));
		} else {
			fhk_pkref pk = subsetC_pk(ss);
			for(;;) {
				invert_putall(&tail, b+pkref_first(pk), i, pkref_znum(pk));
				if(!pkref_more(pk)) break;
				pk = pkref_next(pk);
			}
		}
	}
	intptr_t tail0 = tail;
	// step 2: finalize sets.
	for(int i=0; i<toshape; i++) {
		if(b[i].end == -2) {
			b[i].ss = SUBSET_EMPTY;
		} else {
			pkbuf *pk = mrefp(b+i, b[i].pk);
			if(!pk->used) {
				// b[i].end is already correct.
				// this converts it to an interval subset in-place.
				b[i].pk = pk->start;
			} else {
				// pk->used+1 intervals +3 trailing zero bytes.
				// TODO: commit
				tail -= 5*pk->used + 8;
				fhk_pkref r = (fhk_pkref) tail;
				memcpy(r, pk->pk, pk->used*5);
				pkref_write(r + pk->used*5, pk->start, b[i].end-pk->start);
				b[i].ss = subsetC_new(r);
				r += 5*pk->used + 5;
				*r++ = 0;
				*r++ = 0;
				*r = 0;
			}
		}
	}
	// step 3: move all complex subsets
	if(tail != tail0) {
		ptrdiff_t size = tail0 - tail;
		memcpy((void *)mem->tail - size, (void *)tail, size);
		ptrdiff_t off = mem->tail - tail0;
		mem->tail = size;
		// ~(~c+x) = -(-c-1+x)-1 = c+1+x-1 = c-x
		for(int i=0; i<toshape; i++) {
			if(subset_isC(b[i].ss)) {
				b[i].ss -= off;
			}
		}
	}
}
