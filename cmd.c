#include "fhk.h"
#include "co.h"
#include "debug.h"
#include "def.h"
#include "mem.h"
#include "solve.h"
#include "trace.h"

#include <assert.h>

/* solver control commands */

/* ---- input checks ---------------------------------------- */

static int input_assertV(struct fhk_solver *S, int idx) {
	if(UNLIKELY((uint32_t)(S->G->nv - idx - 1) >= S->G->nv)) {
		fhk_fail(S, ecode(INVAL) | etagA(NODE, idx));
		return 0;
	}
	return 1;
}

/* ---- setmap ---------------------------------------- */

static void setmapK(struct fhk_solver *S, xmap map, fhk_subset ss) {
	if(UNLIKELY(!anymap_isU(S->map[map]))) {
		fhk_fail(S, ecode(WRITE) | etagA(MAP, map));
		return;
	}
	if(map_zext(map) < S->G->ng) {
		assert(subset_isE(ss) || (subset_isI(ss) && subsetI_first(ss) == 0));
		fhk_mem_checkident(S, subsetIE_size(map));
	}
	anymapK(S->map[map]) = ss;
	trace(SETMAPK, map, ss);
}

void fhk_setmapK(struct fhk_solver *S, int map, fhk_subset ss) {
	if(UNLIKELY(map_zext(map) >= S->G->nk)) {
		fhk_fail(S, ecode(BOUND) | etagA(MAP, map));
		return;
	}
	setmapK(S, map, ss);
}

void fhk_setmapI(struct fhk_solver *S, int map, int inst, fhk_subset ss) {
	if(UNLIKELY((uint32_t)map < (uint32_t)-S->G->ni)) {
		fhk_fail(S, ecode(BOUND) | etagA(MAP, map));
		return;
	}
	fhkX_anymap am = S->map[map_zext(map)];
	if(UNLIKELY(anymap_isU(am))){
		xgroup group = S->G->mapg[map_zext(map)];
		if(UNLIKELY(anymap_isU(S->map[group]))) {
			fhk_fail(S, ecode(NOVALUE) | etagA(MAP, group));
			return;
		}
		anymapI(am) = fhk_mem_newmapI(S, subsetIE_size(anymapK(S->map[group])));
		S->map[map_zext(map)] = am;
	}
	if(UNLIKELY(!subset_isU(anymapII(am, inst)))) {
		fhk_fail(S, ecode(WRITE) | etagA(MAP, map) | etagB(INST, inst));
		return;
	}
	anymapII(am, inst) = ss;
	trace(SETMAPI, map, inst, ss);
}

/* ---- shape ---------------------------------------- */

void fhk_setshape(struct fhk_solver *S, int group, int shape) {
	fhk_setmapK(S, group, shape ? subsetI_newZ(shape-1, 0) : SUBSET_EMPTY);
}

void fhk_setshapeT(struct fhk_solver *S, uint32_t *shape) {
	int ng = S->G->ng;
	for(int i=0; i<ng; i++) {
		uint32_t s = shape[i];
		setmapK(S, i, s ? subsetI_newZ(s-1, 0) : SUBSET_EMPTY);
	}
}

/* ---- setroot ---------------------------------------- */

static struct fhkX_bucket *root_find_bucket(struct fhk_solver *S, int flags, fhk_mref hint) {
	while(hint) {
		struct fhkX_bucket *bucket = mrefp(S, hint);
		if(bucket->flags == flags && bucket->num < MAX_ROOT)
			return bucket;
		if(bucket->num == 0 && (bucket->flags ^ (flags & BUCKET_COPY)) == 0) {
			bucket->flags = flags;
			return bucket;
		}
		hint = bucket->next;
	}
	struct fhk_mem *mem = mrefp(S, S->mem);
	fhk_mem_alignT(mem, struct fhkX_bucket *);
	struct fhkX_bucket *bucket = mrefp(mem, mem->ptr);
	fhk_mem_bump(mem, MAX_ROOT*sizeof(fhkX_root));
	if(flags & BUCKET_COPY)
		fhk_mem_bump(mem, MAX_ROOT*sizeof(void *));
	fhk_mem_commit(mem);
	bucket->next = S->bucket;
	S->bucket = pmref(S, bucket);
	bucket->num = 0;
	bucket->flags = flags;
	return bucket;
}

void fhk_setroot(struct fhk_solver *S, int idx, fhk_subset ss) {
	if(UNLIKELY(subset_isE(ss))) return;
	int flags = idx < S->G->nz ? BUCKET_GIVEN : 0;
	struct fhkX_bucket *bucket = root_find_bucket(S, flags, S->bucket);
	if(LIKELY(subset_isI(ss))) {
		bucket->roots[bucket->num++] = root_newidx(idx) | root_newsubsetI(ss);
		// TODO trace
	} else {
		fhkX_pkref pk = subsetC_pk(ss);
		for(;;) {
			if(UNLIKELY(bucket->num == MAX_ROOT))
				bucket = root_find_bucket(S, flags, pmref(S, bucket));
			bucket->roots[bucket->num++] = root_newidx(idx) | root_newpk(pk);
			// TODO trace
			if(!pkref_more(pk)) return;
			pk = pkref_next(pk);
		}
	}
}

static void root_setC_pk(struct fhk_solver *S, int idx, fhkX_pkref pk, void *p,
		struct fhkX_bucket *bucket, size_t size) {
	for(;;) {
		if(UNLIKELY(bucket->num == MAX_ROOT))
			bucket = root_find_bucket(S, bucket->flags, pmref(S, bucket));
		bucket->roots[bucket->num] = root_newidx(idx) | root_newpk(pk) | bucket->num;
		bucket->ptr[bucket->num++] = p;
		// TODO trace
		if(!pkref_more(pk)) return;
		p += size*pkref_size(pk);
		pk = pkref_next(pk);
	}
}

void fhk_setrootC(struct fhk_solver *S, int idx, fhk_subset ss, void *p) {
	if(UNLIKELY(subset_isE(ss))) return;
	int flags = idx < S->G->nz ? (BUCKET_GIVEN|BUCKET_COPY) : BUCKET_COPY;
	struct fhkX_bucket *bucket = root_find_bucket(S, flags, S->bucket);
	if(LIKELY(subset_isI(ss))) {
		bucket->roots[bucket->num] = root_newidx(idx) | root_newsubsetI(ss) | bucket->num;
		bucket->ptr[bucket->num++] = p;
	} else {
		root_setC_pk(S, idx, subsetC_pk(ss), p, bucket, S->G->vars[idx].size);
	}
}

void *fhk_setrootD(struct fhk_solver *S, int idx, fhk_subset ss) {
	if(UNLIKELY(subset_isE(ss))) return NULL;
	struct fhk_var *x = &S->G->vars[idx];
	size_t size = x->size;
	int given = var_isG(x) ? BUCKET_GIVEN : 0;
	if(LIKELY(subset_isI(ss))) {
		void *vp = valueV(S->value, idx);
		if(!vp) {
			fhkX_anymap space = S->map[x->group];
			if(UNLIKELY(anymap_isU(space))) {
				fhk_fail(S, ecode(NOVALUE) | etagA(MAP, x->group));
				return NULL;
			}
			int shape = subsetIE_size(anymapK(space));
			vp = fhk_mem_newvalue(S, size, shape);
			valueV(S->value, idx) = vp;
			// maintain invariant: vp implies bitmap for given variables
			if(UNLIKELY(given && !S->stateG[idx]))
				S->stateG[idx] = fhk_mem_newbitmap(S, shape);
		}
		struct fhkX_bucket *bucket = root_find_bucket(S, given, S->bucket);
		bucket->roots[bucket->num++] = root_newidx(idx) | root_newsubsetI(ss);
		// TODO trace
		return vp + size*subsetI_first(ss);
	} else {
		fhkX_pkref spk = subsetC_pk(ss);
		fhkX_pkref pk = spk;
		int bufsize = 0;
		for(;;) {
			bufsize += pkref_size(pk);
			if(!pkref_more(pk)) break;
			pk = pkref_next(pk);
		}
		struct fhkX_bucket *bucket = root_find_bucket(S, given|BUCKET_COPY, S->bucket);
		void *p = fhk_mem_alloc(mrefp(S, S->mem), bufsize*size, GUESS_ALIGN(size));
		root_setC_pk(S, idx, spk, p, bucket, size);
		return p;
	}
}

/* ---- setvalue ---------------------------------------- */

static void vref_clear_interval(struct fhk_solver *S, int idx, fhkX_bitmap bm, int start, int end) {
	int off = start/64;
	uint64_t *M = bitmap_ref64(bm) + off;
	uint64_t m;
	if(off == end/64){
		uint64_t mask = bitmapW_ones64(bitmap_shift64(start)) | bitmapW_zeros64(bitmap_shift64(end));
		m = ~(*M | mask);
		*M &= mask;
		goto tail;
	}
	m = ~(*M | bitmapW_ones64(bitmap_shift64(start)));
	*M &= bitmapW_ones64(bitmap_shift64(start));
	for(;;){
		if(UNLIKELY(m))
			goto fail;
		M++;
		m = *M;
		if(++off == end/64){
			m = ~(m | bitmapW_zeros64(bitmap_shift64(end)));
			*M &= bitmapW_zeros64(bitmap_shift64(end));
			break;
		}else{
			m = ~m;
			*M = 0;
		}
	}
tail:
	if(UNLIKELY(m)){
fail:
		fhk_fail(S, ecode(WRITE) | etagA(NODE, idx) | etagB(INST, 64*off+bitmapW_ffs64(m)));
	}
}

static void *vref_prep(struct fhk_solver *S, xidx idx, fhk_subset ss, void *p) {
	if(UNLIKELY(subset_isE(ss))) return NULL;
	if(UNLIKELY(!input_assertV(S, idx))) return NULL;
	struct fhk_var *x = &S->G->vars[idx];
	if(UNLIKELY(!var_isG(x))) {
		fhk_fail(S, ecode(GIVEN) | etagA(NODE, idx));
		return NULL;
	}
	void **vp = &valueV(S->value, idx);
	if(*vp) return *vp;
	fhkX_anymap amg = S->map[x->group];
	if(UNLIKELY(anymap_isU(amg))) {
		// need to init vp but group size is unknown.
		fhk_fail(S, ecode(NOVALUE) | etagA(MAP, x->group));
		return NULL;
	}
	fhk_subset space = anymapK(amg);
	xinst num = subsetIE_size(space);
	// maintain invariant: value buffer exists => bitmap exists.
	if(!S->stateG[idx])
		S->stateG[idx] = fhk_mem_newbitmap(S, num);
	if(p && ss == space) {
		*vp = p;
		// bitmaps overflow to zeros, so a brutal memset is fine.
		memset(bitmap_ref64(S->stateG[idx]), 0, bitmap_size(num));
		trace(SETVALR, fhk_debug_sym(S->G, idx), p, fhk_debug_value(S, idx, 0));
		return NULL;
	}
	return *vp = fhk_mem_newvalue(S, x->size, num);
}

static void vref_copyvalue(struct fhk_solver *S, xidx idx, fhk_subset ss, void *p, void *px) {
	void *vp = vref_prep(S, idx, ss, px);
	if(UNLIKELY(!vp)) return;
	size_t size = S->G->vars[idx].size;
	fhkX_bitmap bm = S->stateG[idx];
	if(LIKELY(subset_isI(ss))) {
		int start = subsetI_first(ss);
		int num = subsetIE_size(ss);
		vref_clear_interval(S, idx, bm, start, start+num);
		memcpy(vp+start*size, p, size*num);
		trace(SETVALI, fhk_debug_sym(S->G, idx), start, num-1, fhk_debug_value(S, idx, start));
	} else {
		fhkX_pkref pk = subsetC_pk(ss);
		for(;;) {
			int start = pkref_first(pk);
			int num = pkref_size(pk);
			xinst skip = size*num;
			vref_clear_interval(S, idx, bm, start, start+num);
			memcpy(vp + size*start, p, skip);
			trace(SETVALI, fhk_debug_sym(S->G, idx), start, num-1, fhk_debug_value(S, idx, start));
			if(!pkref_more(pk)) return;
			p += skip;
			pk = pkref_next(pk);
		}
	}
}

void fhk_setvalue(struct fhk_solver *S, int idx, fhk_subset ss, void *p) {
	vref_copyvalue(S, idx, ss, p, p);
}

void fhk_setvalueC(struct fhk_solver *S, int idx, fhk_subset ss, void *p) {
	vref_copyvalue(S, idx, ss, p, NULL);
}

void *fhk_setvalueD(struct fhk_solver *S, int idx, fhk_subset ss) {
	void *vp = vref_prep(S, idx, ss, NULL);
	if(UNLIKELY(!vp)) return NULL;
	size_t size = S->G->vars[idx].size;
	fhkX_bitmap bm = S->stateG[idx];
	if(LIKELY(subset_isI(ss))) {
		int start = subsetI_first(ss);
		int num = subsetIE_size(ss);
		vref_clear_interval(S, idx, bm, start, start+num);
		trace(SETVALD, fhk_debug_sym(S->G, idx), start, num-1);
		return vp + start*size;
	} else {
		fhkX_pkref pk = subsetC_pk(ss);
		vp += size*pkref_first(pk);
		for(;;) {
			int start = pkref_first(pk);
			int num = pkref_size(pk);
			vref_clear_interval(S, idx, bm, start, start+num);
			trace(SETVALD, fhk_debug_sym(S->G, idx), start, num-1);
			if(!pkref_more(pk)) return vp;
			pk = pkref_next(pk);
		}
	}
}

/* ---- copysubset ---------------------------------------- */

static fhk_subset subset_copyC(struct fhk_solver *S, fhk_subset ss){
	fhkX_pkref pk0 = subsetC_pk(ss);
	fhkX_pkref pk = pk0;
	do {
		pk = pkref_next(pk);
	} while(pkref_more(pk));
	struct fhk_mem *mem = mrefp(S, S->mem);
	void *p = mrefp(mem, mem->ptr);
	// no alignment needed here.
	// pk points to the last range, so we have 5+3 = PKWORD_FULL bytes after pk to copy.
	size_t size = PKWORD_FULL + (intptr_t)pk - (intptr_t)pk0;
	fhk_mem_bump(mem, size);
	fhk_mem_commit(mem);
	memcpy(p, pk0, size);
	return subsetC_new(p);
}

fhk_subset fhk_copysubset(struct fhk_solver *S, fhk_subset ss){
	return subset_isC(ss) ? subset_copyC(S, ss) : ss;
}
