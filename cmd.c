#include "fhk.h"
#include "co.h"
#include "debug.h"
#include "def.h"
#include "solve.h"
#include "trace.h"

#include <assert.h>

/* solver control commands */

/* ---- input checks ---------------------------------------- */

static int input_assertV(struct fhk_solver *S, int idx){
	if(UNLIKELY((uint32_t)(S->G->nv - idx - 1) >= S->G->nv)){
		fhk_fail(S, ecode(INVAL) | etagE(NODE, idx));
		return 0;
	}
	return 1;
}

/* ---- setmap ---------------------------------------- */

static int setmapK(struct fhk_solver *S, xmap map, fhk_subset ss){
	if(UNLIKELY(!anymap_isU(S->mapstate[map]))){
		fhk_fail(S, ecode(WRITE) | etagA(MAP, map));
		return 0;
	}

	anymapK(S->mapstate[map]) = ss;
	trace(SETMAPK, map, ss);
	return 1;
}

void fhk_setmapK(struct fhk_solver *S, int map, fhk_subset ss){
	if(UNLIKELY(map >= S->G->nk)){
		fhk_fail(S, ecode(BOUND) | etagE(MAP, map));
		return;
	}

	setmapK(S, mapL_fromext(map, S->G->ng), ss);
}

void fhk_setmapI(struct fhk_solver *S, int map, int inst, fhk_subset ss){
	if(UNLIKELY(map < -S->G->ni)){
		fhk_fail(S, ecode(BOUND) | etagE(MAP, map));
		return;
	}

	fhkX_anymap am = S->mapstate[map];
	if(UNLIKELY(anymap_isU(am))){
		xgroup group = S->G->assoc_mapJ[map];
		if(UNLIKELY(anymap_isU(S->mapstate[group]))){
			fhk_fail(S, ecode(NOVALUE) | etagA(MAP, group));
			return;
		}
		anymapI(am) = fhk_solver_newmapI(S, subsetIE_size(anymapK(S->mapstate[group])));
		S->mapstate[map] = am;
	}

	if(UNLIKELY(!subset_isU(anymapII(am, inst)))){
		fhk_fail(S, ecode(WRITE) | etagA(MAP, map) | etagB(INST, inst));
		return;
	}

	anymapII(am, inst) = ss;
	trace(SETMAPI, map, inst, ss);
}

/* ---- shape ---------------------------------------- */

static int shape_setg(struct fhk_solver *S, xgroup group, uint32_t shape){
	if(UNLIKELY(shape > MAX_INST)){
		fhk_fail(S, ecode(INVAL) | etagE(INST, shape));
		return 0;
	}

	return setmapK(S, group, shape ? subsetI_newZ(shape-1, 0) : FHK_EMPTYSET);
}

void fhk_setshape(struct fhk_solver *S, int group, int shape){
	if(UNLIKELY(group > S->G->ng)){
		fhk_fail(S, ecode(BOUND) | etagE(GROUP, group));
		return;
	}

	shape_setg(S, group, shape);
}

void fhk_setshapeT(struct fhk_solver *S, uint32_t *shape){
	int ng = S->G->ng;
	for(int i=0;i<ng;i++){
		if(UNLIKELY(!shape_setg(S, i, shape[i])))
			return;
	}
}

/* ---- setroot ---------------------------------------- */

static struct fhkX_bucket *root_find_bucket(struct fhk_solver *S, struct fhkX_bucket *hint,
		int flags){

	while(hint){
		if(hint->flags == flags && bucket_free(hint) > 0)
			return hint; // exact match
		if(hint->used == 0 && (hint->flags ^ (flags & BUCKET_COPY)) == 0){
			// compatible empty
			hint->flags = flags;
			return hint;
		}
		hint = hint->next;
	}

	return fhk_solver_newbucket(S, flags);
}

static void root_put(struct fhkX_bucket *bucket, fhkX_root root){
	assert(bucket_free(bucket) > 0 && !bucket_checkC(bucket->flags));
	bucket->roots[bucket->used++] = root;
	trace(SETROOT, bucket->flags, (int)root_idx(root), (int)root_start(root), (int)root_znum(root));
}

static void root_putP(struct fhkX_bucket *bucket, fhkX_root root, void *p){
	assert(bucket_free(bucket) > 0 && bucket_checkC(bucket->flags));
	bucket->roots[bucket->used] = root | bucket->used;
	bucket->p[bucket->used] = p;
	bucket->used++;
	trace(SETROOTP, (uint8_t)bucket->flags, (int)root_idx(root), (int)root_start(root), (int)root_znum(root), p);
}

static void root_put_subsetIE(struct fhk_solver *S, fhkX_root tmpl, fhk_subset ss, void *p, int flags){
	if(UNLIKELY(subset_isE(ss))) return;
	struct fhkX_bucket *bucket = root_find_bucket(S, S->root, flags);
	fhkX_root root = tmpl | root_newsubsetI(ss);
	if(bucket_checkC(flags))
		root_putP(bucket, root, p);
	else
		root_put(bucket, root);
}

static void root_put_pk_copy(struct fhk_solver *S, fhkX_root tmpl, int flags, fhkX_pkref pk,
		void *p, int size){

	struct fhkX_bucket *bucket = root_find_bucket(S, S->root, flags);

	for(;;){
		root_putP(bucket, tmpl | root_newpk(pk), p);
		if(!pkref_more(pk))
			break;
		p += size*pkref_size(pk);
		pk = pkref_next(pk);
		if(!bucket_free(bucket))
			bucket = root_find_bucket(S, bucket->next, flags);
	}
}

static void root_put_pk(struct fhk_solver *S, fhkX_root tmpl, int flags, fhkX_pkref pk){
	struct fhkX_bucket *bucket = root_find_bucket(S, S->root, flags);

	for(;;){
		root_put(bucket, tmpl | root_newpk(pk));
		if(!pkref_more(pk))
			break;
		pk = pkref_next(pk);
		if(!bucket_free(bucket))
			bucket = root_find_bucket(S, bucket->next, flags);
	}
}

static void root_put_subset(struct fhk_solver *S, xidx idx, fhk_subset ss, void *p, int flags){
	if(UNLIKELY(!input_assertV(S, idx))) return;

	if(var_isG(&S->G->vars[idx]))
		flags |= BUCKET_GIVEN;

	if(subset_isIE(ss)){
		root_put_subsetIE(S, root_newidx(idx), ss, p, flags);
	}else if(bucket_checkC(flags)){
		root_put_pk_copy(S, root_newidx(idx), flags, subsetC_pk(ss), p, S->G->vars[idx].size);
	}else{
		root_put_pk(S, root_newidx(idx), flags, subsetC_pk(ss));
	}
}

void fhk_setroot(struct fhk_solver *S, int idx, fhk_subset ss){
	root_put_subset(S, idx, ss, NULL, 0);
}

void fhk_setrootC(struct fhk_solver *S, int idx, fhk_subset ss, void *p){
	root_put_subset(S, idx, ss, p, BUCKET_COPY);
}

void *fhk_setrootD(struct fhk_solver *S, int idx, fhk_subset ss){
	if(UNLIKELY(!input_assertV(S, idx))) return NULL;
	struct fhk_var *x = &S->G->vars[idx];

	if(subset_isIE(ss)){
		void *vp = valueV(S->value, idx);
		if(UNLIKELY(!vp)){
			fhkX_anymap space = S->mapstate[x->group];
			if(UNLIKELY(anymap_isU(space))){
				fhk_fail(S, ecode(NOVALUE) | etagA(MAP, x->group));
				return NULL;
			}

			int shape = subsetIE_size(anymapK(space));
			vp = fhk_solver_newvalue(S, x->size, shape);
			valueV(S->value, idx) = vp;

			// maintain invariant: vp implies bitmap for given variables
			if(UNLIKELY(var_isG(x) && !S->stateG[idx]))
				S->stateG[idx] = fhk_solver_newbitmap(S, shape);
		}

		root_put_subsetIE(S, root_newidx(idx), ss, NULL, var_isG(x) ? BUCKET_GIVEN : 0);
		return vp + x->size*subsetI_first(ss);
	}else{
		fhkX_pkref pk = subsetC_pk(ss);
		int bufnum = 0;
		for(;;){
			bufnum += pkref_size(pk);
			if(!pkref_more(pk))
				break;
			pk = pkref_next(pk);
		}
		void *p = fhk_alloc(S->arena, bufnum*x->size, GUESS_ALIGN(x->size));
		root_put_pk_copy(S,
				root_newidx(idx),
				BUCKET_COPY | (var_isG(x) ? BUCKET_GIVEN : 0),
				subsetC_pk(ss),
				p, x->size);
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
	void *vp = valueV(S->value, idx);
	if(vp) return vp;
	fhkX_anymap amg = S->mapstate[x->group];
	if(UNLIKELY(anymap_isU(amg))) {
		// need to init vp but group size is unknown.
		fhk_fail(S, ecode(NOVALUE) | etagA(MAP, x->group));
		return NULL;
	}
	fhk_subset space = anymapK(amg);
	xinst num = subsetIE_size(space);
	// maintain invariant: value buffer exists => bitmap exists.
	if(!S->stateG[idx])
		S->stateG[idx] = fhk_solver_newbitmap(S, num);
	if(p && ss == space) {
		valueV(S->value, idx) = p;
		// bitmaps overflow to zeros, so a brutal memset is fine.
		memset(bitmap_ref64(S->stateG[idx]), 0, bitmap_size(num));
		trace(SETVALR, fhk_debug_sym(S->G, idx), p, fhk_debug_value(S, idx, 0));
		return NULL;
	}
	vp = fhk_solver_newvalue(S, x->size, num);
	valueV(S->value, idx) = vp;
	return vp;
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

	size_t sz = PKWORD_FULL + (intptr_t)pk - (intptr_t)pk0;
	fhkX_pkref spk = fhk_alloc(S->arena, sz, PKWORD_ALIGN);
	memcpy(spk, pk0, sz);
	return subsetC_new(spk);
}

fhk_subset fhk_copysubset(struct fhk_solver *S, fhk_subset ss){
	return subset_isC(ss) ? subset_copyC(S, ss) : ss;
}
