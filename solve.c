#include "co.h"
#include "debug.h"
#include "def.h"
#include "fhk.h"
#include "solve.h"
#include "trace.h"

#include <assert.h>
#include <math.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* ---- flow control ---------------------------------------- */

static void yield_ok(struct fhk_solver *S){
	trace(YOK);
	fhk_yield(S, 0);
}

static void yield_shape(struct fhk_solver *S, xgroup group){
	trace(YSHAPE, group);
	fhk_yield(S, scode(SHAPE) | group);
}

static void yield_vref(struct fhk_solver *S, xidx idx, xinst inst){
	trace(YVAR, fhk_debug_sym(S->G, idx), inst);
	fhk_yield(S, scode(VREF) | (inst << 16) | idx);
}

static void yield_mapcallK(struct fhk_solver *S, xmap map){
	trace(YMAPK, mapL_fromext(map, S->G->ng), map);
	fhk_yield(S, scode(MAPCALLK) | map);
}

static void yield_mapcallI(struct fhk_solver *S, xmap map, xinst inst){
	trace(YMAPI, map, inst);
	fhk_yield(S, scode(MAPCALLI) | (inst << 16) | (map & 0xffff));
}

static void yield_modcall(struct fhk_solver *S, fhk_modcall *mc){
	trace(YMOD, fhk_debug_sym(S->G, mc->idx), mc->inst, mc->np, mc->nr);
	fhk_yield(S, scode(MODCALL) | (intptr_t)mc);
}

ERRFUNC static void yield_err_nyi(struct fhk_solver *S){
	fhk_yield(S, ecode(NYI));
	UNREACHABLE();
}

ERRFUNC static void yield_err_nomapK(struct fhk_solver *S, xmap map){
	fhk_yield(S, ecode(NOVALUE) | etagA(MAP, map));
	UNREACHABLE();
}

ERRFUNC static void yield_err_nomapJ(struct fhk_solver *S, xmap map, xinst inst){
	fhk_yield(S, ecode(NOVALUE) | etagA(MAP, map) | etagB(INST, inst));
	UNREACHABLE();
}

ERRFUNC static void yield_err_novar(struct fhk_solver *S, xidx xi, xinst inst){
	fhk_yield(S, ecode(NOVALUE) | etagA(NODE, xi) | etagB(INST, inst));
	UNREACHABLE();
}

ERRFUNC static void yield_err_depth(struct fhk_solver *S){
	fhk_yield(S, ecode(DEPTH));
	UNREACHABLE();
}

ERRFUNC static void yield_err_chain(struct fhk_solver *S, xidx xi, xinst inst){
	fhk_yield(S, ecode(CHAIN) | etagA(NODE, xi) | etagB(INST, inst));
	UNREACHABLE();
}

/* ---- scratch space management ---------------------------------------- */

static void scratch_grow(struct fhk_solver *S, uint32_t minsize){
	uint32_t size = S->scratch.size;

	// old scratch buffers are forgotten and never reused,
	// so we grow really aggressively here to minimize the number
	// of wasted buffers.
	do {
		size = (3 * size) + SCRATCH_MINSIZE;
	} while(size < minsize);

	void *newp = fhk_alloc(S->arena, size, SCRATCH_ALIGN);

	if(S->scratch.mark < S->scratch.used)
		memcpy(newp, S->scratch.p, S->scratch.used - S->scratch.mark);

	S->scratch.size = size;
	S->scratch.used = 0;
	S->scratch.mark = scratch_checkM(S->scratch.mark) ? 0 : SCRATCH_NOMARK;
	S->scratch.p = newp;
}

static void *scratch_more(struct fhk_solver *S, uint32_t size){
	size = ALIGN(size, SCRATCH_ALIGN);
	if(UNLIKELY(S->scratch.used + size > S->scratch.size))
		scratch_grow(S, S->scratch.used + size);
	void *p = S->scratch.p + S->scratch.used;
	S->scratch.used += size;
	return p;
}

static void scratch_mark(struct fhk_solver *S){
	S->scratch.mark = S->scratch.used;
}

static void *scratch_atmark(struct fhk_solver *S){
	assert(scratch_checkM(S->scratch.mark));
	return S->scratch.p + S->scratch.mark;
}

static void *scratch_commit(struct fhk_solver *S){
	void *p = scratch_atmark(S);
	S->scratch.mark = SCRATCH_NOMARK;
	return p;
}

static void scratch_reset(struct fhk_solver *S){
	S->scratch.used = 0;
	assert(!scratch_checkM(S->scratch.mark));
}

/* ---- state management ---------------------------------------- */

// S->mapstate[map] must be allocated before calling this
static void yf_state_mapcallJ(struct fhk_solver *S, xmap map, xinst inst){
	yield_mapcallI(S, map, inst);
	if(UNLIKELY(subset_isU(anymapII(S->mapstate[map], inst))))
		yield_err_nomapJ(S, map, inst);
}

static void yf_state_checkmapJ(struct fhk_solver *S, xmap map, xinst inst){
	fhkX_anymap state = S->mapstate[map];
	assert(!anymap_isU(state));
	if(!subset_isU(anymapII(state, inst)))
		return;
	yf_state_mapcallJ(S, map, inst);
}

static void yf_state_checkanymapJ(struct fhk_solver *S, xmap map, xinst inst){
	if(LIKELY(!map_isJ(map)))
		return;
	yf_state_checkmapJ(S, map, inst);
}

static void yf_state_mapcallK(struct fhk_solver *S, xmap map){
	if(LIKELY(map_isL(map, S->G->ng)))
		yield_mapcallK(S, mapL_toext(map, S->G->ng));
	else
		yield_shape(S, map);
	if(UNLIKELY(anymap_isU(S->mapstate[map])))
		yield_err_nomapK(S, map);
}

AINLINE static void yf_state_checkmapK(struct fhk_solver *S, xmap map){
	if(LIKELY(!anymap_isU(S->mapstate[map])))
		return;
	yf_state_mapcallK(S, map);
}

static void yf_state_newmapJ(struct fhk_solver *S, xmap map){
	xgroup group = S->G->assoc_mapJ[map];
	yf_state_checkmapK(S, group);
	anymapI(S->mapstate[map]) = fhk_solver_newmapI(S, subsetIE_size(anymapK(S->mapstate[group])));
}

static void yf_state_setanymap(struct fhk_solver *S, xmap map){
	if(map_isK(map))
		yf_state_mapcallK(S, map);
	else
		yf_state_newmapJ(S, map);
}

AINLINE static void yf_state_checkanymap(struct fhk_solver *S, xmap map){
	assert(map_isE(map));
	if(LIKELY(!anymap_isU(S->mapstate[map])))
		return;
	yf_state_setanymap(S, map);
}

static fhkX_sp *yf_state_newsp(struct fhk_solver *S, fhkX_sp init, xgroup group){
	yf_state_checkmapK(S, group);
	xinst size = subsetIE_size(anymapK(S->mapstate[group]));
	return fhk_solver_newsp(S, size, init);
}

// note: this does NOT expand forward edges.
// forward edges are expanded by yf_state_newvalueM.
static void yf_state_newM(struct fhk_solver *S, xidx idx){
	struct fhk_model *m = &S->G->models[idx];

	uint32_t expanded = 1;

	fhk_check *checks = m->checks;
	for(int i=m->p_check;i;i++){
		xmap map = checks[i].map;
		expanded &= !map_isJ(map);
		if(map_isE(map))
			yf_state_checkanymap(S, map);
	}

	fhk_edge *params = m->params;
	int nc = m->p_cparam;
	for(int i=0;i<nc;i++){
		xmap map = params[i].map;
		expanded &= !map_isJ(map);
		if(map_isE(map))
			yf_state_checkanymap(S, map);
	}

	S->stateM[idx] = yf_state_newsp(S, sp_new(expanded << SP_EXPANDED_BIT, m->cmin), m->group);
}

AINLINE static void yf_state_checkM(struct fhk_solver *S, xidx idx){
	if(LIKELY(S->stateM[idx]))
		return;
	yf_state_newM(S, idx);
}

static void yf_state_newV(struct fhk_solver *S, xidx idx){
	struct fhk_var *x = &S->G->vars[idx];
	assert(var_isC(x));

	uint32_t expanded = 1;
	int64_t i = 0, nm = x->n_mod;
	fhk_edge *models = x->models;
	do {
		xmap map = models[i].map;
		expanded &= !map_isJ(map);
		if(map_isE(map))
			yf_state_checkanymap(S, map);
	} while(++i < nm);

	S->stateV[idx] = yf_state_newsp(S, sp_new(expanded << SP_EXPANDED_BIT, 0), x->group);
}

AINLINE static void yf_state_checkV(struct fhk_solver *S, xidx idx){
	if(LIKELY(S->stateV[idx]))
		return;
	yf_state_newV(S, idx);
}

static void yf_state_newG(struct fhk_solver *S, xidx idx){
	xgroup group = S->G->vars[idx].group;
	yf_state_checkmapK(S, group);
	S->stateG[idx] = fhk_solver_newbitmap(S, subsetIE_size(anymapK(S->mapstate[group])));
}

AINLINE static void yf_state_checkG(struct fhk_solver *S, xidx idx){
	if(LIKELY(S->stateG[idx]))
		return;
	yf_state_newG(S, idx);
}

static void yf_state_newC(struct fhk_solver *S, xidx idx){
	xgroup group = S->G->guards[idx].group;
	yf_state_checkmapK(S, group);
	S->stateC[idx] = fhk_solver_newcheckmap(S, subsetIE_size(anymapK(S->mapstate[group])));
}

AINLINE static void yf_state_checkC(struct fhk_solver *S, xidx idx){
	if(LIKELY(S->stateC[idx]))
		return;
	yf_state_newC(S, idx);
}

static void yf_state_newvalueV(struct fhk_solver *S, xidx idx){
	struct fhk_var *x = &S->G->vars[idx];
	assert(var_isC(x));
	size_t size = x->size;
	xgroup group = x->group;
	yf_state_checkmapK(S, group);
	valueV(S->value, idx) = fhk_solver_newvalue(S, size, subsetIE_size(anymapK(S->mapstate[group])));
}

AINLINE static void yf_state_checkvalueV(struct fhk_solver *S, xidx idx){
	if(LIKELY(valueV(S->value, idx)))
		return;
	yf_state_newvalueV(S, idx);
}

// note: unlike yf_state_newM, this function actually allocates states for
// given and return edges, since they will definitely be needed for computing the value.
static void yf_state_newvalueM(struct fhk_solver *S, xidx idx){
	struct fhk_model *m = &S->G->models[idx];

	fhk_edge *params = m->params;
	int64_t np = m->p_param;
	for(int64_t i=m->p_cparam;i<np;i++){
		yf_state_checkG(S, params[i].idx);
		if(map_isE(params[i].map))
			yf_state_checkanymap(S, params[i].map);
	}

	fhk_edge *re = m->returns;
	int i = 0, nr = m->p_return;
	do {
		// if the model returns multiple values, all returns may not have state,
		// so we explicitly check it here.
		yf_state_checkV(S, re->idx);
		// same for return values.
		yf_state_checkvalueV(S, re->idx);
		if(map_isE(re->map))
			yf_state_checkanymap(S, re->map);
		re++;
	} while(++i < nr);

	// this may be later patched to a retbuf address, if a retbuf is allocated
	valueM(S->value, idx) = 1;
}

AINLINE static void yf_state_checkvalueM(struct fhk_solver *S, xidx idx){
	if(LIKELY(valueM(S->value, idx)))
		return;
	yf_state_newvalueM(S, idx);
}

/* ---- maps, subset and iterators ---------------------------------------- */

static fhk_subset yf_map_subset_checkedJ(struct fhk_solver *S, xmap map, xinst inst){
	assert(map_isE(map));

	fhkX_anymap am = S->mapstate[map];
	assert(!anymap_isU(am));

	if(map_isI(map)){
		fhk_subset ss = anymapII(am, inst);
		if(UNLIKELY(subset_isU(ss))){
			yf_state_mapcallJ(S, map, inst);
			return anymapII(am, inst);
		}else{
			return ss;
		}
	}else{
		return anymapK(am);
	}
}

static fhk_subset map_subset_unchecked(struct fhk_solver *S, xmap map, xinst inst){
	assert(map_isE(map));

	fhkX_anymap am = S->mapstate[map];
	assert(!anymap_isU(am));

	if(map_isI(map)){
		fhk_subset ss = anymapII(am, inst);
		assert(!subset_isU(ss));
		return ss;
	}else{
		return anymapK(am);
	}
}

// very evil match-type macro to make map code a bit more readable.
// note: place this in a block, eg: { ... }
#define MAP_UNPACK_(_subset, S, map, inst, _x) \
	__label__ ident, empty, interval, complex; \
	fhk_subset _x; \
	xmap _map = (map); \
	xinst _inst = (inst); \
	if(map_isID(map)){ _x = _inst; goto ident; } \
	_x = _subset(S, _map, (inst)); \
	if(subset_isI(_x)) goto interval; \
	if(subset_isE(_x)) goto empty; \
	goto complex;

#define MAP_UNPACK_UNCHECKED(...) MAP_UNPACK_(map_subset_unchecked, __VA_ARGS__)

// note: checked unpacks may yield!
#define MAP_UNPACK_CHECKEDJ(...)  MAP_UNPACK_(yf_map_subset_checkedJ, __VA_ARGS__)

// evil macro
#define ITER_NEXT(it, pk, continue_, break_) \
{ \
	it = iter_step(it); \
	if(LIKELY(iter_moreI(it))) { continue_; } \
	if(UNLIKELY(iter_moreC(it))){ \
		pk = pkref_next(pk); \
		it = pkref_iter_next(pk); \
		continue_; \
	} \
	break_; \
}

/* ---- shadows / checks ---------------------------------------- */

static int check_scan_batchC(fhkX_checkmap cmbase, fhkX_sp *spbase, int inst, int end){
	if(UNLIKELY(inst == end))
		goto out;

	int next = inst + 1;
	int off = bitmap_idx64(next);
	int block = 64*off;
	uint64_t *E = bitmap_ref64(checkmap_refE(cmbase)) + 2*off;
	fhkX_sp *sp = spbase + next;
	uint64_t mask = *E & ~bitmapW_ones64(next-block);

	// we are looking for a run of instances that have a value and are not evaluated.
	// iow: we are looking for the first instance that either has no value or is already evaluated.
	for(;;){
		if(mask){
			// this block contains ones so it's the last block.
			int fi = block + bitmapW_ffs64(mask);

			// start has been masked out, and therefore:
			assert(fi-1 >= inst);

			// overflow bits are one-initialized. in particular, this means that if end%64 != 0,
			// then bit(E, end+1) = 1, so we also have:
			assert(fi-1 <= end);

			// and by the previous inequality we may set
			end = fi-1;
			if(inst == end)
				goto out;
		}

		int scanto = min(end, block+63);

		// we maintain the invariant `inst < end`.
		// otoh, we have block points to the start of the block containing `inst+1`.
		// if `inst` is the last in a block, then `block` points to the start of the next block,
		// so we have `block = inst+1`.
		// otherwise, `inst` is not last, so `inst < block+63`.
		// either way, we have:
		assert(inst < scanto);

		do {
			if(!sp_checkV(sp->state))
				goto out;
			sp++;
		} while(++inst < scanto);

		if(inst == end)
			goto out;

		// inst now points to the end of a block,
		// and `block` will point to the start of the next block.
		block += 64;
		E += 2;
		mask = *E;
	}

out:
	return inst;
}

static int check_scan_batchG(fhkX_checkmap cmbase, fhkX_bitmap bmbase, int inst, int end){
	if(UNLIKELY(inst == end))
		return inst;

	int next = inst + 1;
	int off = bitmap_idx64(next);
	int block = 64*off;
	uint64_t *M = bitmap_ref64(bmbase) + off;
	uint64_t *E = bitmap_ref64(checkmap_refE(cmbase)) + 2*off;
	uint64_t mask = (*M | *E) & ~bitmapW_ones64(next-block);

	// we are looking for a run of instances that have a value and are not evaluated
	// iow: we are looking for the first one in M | E (value missing or already evaluated)
	for(;;){
		if(mask){
			int fi = block + bitmapW_ffs64(mask);

			// start is masked out, so we have:
			assert(fi-1 >= inst);

			// overflow part of E is one-initialized, ie: the if there is an overflow part,
			// the first bit will be one, so we have:
			assert(fi-1 <= end);

			return fi - 1;
		}

		block += 64;

		// this inequality is strict: if block=end, then we must scan the bit `block`,
		// and possibly return end-1.
		if(block > end)
			return end;

		M++;
		E += 2;
		mask = *M | *E;
	}
}

static void check_setE(fhkX_checkmap cmbase, int start, int end){
	int off = bitmap_idx64(start);
	uint64_t *E = bitmap_ref64(checkmap_refE(cmbase)) + 2*off;

	if(off == bitmap_idx64(end)){
		*E |= bitmapW_zeros64(bitmap_shift64(start)) & bitmapW_ones64(bitmap_shift64(end+1));
	}else{
		*E++ |= bitmapW_zeros64(bitmap_shift64(start));
		while(++off < bitmap_idx64(end))
			*E++ = ~(uint64_t)0;
		*E |= bitmapW_ones64(bitmap_shift64(end+1));
	}
}

static void yf_check_eval_batch(struct fhk_guard *guard, fhkX_checkmap cmbase, void *vpbase,
		int inst, int end){

	static const void *_label[]    = { &&f32_ge, &&f32_le, &&f64_ge, &&f64_le, &&u8_m64 };
	static const uint8_t _stride[] = { 4,        4,        8,        8,        1 };

	// before we do anything else, we can first set all eval bits to one
	check_setE(cmbase, inst, end);

	int opcode = guard->opcode;

	// the pass bits will be zeros, we only need to toggle them on if it passes
	const void *L = _label[opcode];
	int stride = _stride[opcode];
	void *vp = vpbase + stride*inst;
	uint64_t *P = bitmap_ref64(checkmap_refP(cmbase)) + 2*bitmap_idx64(inst);
	uint64_t p = *P;
	uint64_t bit = bitmap_shift64(inst);
	int num = end - inst;

	float f32 = guard->arg.f32;
	double f64 = guard->arg.f64;
	uint64_t u64 = guard->arg.u64;
	uint64_t ok = 0;

	goto *L;

f32_ge: ok = *(float *)vp >= f32; goto next;
f32_le: ok = *(float *)vp <= f32; goto next;
f64_ge: ok = *(double *)vp >= f64; goto next;
f64_le: ok = *(double *)vp <= f64; goto next;
u8_m64: ok = !!((1ULL << *(uint8_t *)vp) & u64); goto next;

next:
	p |= ok << bit;

	if(!num){
		*P = p;
		return;
	}

	num--;
	vp += stride;

	if(bit == 63){
		*P = p;
		P += 2;
		p = *P;
		bit = 0;
	}else{
		bit++;
	}

	goto *L;
}

/* ---- evaluation ---------------------------------------- */

static void yf_eval_varG(struct fhk_solver *S, xidx xi, xinst inst){
	assert(bitmap_is1(S->stateG[xi], inst));
	yield_vref(S, xi, inst);
	if(UNLIKELY(bitmap_is1(S->stateG[xi], inst)))
		yield_err_novar(S, xi, inst);
}

AINLINE static void yf_eval_checkvarG(struct fhk_solver *S, xidx xi, xinst inst){
	if(LIKELY(bitmap_is0(S->stateG[xi], inst)))
		return;
	yf_eval_varG(S, xi, inst);
}

static void yf_eval_varV(struct fhk_solver *S, xidx xi, xinst inst);

static void yf_eval_checkmapV(struct fhk_solver *S, xmap map, xidx xi, xinst inst){
	fhkX_pkref pk;
	fhkX_iter it;

	// unchecked: computed parameter maps were expanded when solver entered the model
	{
		MAP_UNPACK_UNCHECKED(S, map, inst, ss);
		if(0) { empty: return; }
		if(0) { ident:
			if(!sp_checkV(S->stateV[xi][inst].state))
				yf_eval_varV(S, xi, inst);
			return;
		}
		if(0) { interval: it = ss; }
		if(0) { complex:
			pk = subsetC_pk(ss);
			it = pkref_iter_first(pk);
		}
	}

	fhkX_sp *sp = S->stateV[xi];

	for(;;){
		if(!sp_checkV(sp[iter_inst(it)].state))
			yf_eval_varV(S, xi, iter_inst(it));
		ITER_NEXT(it, pk, continue, return);
	}
}

static void yf_eval_checkintervalG(struct fhk_solver *S, xidx xi, int start, int znum){
	// note: stateG accesses are unchecked.

	int end = start + znum;
	int block = 64*bitmap_idx64(start);
	uint64_t *M = bitmap_ref64(S->stateG[xi]) + bitmap_idx64(start);
	uint64_t mask = *M & ~bitmapW_ones64(start-block);

	do {
		while(mask){
			int fi = block + bitmapW_ffs64(mask);
			if(fi > end)
				return;
			yf_eval_varG(S, xi, fi);
			mask &= *M; // `&` to keep the start masked out
		}
		block += 64;
		M++;
		mask = *M;
	} while(block <= end);
}

static void yf_eval_checkmapG(struct fhk_solver *S, xmap map, xidx xi, xinst inst){
	// checked: solver doesn't expand given edges
	MAP_UNPACK_CHECKEDJ(S, map, inst, ss);

	fhkX_pkref pk;

empty:
	return;

ident:
	yf_eval_checkvarG(S, xi, inst);
	return;

interval:
	yf_eval_checkintervalG(S, xi, subsetI_first(ss), subsetIE_znum(ss));
	return;

complex:
	pk = subsetC_pk(ss);
	for(;;){
		yf_eval_checkintervalG(S, xi, pkref_first(pk), pkref_znum(pk));
		if(!pkref_more(pk))
			return;
		pk = pkref_next(pk);
	}
}

static void yf_eval_checkparams(struct fhk_solver *S, xidx mi, xinst inst){
	struct fhk_model *m = &S->G->models[mi];
	fhk_edge *e = m->params;

	// computed
	int nc = m->p_cparam;
	for(int i=0;i<nc;i++,e++)
		yf_eval_checkmapV(S, e->map, e->idx, inst);

	// given.
	// note: yf_state_newvalueM must be called before this to expand stateG.
	int np = m->p_param;
	for(int i=nc;i<np;i++,e++)
		yf_eval_checkmapG(S, e->map, e->idx, inst);
}

AINLINE static int eval_replace_speculate(struct fhk_solver *S, xidx idx, uint32_t state, float cost){
	assert(sp_checkV(state) && !sp_checkC(state));
	struct fhk_var *x = &S->G->vars[idx];
	xidx smi = x->models[spV_edge(state)].idx;
	fhkX_sp *smsp = S->stateM[smi] + spV_inst(state);
	// replace aggressively here: if we have an equal cost, drop the old value.
	// it doesn't really matter, but this lets us do more direct writes in some edge cases.
	return cost <= smsp->cost;
}

AINLINE static int eval_try_put_direct(struct fhk_solver *S, xidx idx, fhkX_sp *sp,
		uint32_t templ, float cost){

	uint32_t state = sp->state;
	uint32_t cstate = (state & (SP_CHAIN|SP_EXPANDED)) | (SP_VALUE | templ);

	if(UNLIKELY(sp_checkV(state))){
		if(sp_checkC(state) || !eval_replace_speculate(S, idx, state, cost)){
			// either a chain with a value exists,
			// or a better speculated value exists.
			// we may not overwrite here.
			return 0;
		}

		// our speculated value is better, we may overwrite and commit
		sp->state = cstate;
	}else{
		// we have
		// (state ^ checkstate)  >  0   <==>   state has a chain which is different from ours
		//                       =  0   <==>   state = checkstate, ie. state has our chain
		//                       <  0   <==>   state has no chain because SP_CHAIN is the sign bit
		//
		// note: the ">=0" cases hold because C implies E, so that the non-zero bits in
		// state^checkstate must come from the chain (we know that V=0).
		//
		// this means we can use the following check to commit iff no different chain
		// is already selected.
		sp->state = (int32_t)(state ^ (SP_CHAIN | SP_EXPANDED | templ)) <= 0 ? cstate : state;
	}

	return 1;
}

static void eval_scatter_put_header(struct fhk_solver *S, int ei){
	fhkX_scatter *scatter = scratch_more(S, sizeof(*scatter));
	*scatter = scatterH_new(ei);
}

static void eval_scatter_put_range(struct fhk_solver *S, int bpos, int vpos, int num){
	if(!num)
		return;

	fhkX_scatter *scatter = scratch_more(S, sizeof(*scatter));
	*scatter = scatterR_new(num, vpos, bpos);
}

static void eval_scatter_put_end(struct fhk_solver *S){
	fhkX_scatter *scatter = scratch_more(S, sizeof(*scatter));
	*scatter = SCATTER_END;
}

static int eval_scatter_put_split_range(struct fhk_solver *S, xidx idx, int start,
		int bstart, int num, uint32_t templ, float cost){

	int inst = start;
	int bpos = bstart;
	int write = 0;

	fhkX_sp *sp = S->stateV[idx] + start;

	for(;;){
		uint32_t state = sp->state;
		uint32_t cstate = (state & (SP_CHAIN|SP_EXPANDED)) | (SP_VALUE | templ);

		// we must commit iff one of the following is true:
		//     (1) this model's chain is selected
		//     (2) no chain is selected and no value is speculated
		//     (3) no chain is selected, a value is speculated, and we replace the speculated value
		//
		// the value of `state` corresponding to each case is:
		//     (1) 101 [templ]
		//     (2) 00e 000...000
		//     (3) 01e xxx...xxx
		//
		// we will never in any case overwrite anything starting with `11...`: these are values
		// with final chains that have been evaluated.
		//
		// for (1)-(2) we test:
		//     (state^0b101_templ) * (state&0b00e000...000)   ==   0
		//     ^^^^^^^^^^^^^^^^^^    ^^^^^^^^^^^^^^^^^^^^^^        ^
		//      zero iff case (1)      zero iff case (2)           zero iff (1) or (2)
		//
		// these are the 2 common cases, and this is the fast path.
		//
		// for case (3) we test:
		//     (signed) state >= 0b010000...000
		// ie.
		//     state \in [ 0b010000...000, 0b011111...111 ]
		// and if it passes, test the overwrite condition.
		uint64_t w = (uint64_t)(state^(SP_CHAIN|SP_EXPANDED|templ)) * (uint64_t)(state&~SP_EXPANDED);
		int _vx = (int32_t)state >= (int32_t)SP_VALUE;
		if(LIKELY(!w) || (_vx && eval_replace_speculate(S, idx, state, cost))){
			write++;
			sp->state = cstate;
		}else{
			eval_scatter_put_range(S, bpos, start, write);
			bpos += write;
			write = 0;
			start = inst+1;
		}

		if(!--num)
			break;

		sp++;
		inst++;
	}

	eval_scatter_put_range(S, bpos, start, write);
	return bpos + write;
}

static void yf_eval_put_returns(struct fhk_solver *S, xidx mi, xinst inst, fhk_modcall *mc,
		float cost){

	fhk_cedge *ce = mcall_returns(mc);
	struct fhk_model *m = &S->G->models[mi];
	fhk_edge *re = m->returns;
	xedge ei = 0, nr = m->p_return;
	uint32_t templ = spV_newchain(inst, 0);

	do {
		xmap map = re->map;
		xidx idx = re->idx;
		uint32_t size = S->G->vars[idx].size;
		uint32_t etempl = templ | edgeR_reverse(*re);

		// checked: solver doesn't expand return edges
		{
			MAP_UNPACK_CHECKEDJ(S, map, inst, ss);
empty:
			ce->p = NULL;
			ce->n = 0;
			goto next;

interval:
			if(subset_is1(ss))
				goto ident;
			{
				int start = subsetI_first(ss);
				int num = subsetIE_size(ss);
				fhkX_sp *sp = S->stateV[idx] + start;
				ce->n = num;

				for(int off=0;;off++,sp++){
					if(!eval_try_put_direct(S, idx, sp, etempl, cost)){
						// can't directly write to this range, fallback to a scatter
						ce->p = scatter_mark(num*size);
						eval_scatter_put_header(S, ei);
						eval_scatter_put_range(S, 0, start+off, off);
						if(--num)
							eval_scatter_put_split_range(S, idx, start+off+1, off, num, etempl, cost);
						goto next;
					}

					if(!--num)
						goto direct;
				}
			}

complex:
			{
				int tot = 0, bpos = 0;

				eval_scatter_put_header(S, ei);
				fhkX_pkref pk = subsetC_pk(ss);
				for(;;){
					int num = pkref_size(pk);
					int start = pkref_first(pk);
					tot += num;
					bpos = eval_scatter_put_split_range(S, idx, start, bpos, num, etempl, cost);
					if(!pkref_more(pk))
						break;
					pk = pkref_next(pk);
				}

				ce->n = tot;
				ce->p = scatter_mark(tot*size);
				goto next;
			}

ident:
			ce->n = 1;
			if(eval_try_put_direct(S, idx, S->stateV[idx]+ss, etempl, cost)){
				goto direct;
			}else{
				ce->p = scatter_mark(size);
				goto next;
			}

direct:
			ce->p = valueV(S->value, idx) + subsetI_first(ss)*size;
next:
			ce++;
			re++;
		}
	} while(++ei < nr);
}

static void eval_put_scatter_buffers(struct fhk_solver *S, fhk_modcall *mc){
	fhk_cedge *ce = mcall_returns(mc);
	int nr = mc->nr;

	do {
		if(scatter_checkM(ce->p))
			ce->p = scratch_more(S, scatterM_size(ce->p));
		ce++;
	} while(--nr);
}

static void eval_put_params(struct fhk_solver *S, xidx mi, xinst inst, fhk_modcall *mc){
	fhk_cedge *pe = mcall_params(mc);
	struct fhk_model *m = &S->G->models[mi];
	int np = m->p_param;
	fhk_edge *e = m->params;

	while(np--){
		xidx idx = e->idx;
		fhk_cedge *ce = pe + edgeP_order(*e);
		void *vp = valueV(S->value, idx);
		uint32_t size = S->G->vars[idx].size;

		{
			MAP_UNPACK_UNCHECKED(S, e->map, inst, ss);
			if(0) { empty:
				ce->p = NULL;
				ce->n = 0;
			}
			if(0) { ident:
				ce->p = vp + inst*size;
				ce->n = 1;
			}
			if(0) { interval:
				ce->p = vp + subsetI_first(ss)*size;
				ce->n = subsetIE_size(ss);
			}
			if(0) { complex:
				scratch_mark(S);
				uint32_t total = 0;
				fhkX_pkref pk = subsetC_pk(ss);
				for(;;){
					uint32_t pos = pkref_first(pk);
					uint32_t num = pkref_size(pk);
					total += num;
					void *p = scratch_more(S, num*size);
					memcpy(p, vp + pos*size, num*size);
					if(!pkref_more(pk))
						break;
					pk = pkref_next(pk);
				}
				ce->p = scratch_commit(S);
				ce->n = total;
			}
		}

		e++;
	}
}

static void eval_write_scatter(struct fhk_solver *S, xidx mi, fhk_modcall *mc, fhkX_scatter *s){
	fhkX_scatter sw = *s;
	if(scatter_isE(sw))
		return;

	struct fhk_model *m = &S->G->models[mi];
	fhk_edge *returns = m->returns;
	void *vp, *bp;
	uint32_t size;

	do {
		if(scatter_isH(sw)){
			xedge ei = scatterH_edge(sw);
			xidx idx = returns[ei].idx;
			vp = valueV(S->value, idx);
			size = S->G->vars[idx].size;
			bp = mcall_returns(mc)[ei].p;
		}else{
			uint32_t vpos = scatterR_vpos(sw);
			uint32_t bpos = scatterR_bpos(sw);
			uint32_t num = scatterR_num(sw);
			memcpy(vp + vpos*size, bp + bpos*size, num*size);
		}
		sw = *++s;
	} while(!scatter_isE(sw));
}

static void yf_eval_modcall(struct fhk_solver *S, xidx mi, xinst inst){
	fhkX_sp *sp = S->stateM[mi] + inst;
	assert(!sp_checkV(sp->state));
	float cost = sp->cost;
	sp->state |= SP_VALUE;

	yf_state_checkvalueM(S, mi);

	// make sure every parameter has a value
	yf_eval_checkparams(S, mi, inst);

	// after this point we can't recurse anymore.
	// we can now prepare the modcall.
	scratch_reset(S);
	struct fhk_model *m = &S->G->models[mi];
	fhk_modcall *mc = scratch_more(S, sizeof(*mc) + (m->p_param+m->p_return)*sizeof(*mc->edges));
	mc->np = m->p_param;
	mc->nr = m->p_return;
	mc->idx = mi;
	mc->inst = inst;

	// build return values.
	// this must be done after parameters, so that we don't recursively use the scratch buffer.
	scratch_mark(S);
	yf_eval_put_returns(S, mi, inst, mc, cost);
	eval_scatter_put_end(S);
	fhkX_scatter *scatter = scratch_commit(S);

	// allocate scatters for return values.
	// this must be done only after building the entire scatter table, so that we don't
	// interleave the scatter table with the actual buffers
	eval_put_scatter_buffers(S, mc);

	// collect parameters.
	// this could be done at any point after recursion, it doesn't matter.
	eval_put_params(S, mi, inst, mc);

	// perform the modcall!
	yield_modcall(S, mc);

	// write back return value scatters
	eval_write_scatter(S, mi, mc, scatter);
}

static void yf_eval_varV(struct fhk_solver *S, xidx xi, xinst inst){
	fhkX_sp *sp = S->stateV[xi] + inst;
	assert(sp_checkC(sp->state) && !sp_checkV(sp->state));

	struct fhk_var *x = &S->G->vars[xi];
	xedge ei = spV_edge(sp->state);
	xinst m_inst = spV_inst(sp->state);
	yf_eval_modcall(S, x->models[ei].idx, m_inst);

	assert(sp_checkV(sp->state));
}

/* ---- solver ---------------------------------------- */

static int yf_solver_enterV(struct fhk_solver *S, xidx xi, xinst inst, struct fhkX_work *W){
	struct fhk_var *x = &S->G->vars[xi];
	assert(var_isC(x));

	int nm = x->n_mod;
	fhk_edge *models = x->models;

	fhkX_sp *sp = S->stateV[xi] + inst;
	assert(!sp_done(*sp));

	W->sp = sp;
#if FHK_TRACEON(solver)
	W->idx = xi;
	W->inst = inst;
#endif

	if(UNLIKELY(sp_checkM(*sp)))
		yield_err_nyi(S); // cycle

	sp->cost = SP_MARK;

	if(!sp_checkE(sp->state)){
		sp->state |= SP_EXPANDED;

		// model sp's will be checked in the next loop.
		// k-maps were checked while allocating the sp, so all that's left to expand here
		// are the j-maps.
		// because the sp allocator didn't set SP_EXPANDED, it means that there must be
		// some instance maps to expand.
		int en = nm;
		fhk_edge *e = models;
		do {
			yf_state_checkanymapJ(S, e->map, inst);
			e++;
		} while(--en);
	}

	struct fhkX_cselector *s = (struct fhkX_cselector *) slotref(W);
	int ei = 0, cnum = 0;
	fhk_edge *e = models;
	do {
		fhkX_iter it;
		xidx idx = e->idx;

		// unchecked: see expand loop above
		{
			MAP_UNPACK_UNCHECKED(S, e->map, inst, ss);
			if(0) { empty: goto next; }
			if(0) { ident: interval: it = ss; }
			if(0) { complex:
				(s-1)->pk = subsetC_pk(ss);
				it = pkref_iter_first((s-1)->pk);
			}
		}

		yf_state_checkM(S, idx);
		s--;
		cnum++;
		s->it = it;
		s->sp = S->stateM[idx] + iter_inst(it);
		s->info.idx = idx;
		s->info.ei = ei;

next:
		e++;
	} while(++ei < nm);

	return W->cnum = cnum;
}

static void yf_solver_enterM(struct fhk_solver *S, xidx idx, xinst inst){
	fhkX_sp *sp = S->stateM[idx] + inst;

	// sp->state must be zero before entering solver for the first time, which expands it.
	if(sp->state){
		assert(sp_checkE(sp->state));
		return;
	}

	sp->state = SP_EXPANDED;

	struct fhk_model *m = &S->G->models[idx];

	fhk_check *ce = m->checks;
	for(int i=m->p_check;i;i++,ce++)
		yf_state_checkanymapJ(S, ce->map, inst);

	int nc = m->p_cparam;
	fhk_edge *pe = m->params;
	for(int i=0;i<nc;i++,pe++)
		yf_state_checkanymapJ(S, pe->map, inst);
}

/* main solver.
 *
 *                       +-----------------------------[already have chain]-------------------+
 *                       |                                                                    |
 *                       |    +-------------------[cost > beta]---------+                     |
 *                       |    v                                         |                     |
 *                       |  bound <--[cost>beta]-+                      |                     |
 *                       |    |                  |                      |                     |
 * +--[no candidate]----+|    |                  |                      |                     |
 * |                    ||    |                  |                      |                     |
 * |                    ||    v                  |                      |                     v
 * |   solve ------> candidate ------>  (check solver)  ------> (parameter solver) -------> chosen
 * |    ^ ^             ^                    |   ^                   |      ^               | | |
 * |    | |    +--------+                    |   |                   |      |               | | |
 * |    | |    |                             |   |                   |      |               | | |
 * |    | +----|---[computed check]----------+   |                   |      |               | | |
 * |    +------|---[computed parameter]----------|-------------------+      |               | | |
 * |           |                                 |                          |               | | |
 * |           |                          [resume check]           [resume parameter]       | | |
 * |           +-- bound <------+            ^      ^                       ^               | | |
 * |                            |            |      |                       |               | | |
 * +------------------------> failed --------+      |                       +---------------+ | |
 *                                                  +-----------------------------------------+ |
 *                                                                                              |
 *                                                                            return, done. <---+
 *
 * state transition table.
 *
 *                 +---+---+---+---+
 *          reg(.) | X | I | B | C |
 * +---------------+---+---+---+---+
 * | rsolve        | < | < | < | > |          key:
 * +---------------+---+---+---+---+              < input (must be set when jumping here)
 * | solve         | < | < | < | > |              > output (set before jumping out)
 * +---------------+---+---+---+---+              x input+output
 * | chosen        |   |   |   | x |
 * +---------------+---+---+---+---+
 * | failed        |   |   |   | x |
 * +---------------+---+---+---+---+
 * | bound         |   |   |   |   |
 * +---------------+---+---+---+---+
 * | candidate     |   |   |   |   |
 * +---------------+---+---+---+---+
 * | param_s/f     |   |   |   | < |
 * +---------------+---+---+---+---+
 * | check_s/f     |   |   |   | < |
 * +---------------+---+---+---+---+
 *
 * the stack layout is:
 *
 *                    +-----------+-----+-----------+------+
 * ... prev frame ... | selectorN | ... | selector1 | work | ... next frame ...
 *                    +-----------+-----+-----------+------+
 *                                                  ^
 *                                                  |
 *                                                  W
 */
#define reg(name) _reg_##name     // tag for ephemeral variables
#define root(name) _root_##name   // tag for root variables
static void yf_solver_chainV(struct fhk_solver *S, xidx root(X), xinst root(I)){
	/* always valid */
	// beta inverse, (accumulated) cost inverse
	float BI; float CI;
	// work state
	struct fhkX_work *W = (struct fhkX_work *) (S->stack - slots(struct fhkX_work));
	// active candidate
	struct fhk_model *M = NULL;

	/* ephemeral. see state transitions above. */
	xidx reg(X); xidx reg(I);
	float reg(B); float reg(C);

	/* start! */
	reg(X) = root(X);
	reg(I) = root(I);
	reg(B) = FHK_MAX_COST;
	goto solve;

/* save CI and enter solver recursively. */
rsolve:
	W->CI = CI;
	goto solve;

/* push selectors and new work state (see stack layout).
 * W should point to the previous work state. this doesn't have to be valid, it's never accessed.  */
solve:
	{
		xidx idx = reg(X);
		xinst inst = reg(I);
		float beta = reg(B);

		assert(beta >= S->stateV[idx][inst].cost);

		int nm = S->G->vars[idx].n_mod;
		int slot = slotref(W) - S->stack;
		int newslot = slot + slots(struct fhkX_work) + nm*slots(struct fhkX_cselector);
		if(UNLIKELY(newslot + slots(struct fhkX_work) > FHK_MAX_STACK))
			yield_err_depth(S);

		W = (struct fhkX_work *) (S->stack + newslot);
		W->prev = slot;
		W->B = beta;

		trace(ENTERV, slotnum(S, W), fhk_debug_sym(S->G, idx), inst, beta);

		int snum = yf_solver_enterV(S, idx, inst, W);
		if(LIKELY(snum > 0))
			goto candidate;

		reg(C) = INFINITY;
		goto failed;
	}

/* this candidate exceeded bound, try another one */
bound:
	{
		trace(BOUND,
				slotnum(S, W),
				fhk_debug_sym(S->G, W->idx), W->inst,
				fhk_debug_sym(S->G, W->cinfo.idx), W->cinst,
				CI, BI
		);

		fhkX_sp *sp = S->stateM[W->cinfo.idx] + W->cinst;
		sp->cost = costf(M, CI);
		goto candidate;
	}

/* candidate has been chosen, and chain committed to sp.
 * pop state and return to where we left off */
chosen:
	assert(sp_checkC(W->sp->state));
	assert(W->sp->cost <= W->B);

	// read directly from sp here, since W->cinfo might not be written,
	// if we jumped here straight out of the candidate selector.
	// (this only affects debugging, because the next thing we do will be to pop
	// the work stack).
	trace(CHOSEN,
			slotnum(S, W),
			fhk_debug_sym(S->G, W->idx), W->inst,
			fhk_debug_sym(S->G, S->G->vars[W->idx].models[spV_edge(W->sp->state)].idx),
			spV_inst(W->sp->state),
			reg(C), W->B, spV_edge(W->sp->state)
	);

	if(UNLIKELY(W->prev < 0))
		return;

	W = (struct fhkX_work *) (S->stack + W->prev);
	M = &S->G->models[W->cinfo.idx];
	CI = W->CI;
	BI = W->BI;

	// ♪ where the solver at? ♪
	if(LIKELY(where_isP(W->where)))
		goto param_solved;
	else
		goto check_solved;

/* no candidate with cost <= beta.
 * give up and return failure. */
failed:
	W->sp->cost = reg(C);

	// we shouldn't have entered here if the bound was already known
	assert(W->sp->cost > W->B);

	trace(FAILED, slotnum(S, W), fhk_debug_sym(S->G, W->idx), W->inst, reg(C), W->B);

	if(UNLIKELY(W->prev < 0))
		yield_err_chain(S, root(X), root(I)); // noreturn

	W = (struct fhkX_work *) (S->stack + W->prev);
	M = &S->G->models[W->cinfo.idx];

	if(LIKELY(where_isP(W->where))){
		CI = W->CI + reg(C);
		goto bound;
	}else{
		CI = W->CI;
		BI = W->BI;
		goto check_failed;
	}

/* choose a candidate and try to solve the chain recursively */
candidate:

	// ---------------- candidate selection ----------------
	{
		float cost = INFINITY; // low bound
		float beta = W->B;     // high bound for selection
		int32_t inst = 0;      // candidate instance
		struct fhkX_cselector *s = (struct fhkX_cselector *) slotref(W);
		struct fhkX_cselector *cand = NULL;
		int cnum = W->cnum;

		do {
			s--;
			fhkX_sp *sp = s->sp;
			fhkX_iter it = s->it;
			int64_t npk = 0;

			for(;;){
				float scost = sp->cost;
				cand = scost < cost ? s : cand;
				inst = scost < cost ? iter_inst(it) : inst;
				beta = min(beta, max(cost, scost));
				cost = min(cost, scost);

				// the happy path here is that exactly one instance of the model returns
				// our variable, so we check first if there's anything remaining.
				if(LIKELY(!iter0_moreA(it)))
					break;

				it = iter_step(it);
				if(iter_moreI(it)){
					sp++;
					continue;
				}

				it = pkref_iter_next(pkref_nth(s->pk, ++npk));
				sp = S->stateM[s->info.idx] + iter_inst(it);
			}
		} while(--cnum);

		// no candidate
		if(UNLIKELY(cost > beta)){
			reg(C) = cost;
			goto failed;
		}

		xidx idx = cand->info.idx;
		fhkX_sp *sp = S->stateM[idx] + inst;

		// this model already has a chain?
		if(UNLIKELY(sp_checkC(sp->state))){
			// because of speculation we must check for an edge case here:
			// if both of the following conditions hold:
			//     (1) the candidate model has a value
			//     (2) the variable has a speculated value that is not the candidate's
			// then we are in a situation where we have thrown away the candidate's return
			// value, and must switch to the speculated chain.
			// this is not wrong, because a speculated value is only committed if it's
			// better than the already speculated value, so the speculated chain must be
			// at least as good as the candidate.
			// on the other hand, the candidate has a minimum cost, so it's at least as good
			// as the already speculated value, so that they are both equally good, and
			// we can pick whichever one we like.
			uint32_t chain = spV_newchain(inst, cand->info.ei);
			uint32_t value = sp->state & SP_VALUE;
			fhkX_sp *xsp = W->sp;
			// this could probably be branchless, but it's pointless since this
			// edge case will practically never happen (in real world graphs).
			if(UNLIKELY(((xsp->state & (value | ~SP_FLAGS)) ^ chain) > SP_VALUE)){
				// SP_VALUE is set in both sp's, AND the chains don't match.
				// this is our edge case.
				xsp->state |= SP_CHAIN;
			}else{
				// otherwise, one of the following is true:
				//     (1) the candidate model has no value, and therefore it will be computed
				//         and correctly written later
				//     (2) the candidate model has a value and it's the speculated chain
				xsp->state = SP_CHAIN | SP_EXPANDED | value | chain;
			}

			reg(C) = xsp->cost = cost;
			goto chosen;
		}

		M = &S->G->models[idx];
		CI = 0;
		BI = costf_inv(M, beta); // + TODO: tolerance
		assert(BI >= 0);

		W->cinfo = cand->info;
		W->cinst = inst;
		W->BI = BI;

		trace(ENTERM,
				slotnum(S, W),
				fhk_debug_sym(S->G, W->idx), W->inst,
				fhk_debug_sym(S->G, cand->info.idx), inst,
				cost, costf_inv(M, cost),
				beta, BI
		);

		yf_solver_enterM(S, idx, inst);
	}

	// ---------------- checks ----------------
	if(M->p_check != 0){
		fhk_check *edge = M->checks + M->p_check;
		W->where = WHERE_CHECK;

		do {
			fhkX_iter it;
			xidx idx = edge->idx;

			{
				MAP_UNPACK_UNCHECKED(S, edge->map, W->cinst, ss);
				if(0) { empty: continue; }
				if(0) { ident: interval: it = ss; }
				if(0) { complex:
					W->pk = subsetC_pk(ss);
					it = pkref_iter_first(W->pk);
				}
			}

			// this goto-style state machine could be written as nested loops,
			// but, imo, this way is easier to read. fight me.
			int start, block;
			uint64_t *P, *E;
			uint64_t mask;

			yf_state_checkC(S, idx);

/* recompute all state from index and iterator.
 * we will jump here after either starting a new interval, or returning from
 * the recursive solver. this is the "outer" loop. */
check_firstblock:
			start = iter_inst(it);
			block = 64*bitmap_idx64(start);
			P = bitmap_ref64(checkmap_refP(S->stateC[idx])) + 2*bitmap_idx64(start);
			E = bitmap_ref64(checkmap_refE(S->stateC[idx])) + 2*bitmap_idx64(start);
			mask = ~((*P & *E) | bitmapW_ones64(start-block));
			goto check_testmask;

/* "inner" loop inside range */
check_testblock:
			mask = ~(*P & *E);

/* check pass, evaluating the variable if needed */
check_testmask:
			// 0: passed and evaluated
			// 1: either not passed or not evaluated
			if(mask){
				int fail = bitmapW_ffs64(mask);
				int fi = block + fail;

				// the start is masked out, so this holds:
				assert(fi >= start);

				// fast-forward to `fi`.
				// there's 3 possible outcomes here:
				//     (1) `fi` is out of range. we jump to next range (if any).
				//     (2) `fi` is in range and the check fails. we jump to penalty.
				//     (3) `fi` is in range and the check passes. we jump back to `check_firstblock`.
				// in any case, `start` will not be read anymore, so we won't need to update it.
				// thus, inside this block, the invariant `start = iter_inst(it)` will _not_ hold,
				// instead the invariant is `fi = iter_inst(it)`.
				it = iter_stepN(it, fi-start);

				// case (1) ?
				if(!iter_moreI(it))
					goto check_nextrange;

				// case (2) ?
				if(LIKELY(bitmapW_test64(*E, fail)))
					goto check_penalty;

				// check not evaluated.
				// we will now have to do the hard work to find out if it's (2) or (3).
				// before evaluating the check itself, we need to make sure the guarded
				// variable has a value.
				struct fhk_guard *g = &S->G->guards[edge->idx];
				int scanto;

				if(check_isC(edge->flags)){
					// case A: computed variable (the complicated case)
					// we now need to recurse into the solver for the checked variable
					if(UNLIKELY(!S->stateV[g->xi])){
						yf_state_newV(S, g->xi);
						goto check_chain;
					}

					fhkX_sp *sp = S->stateV[g->xi] + fi;

					// not proven to either have a chain or be unsolvable.
					// note: there's no need to worry about it recursing back into this check:
					// if it does, then it will also recurse back to the checked variable
					// and cause the solver to error out.
					// this means we can assume the recursion will not evaluate this check.
					if(!sp_done(*sp)){
check_chain:
						W->edge = edge;
						W->it = it;
						reg(X) = g->xi;
						reg(I) = fi;
						reg(B) = FHK_MAX_COST;
						goto rsolve;

/* solver returned valid chain, evaluate check */
check_solved:
						edge = W->edge;
						idx = edge->idx;
						g = &S->G->guards[idx];
						it = W->it;
						fi = iter_inst(it);
						sp = S->stateV[g->xi] + fi;
						goto check_eval;

/* solver returned no chain, mark it and jump to penalty */
check_failed:
						edge = W->edge;
						fi = iter_inst(W->it);
						fail = fi - 64*bitmap_idx64(fi);
						E = bitmap_ref64(checkmap_refE(S->stateC[edge->idx])) + 2*bitmap_idx64(fi);
						goto check_nochain;
					}

					// unsolvable.
					// only need to toggle the eval bit, pass map is zero initialized
					if(!sp_checkC(sp->state)){
check_nochain:
						*E |= 1LL << fail;
						goto check_penalty;
					}

check_eval:
					if(!sp_checkV(sp->state))
						yf_eval_varV(S, g->xi, fi);

					scanto = check_scan_batchC(S->stateC[idx], S->stateV[g->xi], fi,
							subsetIE_znum(anymapK(S->mapstate[g->group])));
				}else{
					// case B: given variable (simple): no need to recurse here
					yf_state_checkG(S, g->xi);
					yf_eval_checkvarG(S, g->xi, fi);
					scanto = check_scan_batchG(S->stateC[idx], S->stateG[g->xi], fi,
							subsetIE_znum(anymapK(S->mapstate[g->group])));
				}

				yf_check_eval_batch(g, S->stateC[idx], valueV(S->value, g->xi), fi, scanto);

				if(!checkmap_checkP(S->stateC[idx], fi))
					goto check_penalty;

				// check passed, we are in case (3).
				// we have now overwritten all state computed in `check_firstblock`,
				// so the choices are:
				//     (3a) if there's more in this range, jump to `check_firstblock` to restart.
				//     (3b) otherwise, check for next range as normal: entering the new range
				//          recomputes state.

				it = iter_step(it);

				// (3a)
				if(iter_moreI(it))
					goto check_firstblock;

				// (3b)
				goto check_nextrange;
			}

			// fast path: the whole block passed,
			// continue to next block.

			block += 64;
			if(block <= start+iter_remain(it)){
				P++;
				E++;
				goto check_testblock;
			}

			// invariant: `start = iter_inst(it)`
			assert(!iter_moreI(iter_stepN(it, block-start)));

/* advance range */
check_nextrange:
			if(!iter_moreC(it))
				continue; // -> next edge

			W->pk = pkref_next(W->pk);
			it = pkref_iter_next(W->pk);
			goto check_firstblock;

/* check failed */
check_penalty:
			CI += edge->penalty;

			trace(PENALTY,
					slotnum(S, W),
					fhk_debug_sym(S->G, W->idx), W->inst,
					fhk_debug_sym(S->G, W->cinfo.idx), W->cinst,
					fhk_debug_sym(S->G, edge->idx), edge->map,
					edge->penalty,
					CI, BI
			);

			if(CI > BI)
				goto bound;

			// -> next edge

		} while(++edge != M->checks);
	}

	// ---------------- computed parameters ----------------
	if(LIKELY(M->p_cparam != 0)){
		fhk_edge *edge = &M->params[M->p_cparam - 1];
		W->where = WHERE_PARAM;

		do {
			fhkX_iter it;
			W->edge = edge;

			{
				MAP_UNPACK_UNCHECKED(S, edge->map, W->cinst, ss);
				if(0) { empty: continue; }
				if(0) { ident: interval: it = ss; }
				if(0) { complex:
					W->pk = subsetC_pk(ss);
					it = pkref_iter_first(W->pk);
				}
			}

			float ecost = 0;
			yf_state_checkV(S, edge->idx);
			fhkX_sp *spbase = S->stateV[edge->idx];

			for(;;){
				fhkX_sp *sp = spbase + iter_inst(it);

				// sp->cost is always a valid low bound, no matter what the state,
				// and this won't skip cycles because sp->cost is negative
				if(CI + sp->cost > BI){
					assert(sp->cost > ecost);
					CI += sp->cost;

					trace(PARAMB,
							slotnum(S, W),
							fhk_debug_sym(S->G, W->idx), W->inst,
							fhk_debug_sym(S->G, W->cinfo.idx), W->cinst,
							fhk_debug_sym(S->G, edge->idx), edge->map,
							sp->cost
					);

					goto bound;
				}

				if(LIKELY(sp_checkC(sp->state))){
					// fast path: chain solved, cost is true cost
					ecost = max(ecost, sp->cost);
				}else{
					// chain not fully solved, recursion time
					W->ecost = ecost;
					W->it = it;
					reg(X) = edge->idx;
					reg(I) = iter_inst(it);
					reg(B) = BI - CI;
					goto rsolve;

/* chain solved under bound */
param_solved:
					edge = W->edge;
					it = W->it;
					ecost = max(W->ecost, reg(C));
					spbase = S->stateV[edge->idx];
					assert(CI+ecost <= BI);
				}

				ITER_NEXT(it, W->pk, continue, break);
			}

			CI += ecost;
			assert(CI <= BI);

			trace(PARAM,
					slotnum(S, W),
					fhk_debug_sym(S->G, W->idx), W->inst,
					fhk_debug_sym(S->G, W->cinfo.idx), W->cinst,
					fhk_debug_sym(S->G, edge->idx), edge->map,
					ecost,
					CI, BI
			);

		} while(edge-- != M->params);
	}

	/* if we made it this far, we are done.
	 * otherwise, a CI <= BI check should have failed somewhere along the way.  */
	{
		assert(CI <= BI);

		reg(C) = costf(M, CI);

		fhkX_sp *msp = S->stateM[W->cinfo.idx] + W->cinst;
		msp->cost = reg(C);
		msp->state = SP_CHAIN;

		fhkX_sp *xsp = W->sp;

		// if there was a speculated value, this clears it.
		// that's ok because we just solved the model's chain,
		// it couldn't have been executed before, so the speculated
		// value was also wrong.
		xsp->state = SP_CHAIN | SP_EXPANDED | spV_newchain(W->cinst, W->cinfo.ei);
		xsp->cost = reg(C);

		trace(CHAIN,
				slotnum(S, W),
				fhk_debug_sym(S->G, W->idx), W->inst,
				fhk_debug_sym(S->G, W->cinfo.idx), W->cinst,
				CI, BI
		);

		goto chosen;
	}
}
#undef reg
#undef root

/* ---- main loop ---------------------------------------- */

static struct fhkX_bucket *root_find_bucket(struct fhk_solver *S){
	struct fhkX_bucket **prev = &S->root;

	while(*prev){
		struct fhkX_bucket *cur = *prev;
		if(cur->used > 0){
			*prev = cur->next;
			return cur;
		}
		prev = &cur->next;
	}

	return NULL;
}

static void root_bucket_recycle(struct fhk_solver *S, struct fhkX_bucket *bucket){
	bucket->used = 0;
	bucket->next = S->root;
	S->root = bucket;
}

// this is a very naive quicksort, could be a lot faster.
// it doesn't matter, this is not the performance sensitive part.
static void root_list_sort(fhkX_root *roots, int start, int end){
#define swap(a, b) do { typeof(a) _a = (a); (a) = (b); (b) = _a; } while(0)
	if(end-start < 32){
		for(int i=start+1;i<end;i++){
			fhkX_root x = roots[i];
			int j = i;
			for(;j>0;j--){
				if(roots[j-1] <= x) break;
				roots[j] = roots[j-1];
			}
			roots[j] = x;
		}
		return;
	}

	fhkX_root a = roots[start];
	fhkX_root b = roots[(start+end)/2];
	fhkX_root c = roots[end];
	fhkX_root pivot = a < b ? (b < c ? b : a < c ? c : a) : (a < c ? a : b < c ? c : b);

	int i = start-1, j = end+1;
	for(;;){
		for(;;) if(roots[++i] > pivot) break;
		for(;;) if(roots[--j] < pivot) break;
		if(j <= i) break;
		swap(roots[i], roots[j]);
	}

	// tailcall the bigger interval
	if(end-i < j-start){
		swap(start, i);
		swap(end, j);
	}

	root_list_sort(roots, start, j);
	root_list_sort(roots, i, end);

#undef swap
}

static void root_bucket_sort(struct fhkX_bucket *bucket){
	assert(bucket->used > 0);
	root_list_sort(bucket->roots, 0, bucket->used - 1);
}

static void root_bucket_solved(struct fhk_solver *S, struct fhkX_bucket *bucket){
	if(!bucket_checkC(bucket->flags))
		return;

	int num = bucket->used;
	fhkX_root *r = bucket->roots;
	void **p = bucket->p;
	do {
		fhkX_root root = *r++;
		xidx idx = root_idx(root);
		size_t size = S->G->vars[idx].size;
		memcpy(
				p[root_buf(root)],
				valueV(S->value, idx) + size*root_start(root),
				size*root_size(root)
		);
	} while(--num);
}

static void yf_root_bucketG(struct fhk_solver *S, struct fhkX_bucket *bucket){
	int num = bucket->used;
	fhkX_root *r = bucket->roots;
	do {
		fhkX_root root = *r++;
		yf_state_checkG(S, root_idx(root));
		yf_eval_checkintervalG(S, root_idx(root), root_start(root), root_znum(root));
	} while(--num);

	root_bucket_solved(S, bucket);
}

static void yf_root_bucketV(struct fhk_solver *S, struct fhkX_bucket *bucket){
	int num = bucket->used;
	fhkX_root *r = bucket->roots;
	do {
		fhkX_root root = *r++;
		xidx idx = root_idx(root);
		xinst inst = root_start(root);
		int znum = root_znum(root);
		yf_state_checkV(S, idx);
		do {
			fhkX_sp sp = S->stateV[idx][inst];
			if(LIKELY(!sp_done(sp)))
				yf_solver_chainV(S, idx, inst);
			else if(UNLIKELY(!sp_checkC(sp.state)))
				yield_err_chain(S, idx, inst);
			inst++;
		} while(znum--);
	} while(--num);

	num = bucket->used;
	r = bucket->roots;
	do {
		fhkX_root root = *r++;
		xidx idx = root_idx(root);
		xinst inst = root_start(root);
		int znum = root_znum(root);
		do {
			if(LIKELY(!sp_checkV(S->stateV[idx][inst].state)))
				yf_eval_varV(S, idx, inst);
			inst++;
		} while(znum--);
	} while(--num);

	root_bucket_solved(S, bucket);
}

void fhk_yf_solver_main(struct fhk_solver *S){
	for(;;){
		struct fhkX_bucket *bucket = root_find_bucket(S);
		if(!bucket){
			yield_ok(S);
			continue;
		}

		root_bucket_sort(bucket);

		if(UNLIKELY(bucket_checkG(bucket->flags)))
			yf_root_bucketG(S, bucket);
		else
			yf_root_bucketV(S, bucket);

		root_bucket_recycle(S, bucket);
	}
}
