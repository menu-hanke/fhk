#include "co.h"
#include "debug.h"
#include "def.h"
#include "fhk.h"
#include "mem.h"
#include "solve.h"
#include "trace.h"

#include <assert.h>
#include <math.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* ---- flow control ---------------------------------------- */

static void yield_ok(struct fhk_solver *S) {
	trace(YOK);
	fhk_yield(S, 1);
}

static void yield_node(struct fhk_solver *S, int idx, int inst) {
	S->idx = idx;
	S->inst = inst;
	int r = S->G->bn + idx;
	if(idx_isX(idx)) {
		trace(YVAR, r, fhk_debug_sym(S->G, idx), inst);
	} else {
		trace(YMOD, r, fhk_debug_sym(S->G, idx), inst);
	}
	fhk_yield(S, r);
}

static void yield_mapcallK(struct fhk_solver *S, int idx) {
	S->idx = idx;
	int r = S->G->bk + idx;
	trace(YMAPK, r, idx);
	fhk_yield(S, r);
}

static void yield_mapcallI(struct fhk_solver *S, int idx, int inst) {
	S->idx = idx;
	S->inst = inst;
	int r = S->G->bi + idx;
	trace(YMAPI, r, (int8_t)idx, inst);
	fhk_yield(S, r);
}

COLD static void yield_err(struct fhk_solver *S, fhk_status err) {
	trace(YERR);
	S->error = err;
	fhk_yield(S, 0);
}

ERRFUNC static void yield_err_nyi(struct fhk_solver *S) {
	yield_err(S, ecode(NYI));
	UNREACHABLE();
}

ERRFUNC static void yield_err_nomapK(struct fhk_solver *S, xmap map){
	yield_err(S, ecode(NOVALUE) | etagA(MAP, map));
	UNREACHABLE();
}

ERRFUNC static void yield_err_nomapJ(struct fhk_solver *S, xmap map, xinst inst){
	yield_err(S, ecode(NOVALUE) | etagA(MAP, map) | etagB(INST, inst));
	UNREACHABLE();
}

ERRFUNC static void yield_err_novar(struct fhk_solver *S, xidx xi, xinst inst){
	yield_err(S, ecode(NOVALUE) | etagA(NODE, xi) | etagB(INST, inst));
	UNREACHABLE();
}

ERRFUNC static void yield_err_depth(struct fhk_solver *S){
	yield_err(S, ecode(DEPTH));
	UNREACHABLE();
}

ERRFUNC static void yield_err_chain(struct fhk_solver *S, xidx xi, xinst inst){
	yield_err(S, ecode(CHAIN) | etagA(NODE, xi) | etagB(INST, inst));
	UNREACHABLE();
}

/* ---- state management ---------------------------------------- */

/* allocation responsibilities:
 *   +-------------------------------+--------------------+---------------------+
 *   |           edge type           |    anymap/k-map    |   i-map instances   |
 *   +-------------------------------+--------------------+---------------------+
 *   | computed v->m   back (return) |   yf_state_newV    |  yf_solver_enterV   |
 *   +-------------------------------+--------------------+---------------------+
 *   | computed m->v/g back (param)  |   yf_state_newM    |  yf_solver_enterM   |
 *   +-------------------------------+--------------------+---------------------+
 *   | given    m->v   back (param)  | yf_state_newvalueM | yf_eval_checkparam* |
 *   +-------------------------------+--------------------+---------------------+
 *   | computed m->v   fwd  (return) | yf_state_newvalueM |   yf_eval_modcall   |
 *   +-------------------------------+--------------------+---------------------+
 */

// S->mapstate[map] must be allocated before calling this
static void yf_state_mapcallJ(struct fhk_solver *S, xmap map, xinst inst){
	assert(map_isJ(map));
	yield_mapcallI(S, map_sext(map), inst);
	if(UNLIKELY(subset_isU(anymapII(S->map[map], inst))))
		yield_err_nomapJ(S, map, inst);
}

static void yf_state_checkmapJ(struct fhk_solver *S, xmap map, xinst inst) {
	fhkX_anymap am = S->map[map];
	// caller's responsibility to ensure it's allocated.
	assert(!anymap_isU(am));
	if(!subset_isU(anymapII(am, inst)))
		return;
	yf_state_mapcallJ(S, map, inst);
}

static void yf_state_mapcallK(struct fhk_solver *S, xmap map){
	yield_mapcallK(S, map);
	if(UNLIKELY(anymap_isU(S->map[map])))
		yield_err_nomapK(S, map);
}

AINLINE static void yf_state_checkmapK(struct fhk_solver *S, xmap map){
	if(LIKELY(!anymap_isU(S->map[map])))
		return;
	yf_state_mapcallK(S, map);
}

static void yf_state_newmapJ(struct fhk_solver *S, xmap map){
	xgroup group = S->G->mapg[map];
	yf_state_checkmapK(S, group);
	anymapI(S->map[map]) = fhk_mem_newmapI(S, subsetIE_size(anymapK(S->map[group])));
}

static void yf_state_setanymap(struct fhk_solver *S, xmap map){
	assert(map_isK(map) || map_isJ(map)); // do not pass ident here
	if(map_isK(map))
		yf_state_mapcallK(S, map);
	else
		yf_state_newmapJ(S, map);
}

static void yf_state_checkanymap(struct fhk_solver *S, xmap map){
	if(LIKELY(!anymap_isU(S->map[map])))
		return;
	return yf_state_setanymap(S, map);
}

static void yf_state_checkanymapJ(struct fhk_solver *S, xmap map, xinst inst) {
	if(!map_isJ(map))
		return;
	yf_state_checkmapJ(S, map, inst);
}

static fhkX_sp *yf_state_newsp(struct fhk_solver *S, fhkX_sp init, xgroup group){
	yf_state_checkmapK(S, group);
	xinst size = subsetIE_size(anymapK(S->map[group]));
	return fhk_mem_newsp(S, size, init);
}

// note: this does NOT expand forward edges.
// forward edges are expanded by yf_state_newvalueM.
static void yf_state_newM(struct fhk_solver *S, xidx idx){
	struct fhk_model *m = &S->G->models[idx];
	// this must be first since it checks for the group map, which ensures
	// we have the coresponding identity map.
	S->stateM[idx] = yf_state_newsp(S, sp_new(m->exp << SP_EXPANDED_BIT, m->cmin), m->group);
	fhk_check *checks = m->checks;
	int64_t i;
	for(i=m->p_check; i; i++)
		yf_state_checkanymap(S, checks[i].map);
	fhk_edge *params = m->params;
	int nc = m->p_cparam;
	for(i=0; i<nc; i++)
		yf_state_checkanymap(S, params[i].map);
}

AINLINE static void yf_state_checkM(struct fhk_solver *S, xidx idx){
	if(LIKELY(S->stateM[idx]))
		return;
	yf_state_newM(S, idx);
}

static void yf_state_newV(struct fhk_solver *S, xidx idx){
	struct fhk_var *x = &S->G->vars[idx];
	assert(var_isC(x));
	// group must be checked first, see yf_state_newM.
	yf_state_checkmapK(S, x->group);
	int64_t i = 0, nm = x->n_mod;
	fhk_edge *models = x->models;
	uint32_t state = SP_EXPANDED;
	do {
		xmap map = models[i].map;
		state = map_isJ(map) ? 0 : state;
		yf_state_checkanymap(S, map);
	} while(++i < nm);
	S->stateV[idx] = fhk_mem_newsp(S, subsetIE_size(anymapK(S->map[x->group])), sp_new(state, 0));
}

AINLINE static void yf_state_checkV(struct fhk_solver *S, xidx idx){
	if(LIKELY(S->stateV[idx]))
		return;
	yf_state_newV(S, idx);
}

static void yf_state_newG(struct fhk_solver *S, xidx idx){
	xgroup group = S->G->vars[idx].group;
	yf_state_checkmapK(S, group);
	S->stateG[idx] = fhk_mem_newbitmap(S, subsetIE_size(anymapK(S->map[group])));
}

AINLINE static void yf_state_checkG(struct fhk_solver *S, xidx idx){
	if(LIKELY(S->stateG[idx]))
		return;
	yf_state_newG(S, idx);
}

static void yf_state_newC(struct fhk_solver *S, xidx idx){
	xgroup group = S->G->guards[idx].group;
	yf_state_checkmapK(S, group);
	S->stateC[idx] = fhk_mem_newcheckmap(S, subsetIE_size(anymapK(S->map[group])));
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
	valueV(S->value, idx) = fhk_mem_newvalue(S, size, subsetIE_size(anymapK(S->map[group])));
}

AINLINE static void yf_state_checkvalueV(struct fhk_solver *S, xidx idx) {
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
		yf_state_checkanymap(S, re->map);
		re++;
	} while(++i < nr);
	valueM(S->value, idx) = 1;
}

AINLINE static void yf_state_checkvalueM(struct fhk_solver *S, xidx idx){
	if(LIKELY(valueM(S->value, idx)))
		return;
	yf_state_newvalueM(S, idx);
}

/* ---- maps, subset and iterators ---------------------------------------- */

static fhk_subset map_subset_unchecked(struct fhk_solver *S, xmap map, xinst inst) {
	fhkX_anymap am = S->map[map];
	assert(!anymap_isU(am));

	/* branching version: */
	if(map_isI(map)) {
		fhk_subset ss = anymapII(am, inst);
		assert(!subset_isU(ss));
		return ss;
	} else {
		return anymapK(am);
	}

	/* branchless version, with cmov but an extra load for k-maps: */
	// fhk_subset *base = map_isK(map) ? S->map : am;
	// xinst offset = map_isK(map) ? map : inst;
	// assert(!subset_isU(base[offset]));
	// return base[offset];
}

static fhk_subset yf_map_subset_checkedJ(struct fhk_solver *S, xmap map, xinst inst) {
	fhkX_anymap am = S->map[map];
	assert(!anymap_isU(am));
	if(map_isI(map)) {
		fhk_subset ss = anymapII(am, inst);
		if(UNLIKELY(subset_isU(ss))) {
			yf_state_mapcallJ(S, map, inst);
			return anymapII(am, inst);
		} else {
			return ss;
		}
	} else {
		return anymapK(am);
	}
}

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
	yield_node(S, xi, inst);
	if(UNLIKELY(bitmap_is1(S->stateG[xi], inst)))
		yield_err_novar(S, xi, inst);
}

AINLINE static void yf_eval_checkvarG(struct fhk_solver *S, xidx xi, xinst inst){
	if(LIKELY(bitmap_is0(S->stateG[xi], inst)))
		return;
	yf_eval_varG(S, xi, inst);
}

static void yf_eval_varV(struct fhk_solver *S, xidx xi, xinst inst);

static void yf_eval_checkintervalV(struct fhk_solver *S, xidx xi, xinst inst, xinst znum) {
	do {
		assert(sp_checkC(S->stateV[xi][inst].state)); // we come from solver.
		if(!sp_checkV(S->stateV[xi][inst].state))
			yf_eval_varV(S, xi, inst);
		inst++;
	} while(znum--);
}

static void yf_eval_checkparamV(struct fhk_solver *S, xmap map, xidx idx, xinst inst) {
	// unchecked: solver expands computed parameters
	fhk_subset ss = map_subset_unchecked(S, map, inst);
	if(LIKELY(subset_isI(ss))) {
		yf_eval_checkintervalV(S, idx, subsetI_first(ss), subsetIE_znum(ss));
	} else if(!subset_isE(ss)) {
		fhkX_pkref pk = subsetC_pk(ss);
		for(;;) {
			yf_eval_checkintervalV(S, idx, pkref_first(pk), pkref_znum(pk));
			if(!pkref_more(pk)) return;
			pk = pkref_next(pk);
		}
	}
}

// check [start, start+znum]  (inclusive)
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

static void yf_eval_checkparamG(struct fhk_solver *S, xmap map, xidx idx, xinst inst) {
	// checked: solver doesn't expand given edges
	fhk_subset ss = yf_map_subset_checkedJ(S, map, inst);
	if(LIKELY(subset_isI(ss))) {
		yf_eval_checkintervalG(S, idx, subsetI_first(ss), subsetIE_znum(ss));
	} else if(!subset_isE(ss)) {
		fhkX_pkref pk = subsetC_pk(ss);
		for(;;) {
			yf_eval_checkintervalG(S, idx, pkref_first(pk), pkref_znum(pk));
			if(!pkref_more(pk)) return;
			pk = pkref_next(pk);
		}
	}
}

static void eval_put_params(struct fhk_solver *S, xidx idx, xinst inst) {
	struct fhk_graph *G = S->G;
	struct fhk_model *m = &G->models[idx];
	fhk_cedge *ce = S->edges;
	fhk_edge *e = m->params;
	int ne = m->p_param;
	for(int i=0; i<ne; i++, e++) {
		struct fhk_cedge *c = ce + edgeP_order(*e);
		size_t size = G->vars[e->idx].size;
		void *vp = valueV(S->value, e->idx);
		fhk_subset ss = map_subset_unchecked(S, e->map, inst);
		if(LIKELY(subset_isI(ss))) {
			c->p = vp + subsetI_first(ss)*size;
			c->n = subsetIE_size(ss);
		} else if(subset_isE(ss)) {
			c->p = NULL;
			c->n = 0;
		} else {
			struct fhk_mem *mem = mrefp(S, S->mem);
			fhk_mem_align(mem, GUESS_ALIGN(size));
			c->p = mrefp(mem, mem->ptr);
			size_t num = 0;
			fhkX_pkref pk = subsetC_pk(ss);
			for(;;) {
				size_t pos = pkref_first(pk);
				size_t n = pkref_size(pk);
				num += n;
				void *p = mrefp(mem, mem->ptr);
				fhk_mem_bump(mem, size*n);
				fhk_mem_commit(mem);
				memcpy(p, vp + size*pos, size*n);
				if(!pkref_more(pk)) break;
				pk = pkref_next(pk);
			}
			c->n = num;
		}
	}
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

static void *scatter_skipA(struct fhkX_scatter_state *sct, size_t size) {
	sct->mp = ALIGN(sct->mp, GUESS_ALIGN(size));
	void *p = sct->mp;
	sct->mp += size;
	return p;
}

static void scatter_buf(struct fhkX_scatter_state *sct, xinst start, xinst num, fhk_mref off) {
	scatter_prev(sct)->num++;
	struct fhkX_sbuf *b = sct->mp;
	sct->mp += sizeof(struct fhkX_sbuf);
	fhk_mem_commitP(sct->mem, sct->mp);
	b->size = num*sct->size;
	b->vp = sct->vp + start*sct->size;
	b->off = off;
}

static void *scatter_data(struct fhkX_scatter_state *sct, xinst num) {
	sct->mp = ALIGN(sct->mp, GUESS_ALIGN(sct->size));
	void *p = sct->mp;
	scatter_prev(sct)->data = pmref(sct->mem, p);
	sct->mp += num*sct->size;
	fhk_mem_commitP(sct->mem, sct->mp);
	return p;
}

static void eval_start_scatter(struct fhk_solver *S, struct fhkX_scatter_state *sct, xidx idx,
		uint32_t templ) {
	sct->mp = ALIGN(sct->mp, alignof(struct fhkX_scatter));
	struct fhkX_scatter *s = sct->mp;
	sct->mp += sizeof(*s);
	fhk_mem_commitP(sct->mem, sct->mp);
	s->next = 0;
	s->num = 0;
	*sct->prev = pmref(sct->mem, s);
	sct->prev = &s->next;
	sct->idx = idx;
	sct->size = S->G->vars[idx].size;
	sct->vp = pmref(sct->mem, valueV(S->value, idx));
	sct->templ = templ;
}

static void eval_put_scatter(struct fhk_solver *S, struct fhkX_scatter_state *sct, xinst start,
		int znum, xinst pos, float cost) {
	int write = 0;
	xinst inst = start;
	fhkX_sp *sp = S->stateV[sct->idx] + start;
	uint32_t templ = sct->templ;
	for(;;) {
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
		if(LIKELY(!w) || (_vx && eval_replace_speculate(S, sct->idx, state, cost))) {
			write++;
			sp->state = cstate;
		} else if(write > 0) {
			scatter_buf(sct, start, inst-start, pos*sct->size);
			start += write;
			pos += write;
			write = 0;
		} else {
			start++;
			pos++;
		}
		sp++;
		inst++;
		if(!znum--) {
			if(write > 0)
				scatter_buf(sct, start, inst-start, pos*sct->size);
			return;
		}
	}
}

static void eval_put_returns(struct fhk_solver *S, xidx idx, xinst inst,
		struct fhkX_scatter_state *sct) {
	struct fhk_graph *G = S->G;
	struct fhk_mem *mem = mrefp(S, S->mem);
	sct->mem = mem;
	sct->mp = mrefp(mem, mem->ptr);
	sct->next = 0;
	sct->prev = &sct->next;
	uint32_t templ = spV_newchain(inst, 0);
	float cost = S->stateM[idx][inst].cost;
	struct fhk_model *m = &G->models[idx];
	fhk_cedge *ce = S->edges + m->p_param;
	fhk_edge *e = m->returns;
	int ne = m->p_return;
	for(;;) {
		xidx xi = e->idx;
		size_t size = G->vars[xi].size;
		uint32_t etempl = templ | edgeR_reverse(*e);
		fhk_subset ss = map_subset_unchecked(S, e->map, inst);
		// 99.99999% of cases we have a unit return set, so here's a fast path for that.
		// in this case we don't need to consider scatters at all.
		// either we commit the value or throw it away.
		if(LIKELY(subset_is1(ss))) {
			ce->n = 1;
			if(LIKELY(eval_try_put_direct(S, xi, S->stateV[xi]+ss, etempl, cost)))
				ce->p = valueV(S->value, xi) + ss*size;
			else
				ce->p = scatter_skipA(sct, size);
		} else if(subset_isE(ss)) {
			ce->n = 0;
			ce->p = NULL;
		} else if(subset_isI(ss)) {
			xinst start = subsetI_first(ss);
			xinst i = start;
			int num = subsetIE_znum(ss);
			ce->n = num+1;
			ce->p = valueV(S->value, xi) + start*size;
			fhkX_sp *sp = S->stateV[xi] + start;
			for(;;) {
				if(UNLIKELY(!eval_try_put_direct(S, xi, &sp[i], etempl, cost))) {
					// can't write directly, fallback to scatter.
					eval_start_scatter(S, sct, xi, etempl);
					scatter_buf(sct, start, i-start, 0);
					if(num)
						eval_put_scatter(S, sct, i+1, num-1, i-start+1, cost);
					ce->p = scatter_data(sct, ce->n);
					break;
				}
				if(!num--)
					break;
				i++;
			}
		} else {
			xinst num = 0;
			eval_start_scatter(S, sct, xi, etempl);
			fhkX_pkref pk = subsetC_pk(ss);
			for(;;) {
				xinst zn = pkref_znum(pk);
				eval_put_scatter(S, sct, pkref_first(pk), zn, num, cost);
				num += zn+1;
				if(!pkref_more(pk)) break;
				pk = pkref_next(pk);
			}
			ce->n = num;
			ce->p = scatter_data(sct, num);
		}
		if(!--ne)
			break;
		e++;
		ce++;
	}
}

static void eval_write_scatter(struct fhkX_scatter_state *sct) {
	if(LIKELY(!sct->next)) return;
	struct fhk_mem *mem = sct->mem;
	struct fhkX_scatter *s = mrefp(mem, sct->next);
	for(;;) {
		int num = s->num;
		struct fhkX_sbuf *sbuf = s->sbuf;
		void *data = mrefp(mem, s->data);
		for(;;) {
			memcpy(mrefp(mem, sbuf->vp), data+sbuf->off, sbuf->size);
			if(!--num) break;
			sbuf++;
		}
		if(!s->next) return;
		s = mrefp(mem, s->next);
	}
}

static void yf_eval_modcall(struct fhk_solver *S, xidx idx, xinst inst){
	fhkX_sp *sp = S->stateM[idx] + inst;
	assert(!sp_checkV(sp->state));
	sp->state |= SP_VALUE;
	yf_state_checkvalueM(S, idx);
	struct fhk_graph *G = S->G;
	struct fhk_model *m = &G->models[idx];
	fhk_edge *e;
	int ne;
	/* 1: expand forward j-maps if any. there's two reasons to do this here rather than
	 * the return loop below:
	 * (1) 99.9999% cases there's nothing to expand so we get to skip this for free
	 *     and can use the branchless map_subset_unchecked.
	 * (2) we can build the scatter/gather buffers on solver memory without worrying
	 *     about anything allocating since we won't yield until the final modcall. */
	if(UNLIKELY(m->fwdj)) {
		e = m->returns;
		ne = m->p_return;
		do {
			yf_state_checkanymapJ(S, e->map, inst);
			e++;
		} while(--ne);
	}
	/* 2: make sure all parameters have values.
	 * this is the last yield point before MODCALL. */
	e = m->params;
	ne = m->p_cparam;
	for(int i=0; i<ne; i++, e++)
		yf_eval_checkparamV(S, e->map, e->idx, inst);
	int np = m->p_param;
	for(int i=ne; i<np; i++, e++)
		yf_eval_checkparamG(S, e->map, e->idx, inst);
	/* 3: gather parameter edges. */
	fhk_mref ptr = ((struct fhk_mem *) mrefp(S, S->mem))->ptr;
	struct fhk_cedge *ce = fhk_mem_alloc(mrefp(S, S->mem),
			sizeof(fhk_cedge) * (m->p_param+m->p_return), alignof(fhk_cedge));
	S->edges = ce;
	eval_put_params(S, idx, inst);
	/* 4: gather return edges and allocate scatter buffers. */
	struct fhkX_scatter_state sct;
	eval_put_returns(S, idx, inst, &sct);
	/* 5: yield modcall. technically this could call another solver attached to the
	 * same fhk_mem, so we have to check if mem->ptr is bumped during the call. */
	struct fhk_mem *mem = mrefp(S, S->mem);
	mem->ptr = pmref(mem, sct.mp);
	yield_node(S, idx, inst);
	/* 6: write back scatter buffers if we made any. */
	eval_write_scatter(&sct);
	/* 7: pretend we didn't allocate anything. */
	if(LIKELY(mem->ptr == pmref(mem, sct.mp)))
		mem->ptr = ptr;
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
		// are the i-maps.
		// because the sp allocator didn't set SP_EXPANDED, it means that there must be
		// some instance maps to expand.
		int en = nm;
		fhk_edge *e = models;
		do {
			yf_state_checkanymapJ(S, e->map, inst);
			e++;
		} while(--en);
	}
	struct fhkX_cselector *s = W->sel;
	int ei = 0, cnum = 0;
	fhk_edge *e = models;
	do {
		fhkX_iter it;
		xidx idx = e->idx;
		// unchecked: see expand loop above
		fhk_subset ss = map_subset_unchecked(S, e->map, inst);
		if(LIKELY(subset_isI(ss))) {
			it = ss;
		} else if(subset_isE(ss)) {
			goto next;
		} else {
			(s-1)->pk = subsetC_pk(ss);
			it = pkref_iter_first((s-1)->pk);
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
	// work state.
	// W will always point to the start of the current work space,
	// so we will init it below S->work, so that the solver adjust it back to the start
	// before it pushes the first selectors.
	struct fhkX_work *W = mrefp(S, S->work) - sizeof(struct fhkX_work);
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
		// make space for `n_mod` candidates, even though we may not need them all.
		int nm = S->G->vars[idx].n_mod;
		struct fhkX_work *w = ((void *) (W+1)) + nm*sizeof(struct fhkX_cselector);
		if(UNLIKELY(pmref(S, w+1) - S->work) > FHK_WORK_SIZE)
			yield_err_depth(S);
		w->prev = pmref(S, W);
		W = w;
		W->B = beta;
		W->ctol = 0;
		trace(ENTERV, pmref(S,W)-S->work, fhk_debug_sym(S->G, idx), inst, beta);
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
				pmref(S,W)-S->work,
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
	assert(W->sp->cost <= W->B || W->ctol > 0);
	// read directly from sp here, since W->cinfo might not be written,
	// if we jumped here straight out of the candidate selector.
	// (this only affects debugging, because the next thing we do will be to pop
	// the work stack).
	trace(CHOSEN,
			pmref(S,W)-S->work,
			fhk_debug_sym(S->G, W->idx), W->inst,
			fhk_debug_sym(S->G, S->G->vars[W->idx].models[spV_edge(W->sp->state)].idx),
			spV_inst(W->sp->state),
			reg(C), W->B, spV_edge(W->sp->state)
	);
	if(UNLIKELY(W->prev < S->work))
		return;
	W = mrefp(S, W->prev);
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
	trace(FAILED, pmref(S,W)-S->work, fhk_debug_sym(S->G, W->idx), W->inst, reg(C), W->B);
	if(UNLIKELY(W->prev < S->work))
		yield_err_chain(S, root(X), root(I)); // noreturn
	W = mrefp(S, W->prev);
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
		struct fhkX_cselector *s = W->sel;
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
		BI = costf_inv(M, beta); // + TODO: tolerance
		assert(BI >= 0);
		// are we looping?
		// this means CI > BI but costf(CI) < costf(beta) because of fp rounding error.
		if(UNLIKELY(idx == W->cinfo.idx && inst == W->cinst)) {
			assert(CI > BI);
			assert(costf(M, CI) <= beta);
			// epsilon: 0.0009765625 = 1/1024 (arbitrarily chosen).
			W->ctol = W->ctol == 0 ? 0.0009765625 : (W->ctol*2);
			trace(STALL,
					pmref(S,W)-S->work,
					fhk_debug_sym(S->G, W->idx), W->inst,
					fhk_debug_sym(S->G, idx), inst,
					CI,
					BI, W->ctol
			);
			BI += W->ctol;
		}
		CI = 0;
		W->cinfo = cand->info;
		W->cinst = inst;
		W->BI = BI;
		trace(ENTERM,
				pmref(S,W)-S->work,
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
			fhk_subset ss = map_subset_unchecked(S, edge->map, W->cinst);
			if(LIKELY(subset_isI(ss))) {
				it = ss;
			} else if(subset_isE(ss)) {
				continue;
			} else {
				W->pk = subsetC_pk(ss);
				it = pkref_iter_first(W->pk);
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
							subsetIE_znum(anymapK(S->map[g->group])));
				}else{
					// case B: given variable (simple): no need to recurse here
					yf_state_checkG(S, g->xi);
					yf_eval_checkvarG(S, g->xi, fi);
					scanto = check_scan_batchG(S->stateC[idx], S->stateG[g->xi], fi,
							subsetIE_znum(anymapK(S->map[g->group])));
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
					pmref(S,W)-S->work,
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
			fhk_subset ss = map_subset_unchecked(S, edge->map, W->cinst);
			if(LIKELY(subset_isI(ss))) {
				it = ss;
			} else if(subset_isE(ss)) {
				continue;
			} else {
				W->pk = subsetC_pk(ss);
				it = pkref_iter_first(W->pk);
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
							pmref(S,W)-S->work,
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
					if(UNLIKELY(CI+reg(C) > BI)) {
						// parameter was selected over bound because of tolerance.
						// we could just continue here and end up with something reasonable,
						// but we'll restart just so that each tolerance is handled separately,
						// instead of letting them compound.
						// this should almost never happen anyway, so it's not a huge penalty.
						CI += reg(C);
						trace(PARAMX,
								pmref(S,W)-S->work,
								fhk_debug_sym(S->G, W->idx), W->inst,
								fhk_debug_sym(S->G, W->cinfo.idx), W->cinst,
								fhk_debug_sym(S->G, edge->idx), edge->map,
								reg(C)
						);
						goto bound;
					}
				}
				ITER_NEXT(it, W->pk, continue, break);
			}
			CI += ecost;
			assert(CI <= BI);
			trace(PARAM,
					pmref(S,W)-S->work,
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
				pmref(S,W)-S->work,
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
	fhk_mref *prev = &S->bucket;
	while(*prev) {
		struct fhkX_bucket *bucket = mrefp(S, *prev);
		if(bucket->num > 0) {
			*prev = bucket->next;
			return bucket;
		}
		prev = &bucket->next;
	}
	return NULL;
}

static void root_bucket_recycle(struct fhk_solver *S, struct fhkX_bucket *bucket){
	bucket->num = 0;
	bucket->next = S->bucket;
	S->bucket = pmref(S, bucket);
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
	assert(bucket->num > 0);
	root_list_sort(bucket->roots, 0, bucket->num - 1);
}

static void root_bucket_solved(struct fhk_solver *S, struct fhkX_bucket *bucket){
	if(!bucket_checkC(bucket->flags))
		return;
	int num = bucket->num;
	fhkX_root *r = bucket->roots;
	void **p = bucket->ptr;
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
	int num = bucket->num;
	fhkX_root *r = bucket->roots;
	do {
		fhkX_root root = *r++;
		yf_state_checkG(S, root_idx(root));
		yf_eval_checkintervalG(S, root_idx(root), root_start(root), root_znum(root));
	} while(--num);

	root_bucket_solved(S, bucket);
}

static void yf_root_bucketV(struct fhk_solver *S, struct fhkX_bucket *bucket){
	int num = bucket->num;
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
	num = bucket->num;
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
