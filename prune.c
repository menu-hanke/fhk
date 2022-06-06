#include "conf.h"
#include "debug.h"
#include "def.h"
#include "mut.h"
#include "prune.h"
#include "trace.h"

#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>

/* ---- heap management ---------------------------------------- */

static int bheap_new(fhkX_href *hp){
	struct fhkX_bheap *H = malloc(bheap_size(FHK_BHEAP_SIZE));
	if(UNLIKELY(!H))
		return 0;
	H->used = 0;
	H->cap = FHK_BHEAP_SIZE;
	*hp = H;
	return 1;
}

static int bheap_insert(fhkX_href *hp, fhkX_bound b){
	assert(prog_isfinite(fu32(b.cost)));
	struct fhkX_bheap *H = *hp;
	if(UNLIKELY(H->used == H->cap)){
		uint32_t cap = 2 * H->cap;
		H = realloc(H, bheap_size(cap));
		if(UNLIKELY(!H))
			return 0;
		H->cap = cap;
		*hp = H;
	}

	size_t idx = ++H->used;
	fhkX_bound *heap = bheap_heap1(H);
	while(idx > 1){
		size_t idxp = idx/2;
		fhkX_bound parent = heap[idxp];
		if(!bound_cmp(b, parent))
			break;
		heap[idx] = parent;
		idx = idxp;
	}

	heap[idx] = b;
	return 1;
}

static fhkX_bound bheap_remove(struct fhkX_bheap *H){
	assert(H->used > 0);
	fhkX_bound *heap = bheap_heap1(H);
	fhkX_bound root = heap[1];
	fhkX_bound e = heap[H->used];
	size_t end = --H->used;
	size_t idx = 1;
	while(2*idx <= end){
		size_t lo = 2*idx;
		if(lo+1 <= end && bound_cmp(heap[lo+1], heap[lo])) lo++;
		if(bound_cmp(e, heap[lo]))
			break;
		heap[idx] = heap[lo];
		idx = lo;
	}
	heap[idx] = e;
	return root;
}

/* ---- pruning ---------------------------------------- */

/* the algorithm:
 * (1) color all variables white, insert given variables into heap with 0 cost
 * (2.1) color all const models (models with 0 parameters) dark gray, insert returns in heap
 * (2.2) color all remaining models white
 * (3) forward prop: repeat until heap is empty
 *     (3.1) pull minimal (var, color, cost) triple from heap
 *     (3.2) if already colored at least as dark, continue -> (3)
 *     (3.3) set cost and color it
 *     (3.4) decrement remaining count of all fwd edges, propagate if 0
 * (4) backprop each pinned variable, color selected nodes black
 * (5) sweep all nodes not colored black
 *
 * colors:
 *     white         no bounds                             (u32)lo>=inf  (u32)hi>=inf
 *     light gray    has lower bound, no upper bound       (u32)lo<inf   (u32)hi<=inf
 *     dark gray     has both bounds                       (u32)lo<inf   (u32)hi<inf
 *     black         keep                                  tagged 'A'
 *
 * v->m forward propagation:
 *     - for low bounds, only propagate builtin maps. usermaps may have empty sets.
 *     - for high bounds, propagate everything.
 *
 * m->v forward propagation:
 *     - for low bounds, always propagate return edges
 *     - for high bounds, only propagate builtin return edges. empty set means no solution.
 *
 * v->m back propagation: pick all models with lo_m < hi_v. if none of them has hi_m = hi_v
 * then pick one (any) model with hi_m = hi_v.
 *
 * m->v back propagation: pick all guards & parameters. return values don't need to be propagated
 * recursively (the variable only needs to be included in the graph for the model returns to make
 * sense. note that this is not required for correctness, but because it's easier to implement
 * rather than special-casing pruned returns, which would still need a retbuf when the model is
 * called.)
 * return values are colored in a separate pass after the recursive backprop.
 *
 * note 1: after step (3) all nodes are colored dark gray, except unreachable cycles.
 * the forward prop gives correct bounds for reachable cycles, so that the backprop doesn't need
 * to care.
 *
 * note 2: starting the backprop from a variable with a finite (low bound) cost will never enter
 * a model (or a variable) with an infinite or unreachable (low bound) cost. this means that
 * finiteness only needs to be checked when entering the pinned variable, not on each recursion.
 */

static fhk_status prune_init_vars(struct fhk_mut_graph *M, fhkX_href *hp){
	struct fhk_mut_var *vm;
	for(fhk_mref vh=M->var; vh; vh=vm->next){
		vm = mrefp(M, vh);
		// mark white
		vm->clo = INFINITY;
		vm->chi = INFINITY;
		if(!vm->back){
			// given variable, put bounds on the heap.
			if(UNLIKELY(!bheap_insert(hp, bound_newL(vh, 0)))) return ecode(MEM);
			if(UNLIKELY(!bheap_insert(hp, bound_newH(vh, 0)))) return ecode(MEM);
			trace(PGIVEN, fhk_mut_debug_sym(M, vh));
		}
	}
	return 0;
}

static fhk_status prune_color_modelL(struct fhk_mut_graph *M, fhkX_href *hp,
		struct fhk_mut_model *mm){

	float cost = 0;
	struct fhk_mut_edge *em;
	for(fhk_mref eh=mm->backV; eh; eh=em->nextM){
		em = mrefp(M, eh);
		if(mhandle_ismapu(em->mapMV))
			continue;
		struct fhk_mut_var *vm = mrefp(M, em->var);
		assert(prog_isfinite(fu32(vm->clo)));
		cost += vm->clo;
	}

	trace(PLMOD, fhk_mut_debug_sym(M, pmref(M, mm)), costf(mm, cost), cost);
	cost = costf(mm, cost);
	mm->clo = cost;

	if(LIKELY(cost < INFINITY)){
		for(fhk_mref eh=mm->fwd; eh; eh=em->nextM){
			em = mrefp(M, eh);
			if(UNLIKELY(!bheap_insert(hp, bound_newL(em->var, cost))))
				return ecode(MEM);
		}
	}

	return 0;
}

static fhk_status prune_color_modelH(struct fhk_mut_graph *M, fhkX_href *hp,
		struct fhk_mut_model *mm){

	float cost = 0;

	struct fhk_mut_check *cm;
	for(fhk_mref ch=mm->backC; ch; ch=cm->nextM){
		cm = mrefp(M, ch);
		cost += cm->penalty;
	}

	struct fhk_mut_edge *em;
	for(fhk_mref eh=mm->backV; eh; eh=em->nextM){
		em = mrefp(M, eh);
		struct fhk_mut_var *vm = mrefp(M, em->var);
		// even for high bounds we will never propagate infinities, so the fact that
		// this function is called means all the variables have finite high bounds.
		// this does _not_ mean that the model itself has a finite high bound, though.
		assert(prog_isfinite(fu32(vm->chi)));
		cost += vm->chi;
	}

	trace(PHMOD, fhk_mut_debug_sym(M, pmref(M, mm)), costf(mm, cost), cost);
	cost = costf(mm, cost);
	mm->chi = cost;

	if(LIKELY(cost < INFINITY)){
		for(fhk_mref eh=mm->fwd; eh; eh=em->nextM){
			em = mrefp(M, eh);
			if(mhandle_ismapu(em->mapMV))
				continue;
			if(UNLIKELY(!bheap_insert(hp, bound_newH(em->var, cost))))
				return ecode(MEM);
		}
	}

	return 0;
}

static fhk_status prune_color_model(struct fhk_mut_graph *M, fhkX_href *hp,
		struct fhk_mut_model *mm, int hi){

	return hi ? prune_color_modelH(M, hp, mm) : prune_color_modelL(M, hp, mm);
}

static fhk_status prune_init_models(struct fhk_mut_graph *M, fhkX_href *hp){
	fhk_status status;
	struct fhk_mut_model *mm;
	for(fhk_mref mh=M->model; mh; mh=mm->next){
		mm = mrefp(M, mh);
		int remlo = 0, remhi = 0;
		struct fhk_mut_edge *em;
		for(fhk_mref eh=mm->backV; eh; eh=em->nextM){
			em = mrefp(M, eh);
			remlo += !mhandle_ismapu(em->mapMV);
			remhi++;
		}
		if(remlo > 0) mm->clo = uf32(-remlo);
		else if(UNLIKELY(status = prune_color_modelL(M, hp, mm))) return status;
		if(remhi > 0) mm->chi = uf32(-remhi);
		else if(UNLIKELY(status = prune_color_modelH(M, hp, mm))) return status;
	}
	return 0;
}

static fhk_status prune_prop_fwd(struct fhk_mut_graph *M, fhkX_href *hp){
	while((*hp)->used){
		fhkX_bound b = bheap_remove(*hp);
		int hi = bound_isH(b.state);
		struct fhk_mut_var *vm = mrefp(M, bound_ref(b.state));
		float *cv = &vm->clo + hi;
		if(prog_isfinite(fu32(*cv)))
			continue;
		*cv = b.cost;
		if(hi) trace(PHVAR, fhk_mut_debug_sym(M, bound_ref(b.state)), b.cost);
		else   trace(PLVAR, fhk_mut_debug_sym(M, bound_ref(b.state)), b.cost);
		struct fhk_mut_edge *em;
		for(fhk_mref eh=vm->fwdM; eh; eh=em->nextV){
			em = mrefp(M, eh);
			if(!hi && mhandle_ismapu(em->mapVM))
				continue;
			struct fhk_mut_model *mm = mrefp(M, em->model);
			float *cm = &mm->clo + hi;
			assert(!prog_isfinite(fu32(*cm)));
			uint32_t rem = fu32(*cm) + 1;
			if(!rem){
				fhk_status status;
				if(UNLIKELY(status = prune_color_model(M, hp, mm, hi)))
					return status;
			}else{
				*cm = uf32(rem);
			}
		}
	}
	return 0;
}

static void prune_markV(struct fhk_mut_graph *M, struct fhk_mut_var *vm);

static void prune_markM(struct fhk_mut_graph *M, struct fhk_mut_model *mm){
	if(mtag_isA(mm->tag))
		return;

	mm->tag |= MTAG_A;

	// low bound may be infinite if this model has to be included to keep an uncomputable variable
	if(!prog_isfinite(fu32(mm->clo))) mm->clo = INFINITY;

	// unprogated (and therefore non-finite) high bound is fine, we normalize it to INFINITY.
	if(!prog_isfinite(fu32(mm->chi))) mm->chi = INFINITY;

	struct fhk_mut_check *cm;
	for(fhk_mref ch=mm->backC; ch; ch=cm->nextM){
		cm = mrefp(M, ch);
		struct fhk_mut_guard *gm = mrefp(M, cm->guard);
		struct fhk_mut_var *vm = mrefp(M, gm->var);
		if(LIKELY(prog_isfinite(fu32(vm->clo)))){
			cm->tag |= MTAG_A;
			gm->tag |= MTAG_A;
			trace(PMGUARD, fhk_mut_debug_sym(M, cm->guard));
			prune_markV(M, vm);
		}else{
			// check will be pruned, so the penalty will always be applied.
			// this is ok, only the high bound matters for correctness.
			mm->clo += cm->penalty;
		}
	}

	assert(mm->clo <= mm->chi);
	trace(PMMOD, fhk_mut_debug_sym(M, pmref(M, mm)), mm->clo, mm->chi);

	struct fhk_mut_edge *em;
	for(fhk_mref eh=mm->backV; eh; eh=em->nextM){
		em = mrefp(M, eh);
		em->tag |= MTAG_A;
		prune_markV(M, mrefp(M, em->var));
	}
}

static void prune_markV(struct fhk_mut_graph *M, struct fhk_mut_var *vm){
	if(mtag_isA(vm->tag))
		return;

	vm->tag |= MTAG_A;
	trace(PMVAR, fhk_mut_debug_sym(M, pmref(M, vm)), vm->clo, vm->chi);

	if(!vm->back)
		return;

	// similarly to models, unprogated high bounds are fine.
	// we don't need to normalize it here, variables only get INFINITY or a finite positive fp.
	assert(prog_isfinite(fu32(vm->chi)) || vm->chi == INFINITY);

	// low bound may be infinite: this means we have to include any model to keep this variable
	// computed. it doesn't matter which one, the algoritm will fail on any of them.
	if(UNLIKELY(!prog_isfinite(vm->clo))){
		struct fhk_mut_edge *em = mrefp(M, vm->back);
		em->tag |= MTAG_A;
		prune_markM(M, mrefp(M, em->model));
		return;
	}

	uint32_t hi = fu32(vm->chi);
	uint32_t beta = ~(uint32_t)0;

	struct fhk_mut_edge *em;
	for(fhk_mref eh=vm->back; eh; eh=em->nextV){
		em = mrefp(M, eh);
		struct fhk_mut_model *mm = mrefp(M, em->model);
		uint32_t mlo = fu32(mm->clo);
		if(mlo < hi){
			em->tag |= MTAG_A;
			prune_markM(M, mm);
			// usermaps don't guarantee a result.
			// this must go after the prune_markM call, because that normalizes the high bound.
			if(!mhandle_ismapu(em->mapVM))
				beta = min(beta, fu32(mm->chi));
		}
	}

	// case 1 - all maps are usermaps: then we have hi=inf, and the previous loop selected all maps.
	// case 2 - let N be the nonempty set of non-usermaps: then we have hi=max(chi(N)).
	// either the previous loop picked a non-usermap model with chi=hi, or there exists such
	// a model in N that the next loop will pick.
	// ---> we don't need to consider usermaps in either case in the next loop.

	if(UNLIKELY(hi < beta)){
		for(fhk_mref eh=vm->back; eh; eh=em->nextV){
			em = mrefp(M, eh);
			struct fhk_mut_model *mm = mrefp(M, em->model);
			if(fu32(mm->chi) == hi && !mhandle_ismapu(em->mapVM)){
				assert(!mtag_isA(em->tag));
				em->tag |= MTAG_A;
				prune_markM(M, mm);
				break;
			}
		}
	}
}

static fhk_status prune_prop_back(struct fhk_mut_graph *M){
	struct fhk_mut_var *vm;
	for(fhk_mref vh=M->var; vh; vh=vm->next){
		vm = mrefp(M, vh);
		if(mtag_ispinned(vm->tag)){
			if(UNLIKELY(!prog_isfinite(fu32(vm->clo))))
				return ecode(CHAIN) | etagA(HANDLE, vh);
			prune_markV(M, vm);
		}
	}
	return 0;
}

static void prune_mark_returns(struct fhk_mut_graph *M){
	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		fhkX_mtag *tag = mrefp(M, ref);
		int t = *tag;
		if(t == MTAG(edgeR)){
			struct fhk_mut_edge *em = mrefp(M, ref);
			struct fhk_mut_var *vm = mrefp(M, em->var);
			struct fhk_mut_model *mm = mrefp(M, em->model);
			if((mm->tag & MTAG_A) && !(vm->tag & MTAG_A))
				trace(PMRET, fhk_mut_debug_sym(M, em->var));
			em->tag |= mm->tag & MTAG_A;
			vm->tag |= mm->tag & MTAG_A;
		}
		ref += mtag_size(t);
	}
}

static void prune_sweep(struct fhk_mut_graph *M){
	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		fhkX_mtag *tag = mrefp(M, ref);
		uint32_t tv = *tag;
		*tag |= mtag_isA(tv) ? 0 : MTAG_PRUNE;
		if(mtag_ispruned(*tag))
			trace(PSWEEP, fhk_mut_debug_sym(M, ref));
		ref += mtag_size(tv);
	}
}

fhk_status fhk_prune(fhk_mut_ref *mp){
	fhkX_href hp;
	if(UNLIKELY(!bheap_new(&hp)))
		return ecode(MEM);

	fhk_status status;
	struct fhk_mut_graph *M = mgraph(mp);
	mgraph_invalidate(M);
	fhk_mut_unflag(M);

	// (1)
	if(UNLIKELY(status = prune_init_vars(M, &hp)))
		goto exit;

	// (2)
	if(UNLIKELY(status = prune_init_models(M, &hp)))
		goto exit;

	// (3)
	if(UNLIKELY(status = prune_prop_fwd(M, &hp)))
		goto exit;

	// (4)
	if(UNLIKELY(status = prune_prop_back(M)))
		goto exit;

	prune_mark_returns(M);
	prune_sweep(M);

exit:
	free(hp);
	return status;
}
