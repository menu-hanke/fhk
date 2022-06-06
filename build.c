#include "conf.h"
#include "fhk.h"
#include "debug.h"
#include "def.h"
#include "mut.h"
#include "trace.h"

#include <assert.h>
#include <math.h>
#include <stdalign.h>
#include <stdlib.h>
#include <string.h>

/* ---- layouting ---------------------------------------- */

static void layout_link_edge(struct fhk_mut_graph *M, fhk_mref ref){
	struct fhk_mut_edge *edge = mrefp(M, ref);
	struct fhk_mut_var *var = mrefp(M, edge->var);
	struct fhk_mut_model *model = mrefp(M, edge->model);
	assert(!mtag_ispruned(model->tag));
	assert(!mtag_ispruned(var->tag));
	if(mtagTP(edge->tag) == MTAG(edgeP)){
		edge->nextV = var->fwdM;
		edge->nextM = model->backV;
		var->fwdM = ref;
		model->backV = ref;
	}else{
		edge->nextV = var->back;
		edge->nextM = model->fwd;
		var->back = ref;
		model->fwd = ref;
	}
	trace(LINKEDGE, fhk_mut_debug_sym(M, edge->var), fhk_mut_debug_sym(M, edge->model));
}

static void layout_link_check(struct fhk_mut_graph *M, fhk_mref ref){
	struct fhk_mut_check *check = mrefp(M, ref);
	struct fhk_mut_guard *guard = mrefp(M, check->guard);
	struct fhk_mut_model *model = mrefp(M, check->model);
	// merged guard
	if(mtag_isA(guard->tag)){
		assert(mtag_ispruned(guard->tag));
		check->guard = guard->nextV;
		guard = mrefp(M, check->guard);
	}
	assert(!mtag_ispruned(model->tag));
	assert(!mtag_ispruned(guard->tag));
	check->nextG = guard->fwd;
	check->nextM = model->backC;
	guard->fwd = ref;
	model->backC = ref;
	trace(LINKCHK, fhk_mut_debug_sym(M, ref));
}

static void layout_link_var(struct fhk_mut_graph *M, fhk_mref ref){
	struct fhk_mut_var *var = mrefp(M, ref);
	var->next = M->var;
	var->back = 0;
	var->fwdM = 0;
	var->fwdG = 0;
	M->var = ref;
	trace(LINKVAR, fhk_mut_debug_sym(M, ref));
}

static void layout_link_model(struct fhk_mut_graph *M, fhk_mref ref){
	struct fhk_mut_model *model = mrefp(M, ref);
	model->next = M->model;
	model->backV = 0;
	model->backC = 0;
	model->fwd = 0;
	M->model = ref;
	trace(LINKMOD, fhk_mut_debug_sym(M, ref));
}

static void layout_link_guard(struct fhk_mut_graph *M, fhk_mref ref){
	struct fhk_mut_guard *guard = mrefp(M, ref);
	struct fhk_mut_var *var = mrefp(M, guard->var);
	assert(!mtag_ispruned(var->tag));
	// set 'A' iff it's merged.
	guard->tag &= ~MTAG_AB;
	// can we merge it? (XXX: should this be its own pass or part of layouting?)
	if(guard_isset(guard->opcode)){
		struct fhk_mut_guard *gm;
		for(fhk_mref gh=var->fwdG; gh; gh=gm->nextV){
			gm = mrefp(M, gh);
			if(gm->opcode == guard->opcode && gm->arg.u64 == guard->arg.u64){
				// merge into `gm`
				guard->tag |= MTAG_PRUNE | MTAG_A;
				guard->nextV = gh;
				trace(LINKMRG, fhk_mut_debug_sym(M, ref), fhk_mut_debug_sym(M, gh));
				return;
			}
		}
	}
	guard->next = M->guard;
	guard->nextV = var->fwdG;
	guard->fwd = 0;
	M->guard = ref;
	var->fwdG = ref;
	trace(LINKGRD, fhk_mut_debug_sym(M, ref));
}

static void layout_relink(struct fhk_mut_graph *M){
	M->var = 0;
	M->model = 0;
	M->guard = 0;

	fhk_mref ref = MGRAPH_FIRSTOBJ;

	while(ref < M->committed){
		int tag = mref_tag(M, ref);

		switch(mtagTP(tag)){
			case MTAG(edgeP):
			case MTAG(edgeR):
				layout_link_edge(M, ref);
				break;

			case MTAG(check):
				layout_link_check(M, ref);
				break;

			case MTAG(var):
				layout_link_var(M, ref);
				break;

			case MTAG(model):
				layout_link_model(M, ref);
				break;

			case MTAG(guard):
				layout_link_guard(M, ref);
				break;

			default:
				trace(LINKSKIP, fhk_mut_debug_sym(M, ref));
		}

		ref += mtag_size(tag);
	}
}

static fhk_status layout_count(struct fhk_mut_graph *M){
	int num[FHKX_MTAG__max] = { 0 };

	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		fhkX_mtag tag = mref_tag(M, ref);
		num[mtagT(tag)] += mtag_ispruned(tag) ? 0 : 1;
		ref += mtag_size(tag);
	}

	int nv = num[MTAG(var)];
	int nx = nv + num[MTAG(guard)];
	if(UNLIKELY(nx-1 > MAX_IDX)) return ecode(BOUND) | etagA(NODE, nx-1);
	M->nv = nv;
	M->nx = nx;

	int nm = num[MTAG(model)];
	if(UNLIKELY(-nm < MIN_IDX)) return ecode(BOUND) | etagA(NODE, -nm);
	M->nm = nm;

	// return edges have a reverse edge v->m
	M->ne = num[MTAG(edgeP)] + 2*num[MTAG(edgeR)];
	M->nc = num[MTAG(check)];

	return 0;
}

static void layout_order_walkV(struct fhk_mut_graph *M, fhk_mref ref, int *pv, int *pg, int *pm);

static void layout_order_walkM(struct fhk_mut_graph *M, fhk_mref ref, int *pv, int *pg, int *pm){
	struct fhk_mut_model *model = mrefp(M, ref);
	if(mtag_isA(model->tag))
		return;

	model->tag |= MTAG_A;

	struct fhk_mut_check *cm;
	for(fhk_mref ch=model->backC; ch; ch=cm->nextM){
		cm = mrefp(M, ch);
		struct fhk_mut_guard *guard = mrefp(M, cm->guard);
		if(!mtag_isA(guard->tag)){
			guard->tag |= MTAG_A;
			guard->order = (*pg)++;
			trace(OGUARD, guard->order, fhk_mut_debug_sym(M, cm->guard));
		}
	}

	for(fhk_mref ch=model->backC; ch; ch=cm->nextM){
		cm = mrefp(M, ch);
		struct fhk_mut_guard *guard = mrefp(M, cm->guard);
		layout_order_walkV(M, guard->var, pv, pg, pm);
	}

	struct fhk_mut_edge *em;
	for(fhk_mref eh=model->backV; eh; eh=em->nextM){
		em = mrefp(M, eh);
		layout_order_walkV(M, em->var, pv, pg, pm);
	}
}

static void layout_order_walkV(struct fhk_mut_graph *M, fhk_mref ref, int *pv, int *pg, int *pm){
	struct fhk_mut_var *var = mrefp(M, ref);
	if(mtag_isA(var->tag))
		return;

	var->tag |= MTAG_A;

	struct fhk_mut_edge *em;
	for(fhk_mref eh=var->back; eh; eh=em->nextV){
		em = mrefp(M, eh);
		struct fhk_mut_model *model = mrefp(M, em->model);
		if(!mtag_isB(model->tag)){
			model->tag |= MTAG_B;
			model->order = (*pm)++;
			trace(OMODEL, model->order, fhk_mut_debug_sym(M, em->model));
		}
	}

	for(fhk_mref eh=var->back; eh; eh=em->nextV){
		em = mrefp(M, eh);
		layout_order_walkM(M, em->model, pv, pg, pm);
	}

	var->order = (*pv)++;
	trace(OVAR, var->order, fhk_mut_debug_sym(M, ref));
}

static void layout_order(struct fhk_mut_graph *M){
	fhk_mut_unflag(M);

	int pv = 0, pg = M->nv, pm = -M->nm;

	// tagging in layout_order_* functions:
	//              +----------+--------+
	//              |    A     |   B    |
	// +------------+----------+--------+
	// | var        | visited  |        |
	// +------------+   and    |        |
	// | guard      | has id   |        |
	// +------------+----------+--------+
	// | model      | visited  | has id |
	// +------------+----------+--------+

	// step 1. special cases:
	// * given variables go first.
	// * we will put models without any returns last. this doesn't matter much because the solver
	//   never calls them, but it's a case we must handle. note that if a prune step is run,
	//   there won't be any of these in the graph.
	// * we will put guards without any models first. it doesn't matter where we put them,
	//   and there won't be any in a pruned graph.
	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		int tag = mref_tag(M, ref);
		switch(mtagTP(tag)){
			case MTAG(var):
			{
				struct fhk_mut_var *var = mrefp(M, ref);
				if(!var->back){
					var->order = pv++;
					var->tag |= MTAG_A;
					trace(OGIVEN, var->order, fhk_mut_debug_sym(M, ref));
				}
				break;
			}

			case MTAG(model):
			{
				struct fhk_mut_model *model = mrefp(M, ref);
				if(UNLIKELY(!model->fwd)){
					model->order = pm++;
					model->tag |= MTAG_AB;
					trace(OMODEL, model->order, fhk_mut_debug_sym(M, ref));
				}
				break;
			}

			case MTAG(guard):
			{
				struct fhk_mut_guard *guard = mrefp(M, ref);
				if(UNLIKELY(!guard->fwd)){
					guard->order = pg++;
					guard->tag |= MTAG_A;
					trace(OGUARD, guard->order, fhk_mut_debug_sym(M, ref));
				}
				break;
			}
		}
		ref += mtag_size(tag);
	}

	M->nz = pv;

	// step 2. make a topological sort of the rest.
	// we sort variables in depth-first order and models in breadth-first order.
	// this makes the solver have shallower chains as well as have related models
	// next to each other in memory. we don't care about cycles (a topological sort
	// doesn't even make sense in a cyclic graph). if we have cycles we will get
	// some "good enough" approximation.
	//
	// TODO: this doesn't sort edges in the corresponding order. for v->m edges this doesn't
	// matter, since the solver iterates them in an arbitrary order anyway, but for
	// m->v edges fixing the order could be a good idea here.
	ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		int tag = mref_tag(M, ref);
		if((tag & ~MTAG_PIN) == MTAG(var))
			layout_order_walkV(M, ref, &pv, &pg, &pm);
		ref += mtag_size(tag);
	}

	assert(pv == M->nv && pg == M->nx && pm == 0);
}

static void layout_bias(struct fhk_mut_graph *M) {
	M->bn = 2 + M->nm;
	M->bk = M->bn + M->nz;
	M->bi = M->bk + M->nk + M->ni;
}

static fhk_status layout_maps(struct fhk_mut_graph *M){
	if(M->maptable)
		free(M->maptable);

	int nmap = M->c_group + M->c_mapK + M->c_mapI;
	M->maptable = malloc(nmap);
	memset(M->maptable, 0, nmap);

	fhkP_smap *mtab = M->maptable + M->c_mapI;
	int cg = M->c_group;
	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		fhkX_mtag tag = mref_tag(M, ref);

		switch(mtagTP(tag)){
			// m->v is used for evaluation.
			// v->m is used for candidate selection.
			case MTAG(edgeR):
			{
				struct fhk_mut_edge *edge = mrefp(M, ref);
				if(mhandle_ismapu(edge->mapMV)){
					mtab[mhandleV(edge->mapMV) + (mhandle_ismapL(edge->mapMV) ? cg : 0)] = 1;
					mtab[mhandleV(edge->mapVM) + (mhandle_ismapL(edge->mapVM) ? cg : 0)] = 1;
				}
				break;
			}

			// m->v is used for evaluation & solving.
			// v->m is unused.
			case MTAG(edgeP):
			case MTAG(check):
			{
				fhk_mhandle map = ((struct fhk_mut_edge *) mrefp(M, ref))->mapMV;
				if(mhandle_ismapu(map))
					mtab[mhandleV(map) + (mhandle_ismapL(map) ? cg : 0)] = 1;
				break;
			}

			case MTAG(var):
			case MTAG(model):
			{
				int gid = ((struct fhk_mut_var *) mrefp(M, ref))->gid;
				mtab[gid] = 1;
				break;
			}
		}

		ref += mtag_size(tag);
	}

	int ni = 1, nk = 0, ng = 0;
	fhkP_smap *p = M->maptable;

	for(int i=0;i<M->c_mapI;i++,p++){
		ni += *p;
		if(*p) trace(OMAP, 'i', ~i, -ni);
		else   trace(OSKIPMAP, 'i', ~i);
		*p = *p ? -ni : 0;
	}

	for(int i=0;i<M->c_group;i++,p++){
		int flag = *p;
		if(flag) trace(OMAP, 'g', i, nk);
		else     trace(OSKIPMAP, 'g', i);
		*p = flag ? nk : ~0;
		nk += flag;
		ng += flag;
	}

	for(int i=0;i<M->c_mapK;i++,p++){
		int flag = *p;
		if(flag) trace(OMAP, 'k', i, nk);
		else     trace(OSKIPMAP, 'k', i);
		*p = flag ? nk : ~0;
		nk += flag;
	}

	if(UNLIKELY(-ni < MIN_MAPI))   return ecode(BOUND) | etagA(MAP, -ni);
	if(UNLIKELY(nk-1 > MAX_MAPK))  return ecode(BOUND) | etagA(MAP, nk-1);

	M->ni = ni;
	M->nk = nk;
	M->ng = ng;

	return 0;
}

static int layout_relocate_map(struct fhk_mut_graph *M, fhk_mhandle map){
	if(mhandle_isident(map))
		return MAP_IDENT;
	fhkP_smap *mtab = mgraph_maptable(M);
	return mtab[mhandleV(map) + (mhandle_ismapL(map) ? M->c_group : 0)];
}

static size_t layout_size(struct fhk_mut_graph *M){
	size_t size = sizeof(struct fhk_graph)
		+ M->nm * sizeof(struct fhk_model)
		+ M->nx * sizeof(struct fhk_var) // this includes guards
		+ M->ne * sizeof(fhk_edge)
		+ M->nc * sizeof(fhk_check)
		+ (M->ni-1) * sizeof(fhkP_group);

#if FHK_DSYM
	if(M->dsym){
		size = ALIGN(size, alignof(*M->dsym));
		size += dsym_tabsize(M->dsym);
	}
#endif

	return size;
}

static fhk_query layout_query_ref(struct fhk_mut_graph *M, fhk_mref ref) {
	switch(mtagTP(mref_tag(M, ref))) {
		case MTAG(edgeP):
		case MTAG(edgeR):
		case MTAG(check):
			// edge reordering is not saved, so it's just included/pruned.
			return QUERY_INCLUDE;
		case MTAG(var):
		{
			struct fhk_mut_var *x = mrefp(M, ref);
			return query_new(x->order, x->back ? 0 : M->bn+x->order);
		}
		case MTAG(model):
		{
			int idx = ((struct fhk_mut_model *) mrefp(M, ref))->order;
			return query_new(idx, M->bn+idx);
		}
		case MTAG(guard):
			return query_idx(((struct fhk_mut_guard *)mrefp(M, ref))->order);
	}
	return QUERY_PRUNED;
}

static fhk_query layout_query_map(struct fhk_mut_graph *M, fhk_mhandle mapH) {
	if(mhandle_isident(mapH))
		return query_idx(MAP_IDENT);
	fhkP_smap *maptab = mgraph_maptable(M);
	if(mhandle_isgroup(mapH)) {
		int idx = maptab[mhandleU(mapH)];
		if(idx >= 0) return query_new(idx, M->bk+idx);
	} else if(mhandle_ismapL(mapH)) {
		int idx = maptab[M->c_group + mhandleU(mapH)];
		if(idx >= 0) return query_new(idx, M->bk+idx);
	} else if(mhandle_ismapJ(mapH)) {
		int idx = maptab[mhandleV(mapH)];
		if(idx < 0) return query_new(idx, M->bi+idx);
	}
	return QUERY_PRUNED;
}

fhk_query fhk_mut_query(fhk_mut_ref *mp, fhk_mhandle handle) {
	struct fhk_mut_graph *M = mgraph(mp);
	if(LIKELY(M->layout_valid)) {
		if(mhandle_isref(handle))
			return layout_query_ref(M, handle);
		if(mhandle_ismap(handle))
			return layout_query_map(M, handle);
	}
	return QUERY_PRUNED;
}

int fhk_mut_size(fhk_mut_ref *mp){
	struct fhk_mut_graph *M = mgraph(mp);
	return LIKELY(M->layout_valid) ? layout_size(M) : 0;
}

fhk_status fhk_mut_layout(fhk_mut_ref *mp){
	// the order of passes matters here.
	// each pass depends on the results of the previous pass(es).
	struct fhk_mut_graph *M = mgraph(mp);
	fhk_status s;
	layout_relink(M);
	if(UNLIKELY((s = layout_count(M)))) return s;
	layout_order(M);
	if(UNLIKELY((s = layout_maps(M)))) return s;
	layout_bias(M);
	M->layout_valid = 1;
	return 0;
}

/* ---- building ---------------------------------------- */

static void build_base(struct fhk_mut_graph *M, struct fhk_graph *G){
	G->bn = M->bn;
	G->bk = M->bk;
	G->bi = M->bi;
	G->nz = M->nz;
	G->nv = M->nv;
	G->nx = M->nx;
	G->nm = M->nm;
	G->ng = M->ng;
	G->nk = M->nk;
	G->ni = M->ni;
}

static fhk_status build_models(struct fhk_mut_graph *M, struct fhk_graph *G){
	// pruned checks act as if the variable was never computable.
	// they will not be included in the graph, so we add the penalties directly
	// into the cost parameters here.

	for(int64_t i=0;i<G->nm;i++)
		G->models[~i].k = 0;

	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		int tag = mref_tag(M, ref);
		if(mtagTP(tag) == (MTAG_PRUNE|MTAG(check))){
			struct fhk_mut_check *cm = mrefp(M, ref);
			struct fhk_mut_model *mm = mrefp(M, cm->model);
			if(!mtag_ispruned(mm->tag))
				G->models[mm->order].k += cm->penalty;
		}
		ref += mtag_size(tag);
	}

	// now we can build the models.
	// the order matters here because of the inverse computation.

	fhkP_smap *map = mgraph_maptable(M);
	struct fhk_mut_model *mm;
	for(fhk_mref mh=M->model; mh; mh=mm->next){
		mm = mrefp(M, mh);
		if(mtag_ispruned(mm->tag))
			continue;
		if(UNLIKELY(!cost_isset(mm->k) || !cost_isset(mm->c)))
			return ecode(UNSET) | etagA(HANDLE, mh);
		struct fhk_model *mg = G->models + mm->order;
		mg->group = map[mm->gid];
		mg->k += mm->k;
		mg->c = mm->c;
		mg->ki = -mg->k/mg->c;
		mg->ci = 1/mg->c;
		mg->cmin = mm->clo;
		mg->dsym = mm->dsym;
		mg->exp = 1; // edge builder will toggle off
		mg->fwdj = 0; // edge builder will toggle on
	}

	return 0;
}

static fhk_status build_vars(struct fhk_mut_graph *M, struct fhk_graph *G){
	fhkP_smap *map = mgraph_maptable(M);
	struct fhk_mut_var *vm;
	for(fhk_mref vh=M->var; vh; vh=vm->next){
		vm = mrefp(M, vh);
		if(mtag_ispruned(vm->tag))
			continue;
		if(UNLIKELY(!size_isset(vm->size))) return ecode(UNSET) | etagA(HANDLE, vh);
		struct fhk_var *vg = G->vars + vm->order;
		vg->group = map[vm->gid];
		vg->size = vm->size;
		vg->dsym = vm->dsym;
	}
	return 0;
}

static fhk_status build_guards(struct fhk_mut_graph *M, struct fhk_graph *G){
	fhkP_smap *map = mgraph_maptable(M);
	struct fhk_mut_guard *gm;
	for(fhk_mref gh=M->guard; gh; gh=gm->next){
		gm = mrefp(M, gh);
		if(mtag_ispruned(gm->tag))
			continue;
		if(UNLIKELY(!guard_isset(gm->opcode))) return ecode(UNSET) | etagA(HANDLE, gh);
		struct fhk_guard *gg = G->guards + gm->order;
		struct fhk_mut_var *vm = mrefp(M, gm->var);
		gg->xi = vm->order;
		gg->group = map[vm->gid];
		gg->opcode = gm->opcode;
		gg->dsym = gm->dsym;
		gg->arg = gm->arg;
	}
	return 0;
}

static fhk_status build_back_edgesM(struct fhk_mut_graph *M, fhk_mref modelH,
		struct fhk_model *mg, void **bp){

	struct fhk_mut_model *mm = mrefp(M, modelH);

	struct fhk_mut_check *cm;
	int nc = 0;
	for(fhk_mref ch=mm->backC; ch; ch=cm->nextM){
		cm = mrefp(M, ch);
		fhk_check *cg = *bp;
		*bp += sizeof(*cg);

		struct fhk_mut_guard *gm = mrefp(M, cm->guard);
		struct fhk_mut_var *vm = mrefp(M, gm->var);

		cg->idx = gm->order;
		cg->map = layout_relocate_map(M, cm->mapMG);
		cg->flags = vm->back ? CHECK_COMPUTED : 0;
		cg->penalty = cm->penalty;
		if(mhandle_ismapJ(cm->mapMG))
			mg->exp = 0;

		nc++;
	}

	if(UNLIKELY(nc-1 > MAX_CHECK)) return ecode(BOUND) | etagA(EDGE, nc-1);
	mg->p_check = -nc;
	mg->params = *bp;

	// reorder checks.
	// not required for correctness, but putting expensive checks first helps the solver
	// fail faster.
	fhk_check *checks = mg->checks - nc;
	for(int i=1;i<nc;i++){
		fhk_check c = checks[i];
		int j = i;
		for(; j>0; j--){
			if(checks[j-1].penalty >= c.penalty) break;
			checks[j] = checks[j-1];
		}
		checks[j] = c;
	}

	uint32_t order[MAX_PARAM];

	struct fhk_mut_edge *pm;
	int np = 0, ncp = 0;
	for(fhk_mref ph=mm->backV; ph; ph=pm->nextM){
		if(UNLIKELY(np > MAX_PARAM)) return ecode(BOUND) | etagA(EDGE, np);

		pm = mrefp(M, ph);
		fhk_edge *pg = *bp;
		*bp += sizeof(*pg);

		struct fhk_mut_var *vm = mrefp(M, pm->var);
		pg->idx = vm->order;
		pg->map = layout_relocate_map(M, pm->mapMV);
		order[np] = vm->back ? fu32(vm->chi - vm->clo) : ~(uint32_t)0;
		ncp += !!vm->back;
		np++;
		pg->ex = -np;
		if(mhandle_ismapJ(pm->mapMV))
			mg->exp = 0;
	}

	// the parameter linked list is initially in reverse order. this fixes the indexing.
	for(int i=0;i<np;i++)
		mg->params[i].ex += np;

	mg->p_param = np;
	mg->p_cparam = ncp;

	// reorder edges.
	// placing computed edges before given edges is required for correctness.
	// the internal order between computed & given edges is arbitrary,
	// so here we choose to put the computed edges in order of max possible
	// cost increase, to hopefully make the solver fail fast.
	fhk_edge *params = mg->params;
	for(int i=1;i<np;i++){
		uint32_t v = order[i];
		fhk_edge p = params[i];
		int j = i;
		for(; j>0; j--){
			if(order[j-1] <= v) break;
			order[j] = order[j-1];
			params[j] = params[j-1];
		}
		order[j] = v;
		params[j] = p;
	}

	return 0;
}

static fhk_status build_check_back_edgesM(struct fhk_mut_graph *M, fhk_mref modelH,
		struct fhk_model *mg, void **bp){

	return mg->params ? 0 : build_back_edgesM(M, modelH, mg, bp);
}

static fhk_status build_back_edgesV(struct fhk_mut_graph *M, struct fhk_graph *G, fhk_mref varH,
		struct fhk_var *vg, void **bp){

	struct fhk_mut_var *vm = mrefp(M, varH);
	vg->models = *bp;
	int nm = 0;

	struct fhk_mut_edge *em;
	for(fhk_mref eh=vm->back; eh; eh=em->nextV){
		em = mrefp(M, eh);
		fhk_edge *e = *bp;
		*bp += sizeof(*e);

		e->idx = ((struct fhk_mut_model *) mrefp(M, em->model))->order;
		e->map = layout_relocate_map(M, em->mapVM);
		e->ex = ~0; // unused for v->m back edges

		nm++;
	}

	if(UNLIKELY(nm-1 > MAX_MOD)) return ecode(BOUND) | etagA(EDGE, nm-1);
	vg->n_mod = nm;

	fhk_status status;
	fhk_edge *e = vg->models;

	for(fhk_mref eh=vm->back; eh; eh=em->nextV, e++){
		em = mrefp(M, eh);
		struct fhk_model *m = G->models + e->idx;
		if(UNLIKELY((status = build_check_back_edgesM(M, em->model, m, bp))))
			return status;
	}

	return 0;
}

static fhk_status build_back_edges(struct fhk_mut_graph *M, struct fhk_graph *G, void **bp){
	fhk_mref *orderv = NULL;

	// we will build the edges in topological order,
	// this buffer is for collecting the topo order.
	orderv = malloc(M->nv * sizeof(*orderv));
	if(UNLIKELY(!orderv)) return ecode(MEM);

	struct fhk_mut_var *vm;
	for(fhk_mref vh=M->var; vh; vh=vm->next){
		vm = mrefp(M, vh);
		orderv[vm->order] = vh;
	}

	fhk_status status = 0;

	// this will construct every reachable model back-edge as well.
	for(int i=0;i<M->nv;i++)
		if(UNLIKELY((status = build_back_edgesV(M, G, orderv[i], G->vars+i, bp))))
			break;

	free(orderv);
	return status;
}

static fhk_status build_fwd_edges(struct fhk_mut_graph *M, struct fhk_graph *G, void **bp){
	// first just allocate the edge list pointers.
	// we can't yet build the actual edges here, because they are in reverse order.
	struct fhk_mut_model *mm;
	for(fhk_mref mh=M->model; mh; mh=mm->next){
		mm = mrefp(M, mh);
		struct fhk_model *mg = G->models + mm->order;
		mg->returns = *bp;
		mg->p_return = 0;
		int nr = 0;
		struct fhk_mut_edge *rm;
		for(fhk_mref rh=mm->fwd; rh; rh=rm->nextM){
			rm = mrefp(M, rh);
			nr++;
		}
		if(UNLIKELY(nr-1 > MAX_RETURN)) return ecode(BOUND) | etagA(EDGE, nr-1);
		*bp += nr * sizeof(fhk_edge);
	}

	// `n_mod` will be a running counter
	for(int i=0;i<G->nv;i++)
		G->vars[i].n_mod = 0;

	// build the actual edges in chrono order.
	// NOTE: this step assumes that the reverse edges are in reverse chrono order
	//       (ie. the link list order).
	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->committed){
		int tag = mref_tag(M, ref);
		if(mtagTP(tag) == MTAG(edgeR)){
			struct fhk_mut_edge *me = mrefp(M, ref);
			struct fhk_mut_model *mm = mrefp(M, me->model);
			struct fhk_mut_var *vm = mrefp(M, me->var);
			struct fhk_model *mg = G->models + mm->order;
			struct fhk_var *vg = G->vars + vm->order;
			fhk_edge *e = mg->returns + mg->p_return;
			mg->p_return++;
			vg->n_mod++;
			e->idx = vm->order;
			e->map = layout_relocate_map(M, me->mapMV);
			e->ex = -vg->n_mod;
			if(mhandle_ismapJ(me->mapMV))
				mg->fwdj = 1;
		}
		ref += mtag_size(tag);
	}

	// fixup return edges so that the reverses are in reverse order.
	for(int i=0;i<G->nm;i++){
		struct fhk_model *m = G->models + ~i;
		for(int j=0;j<m->p_return;j++){
			fhk_edge *e = m->returns + j;
			struct fhk_var *v = G->vars + e->idx;
			e->ex += v->n_mod;
		}
	}

	return 0;
}

static fhk_status build_edges(struct fhk_mut_graph *M, struct fhk_graph *G, void *buf){
	/* strategy:
	 *
	 * [var1 back-edges] [model1 of var1 back-edges] ... [modelN1 of var1 back-edges]
	 * .
	 * .
	 * .
	 * [varM back-edges] [model1 of varM back-edges] ... [modelNM of varM back-edges]
	 * [model1 return-edges]
	 * .
	 * .
	 * .
	 * [modelL return-edges]
	 */

	for(int i=0;i<G->nm;i++){
		struct fhk_model *m = G->models + ~i;
		m->params = NULL; // this will mark if the back edges exist yet
	}

	fhk_status status;
	if(UNLIKELY((status = build_back_edges(M, G, &buf)))) return status;
	if(UNLIKELY((status = build_fwd_edges(M, G, &buf)))) return status;

	return 0;
}

static fhk_status build_associate_map(struct fhk_mut_graph *M, fhkP_group *assoc, fhk_mhandle mapH,
		fhk_mref source){
	fhkP_smap *mtab = mgraph_maptable(M);
	int map = mtab[mhandleV(mapH)];
	int group = mtab[mrefVM_gid(M, source)];
	fhkP_group *ap = &assoc[map_zext(map)];
	if(group_isvalid(*ap) && UNLIKELY(*ap != group))
		return ecode(MAPASSOC) | etagA(MAP, map) | etagB(GROUP, group);
	*ap = group;
	return 0;
}

static fhk_status build_maps(struct fhk_mut_graph *M, struct fhk_graph *G, void *buf){
	// associate each j-map to a source group.
	// the only reason this is done is to know the size of the mapstate to allocate.
	// possible j-map evaluations:
	//     (1) parameter   m->v   model group is source
	//     (2) return      m->v   model group is source
	//     (3) return      v->m   var group is source     (reverse edge)
	// the check<->var is edge is (implicit) ident, so only m<->v edges need to be checked.
	memset(buf, GROUP_INVALID, M->ni-1);
	// ident (-1 = 255) will never be used as an index,
	// -2 is the first valid one and -ni is the last one.
	// ie: the valid incides are (inlusive): [256-ni..254]
	fhkP_group *assoc = buf + M->ni - 256;
	G->mapg = assoc;
	fhk_status status;
	fhk_mref ref = MGRAPH_FIRSTOBJ;
	while(ref < M->used){
		fhkX_mtag tag = mref_tag(M, ref);
		if(mtagT_isedge(mtagTP(tag))){
			struct fhk_mut_edge *e = mrefp(M, ref);
			// (1) & (2)
			if(mhandle_ismapJ(e->mapMV)
					&& UNLIKELY((status = build_associate_map(M, assoc, e->mapMV, e->model))))
				return status;
			// (3)
			if(mtagTP(tag) == MTAG(edgeR)
					&& mhandle_ismapJ(e->mapVM)
					&& UNLIKELY((status = build_associate_map(M, assoc, e->mapVM, e->var))))
				return status;
		}
		ref += mtag_size(tag);
	}
	return 0;
}

fhk_status fhk_mut_build(fhk_mut_ref *mp, void *buf){
	struct fhk_mut_graph *M = mgraph(mp);
	if(UNLIKELY(!M->layout_valid)) return ecode(NOLAYOUT);

	fhk_status status;
	void *ownbuf = NULL;

	if(!buf){
		ownbuf = buf = malloc(layout_size(M));
		if(UNLIKELY(!buf)) return ecode(MEM);
	}

	buf += M->nm*sizeof(struct fhk_model);
	struct fhk_graph *G = buf;
	build_base(M, G);
	if(UNLIKELY(status = build_models(M, G))) goto fail;
	if(UNLIKELY(status = build_vars(M, G))) goto fail;
	if(UNLIKELY(status = build_guards(M, G))) goto fail;

	buf += sizeof(struct fhk_graph) + M->nx*sizeof(struct fhk_var);
	if(UNLIKELY(status = build_edges(M, G, buf))) goto fail;

	buf += M->nc*sizeof(fhk_check) + M->ne*sizeof(fhk_edge);
	if(UNLIKELY((status = build_maps(M, G, buf)))) goto fail;

#if FHK_DSYM
	buf += (M->ni-1)*sizeof(fhkP_group);
	if(M->dsym){
		buf = (void *) ALIGN((intptr_t)buf, alignof(*M->dsym));
		memcpy(buf, M->dsym, dsym_tabsize(M->dsym));
		G->dsym = buf;
	}else{
		G->dsym = DSYM_NONE;
	}
#endif

	return (fhk_status) G;

fail:
	if(ownbuf)
		free(ownbuf);
	return status;
}

/* ---- input validation ---------------------------------------- */

// note: the assert* macros are evil: they may return

#define handle_assertref(M, h, t) ({ \
		fhk_mhandle _h = (h); \
		if(UNLIKELY(!mhandle_isref(h))) return ecode(INVAL); \
		fhkX_mtag *tag = mrefp((M), _h); \
		if(UNLIKELY(mtagTP(*tag) != (t))) return ecode(INVAL); \
		(void *) tag; \
	})

/* ---- buffer management ---------------------------------------- */

static fhk_mref mgraph_alloc(fhk_mut_ref *mp, fhk_mref size){
	assert(size%alignof(fhk_mref) == 0);

	struct fhk_mut_graph *M = mgraph(mp);
	if(UNLIKELY(M->committed + size > M->cap)){
		do {
			M->cap *= 2;
		} while(M->committed + size > M->cap);

		M = realloc(M, M->cap);
		if(UNLIKELY(!M))
			return 0;

		mgraph(mp) = M;
	}

	M->used = M->committed + size;
	return M->committed;
}

static void mgraph_commit(struct fhk_mut_graph *M){
	M->committed = M->used;
}

#define mgraph_newobj(mp, t) mgraph_alloc((mp), sizeof(t))

/* ---- mutation ---------------------------------------- */

fhk_status fhk_create_mut(fhk_mut_ref *mp){
	struct fhk_mut_graph *M = malloc(sizeof(struct fhk_mut_graph) + FHK_MUT_SIZE);
	if(UNLIKELY(!M)) return ecode(MEM);
	memset(M, 0, sizeof(*M));
	M->cap = sizeof(*M) + FHK_MUT_SIZE;
	M->committed = MGRAPH_FIRSTOBJ;
	M->used = M->committed;
	M->maptable = NULL;
	M->layout_valid = 0;
	M->dsym = DSYM_NOTAB;
	mgraph(mp) = M;
	return 0;
}

void fhk_destroy_mut(fhk_mut_ref *mp){
	struct fhk_mut_graph *M = mgraph(mp);
	if(M->maptable) free(M->maptable);
#if FHK_DSYM
	if(M->dsym)     free(M->dsym);
#endif
	free(M);
	mgraph(mp) = NULL;
}

void fhk_mut_pin(fhk_mut_ref *mp, fhk_mhandle e){
	if(mhandle_isref(e))
		mref_tag(mgraph(mp), e) |= MTAG_PIN;
}

fhk_status fhk_mut_add_group(fhk_mut_ref *mp){
	mgraph_invalidate(mgraph(mp));
	return mhandle_newgroup(mgraph(mp)->c_group++);
}

fhk_status fhk_mut_add_mapK(fhk_mut_ref *mp){
	mgraph_invalidate(mgraph(mp));
	return mhandle_newmapL(mgraph(mp)->c_mapK++);
}

fhk_status fhk_mut_add_mapI(fhk_mut_ref *mp){
	mgraph_invalidate(mgraph(mp));
	return mhandle_newmap(~(mgraph(mp)->c_mapI++));
}

fhk_status fhk_mut_add_model(fhk_mut_ref *mp, fhk_mhandle group, float k, float c){
	if(UNLIKELY(!mhandle_isgroup(group))) return ecode(INVAL);
	// this comparison also works for unset costs (NaN)
	if(UNLIKELY(k < 0 || c < 1)) return ecode(INVAL);

	fhk_mref modH = mgraph_newobj(mp, struct fhk_mut_model);
	if(UNLIKELY(!modH)) return ecode(MEM);

	struct fhk_mut_graph *M = mgraph(mp);
	struct fhk_mut_model *mod = mrefp(M, modH);

	mod->tag = MTAG(model);
	mod->gid = mhandleU(group);
	mod->next = M->model;
	mod->backV = 0;
	mod->backC = 0;
	mod->fwd = 0;
	mod->k = k;
	mod->c = c;
	// note: clo >= k is required for correctness, so that initial guesses can never
	// have negative upper bounds.
	// the best we can do at this stage, before prune, is clo <= k.
	// if k is unset, clo is unset which is fine.
	mod->clo = k;
	mod->chi = INFINITY;
	mod->dsym = DSYM_NONE;

	mgraph_invalidate(M);
	mgraph_commit(M);

	return M->model = modH;
}

fhk_status fhk_mut_add_var(fhk_mut_ref *mp, fhk_mhandle group){
	if(UNLIKELY(!mhandle_isgroup(group))) return ecode(INVAL);

	fhk_mref varH = mgraph_newobj(mp, struct fhk_mut_var);
	if(UNLIKELY(!varH)) return ecode(MEM);

	struct fhk_mut_graph *M = mgraph(mp);
	struct fhk_mut_var *var = mrefp(M, varH);

	var->tag = MTAG(var);
	var->size = SIZE_UNSET;
	var->gid = mhandleU(group);
	var->next = M->var;
	var->back = 0;
	var->fwdM = 0;
	var->fwdG = 0;
	var->clo = 0;
	var->chi = INFINITY;
	var->dsym = DSYM_NONE;

	mgraph_invalidate(M);
	mgraph_commit(M);

	return M->var = varH;
}

fhk_status fhk_mut_add_guard(fhk_mut_ref *mp, fhk_mhandle varH){
	fhk_mref guardH = mgraph_newobj(mp, struct fhk_mut_guard);
	if(UNLIKELY(!guardH)) return ecode(MEM);

	struct fhk_mut_graph *M = mgraph(mp);
	struct fhk_mut_guard *guard = mrefp(M, guardH);
	struct fhk_mut_var *var = handle_assertref(M, varH, MTAG(var));

	guard->tag = MTAG(guard);
	guard->opcode = GUARD_UNSET;
	guard->next = M->guard;
	guard->nextV = var->fwdG;
	guard->fwd = 0;
	guard->var = varH;
	guard->dsym = DSYM_NONE;

	mgraph_invalidate(M);
	mgraph_commit(M);

	var->fwdG = guardH;
	M->guard = guardH;

	return guardH;
}

static int edge_unpack_map(struct fhk_mut_edge *edge, struct fhk_mut_model *model,
		struct fhk_mut_var *var, fhk_mhandle2 map){

	fhk_mhandle lo = mhandle2_lo(map);

	if(mhandle_ismapu(lo)){ // usermap-usermap
		fhk_mhandle hi = mhandle2_hi(map);
		if(UNLIKELY(!mhandle_ismapu(hi))) return 0;
		edge->mapMV = lo;
		edge->mapVM = hi;
	}else{
		if(UNLIKELY(mhandle2_hi(map))) return 0;
		if(mhandle_istarget(lo)){ // space-space
			edge->mapMV = mhandle_newgroup(var->gid);
			edge->mapVM = mhandle_newgroup(model->gid);
		}else if(mhandle_isident(lo)){ // ident-ident
			edge->mapMV = lo;
			edge->mapVM = lo;
		}else{
			return 0;
		}
	}

	return 1;
}

fhk_status fhk_mut_add_param(fhk_mut_ref *mp, fhk_mhandle modelH, fhk_mhandle varH, fhk_mhandle2 map){
	fhk_mref edgeH = mgraph_newobj(mp, struct fhk_mut_edge);
	if(UNLIKELY(!edgeH)) return ecode(MEM);

	struct fhk_mut_graph *M = mgraph(mp);
	struct fhk_mut_edge *edge = mrefp(M, edgeH);
	struct fhk_mut_model *model = handle_assertref(M, modelH, MTAG(model));
	struct fhk_mut_var *var = handle_assertref(M, varH, MTAG(var));

	edge->tag = MTAG(edgeP);
	edge->nextV = var->fwdM;
	edge->nextM = model->backV;
	edge->var = varH;
	edge->model = modelH;
	if(UNLIKELY(!edge_unpack_map(edge, model, var, map))) return ecode(INVAL);

	mgraph_invalidate(M);
	mgraph_commit(M);

	var->fwdM = edgeH;
	model->backV = edgeH;

	return edgeH;
}

fhk_status fhk_mut_add_return(fhk_mut_ref *mp, fhk_mhandle modelH, fhk_mhandle varH, fhk_mhandle2 map){
	fhk_mref edgeH = mgraph_newobj(mp, struct fhk_mut_edge);
	if(UNLIKELY(!edgeH)) return ecode(MEM);

	struct fhk_mut_graph *M = mgraph(mp);
	struct fhk_mut_edge *edge = mrefp(M, edgeH);
	struct fhk_mut_model *model = handle_assertref(M, modelH, MTAG(model));
	struct fhk_mut_var *var = handle_assertref(M, varH, MTAG(var));

	edge->tag = MTAG(edgeR);
	edge->nextV = var->back;
	edge->nextM = model->fwd;
	edge->var = varH;
	edge->model = modelH;
	if(UNLIKELY(!edge_unpack_map(edge, model, var, map))) return ecode(INVAL);

	mgraph_invalidate(M);
	mgraph_commit(M);

	var->back = edgeH;
	model->fwd = edgeH;

	return edgeH;
}

fhk_status fhk_mut_add_check(fhk_mut_ref *mp, fhk_mhandle modelH, fhk_mhandle guardH, fhk_mhandle2 map,
		float penalty){

	fhk_mref checkH = mgraph_newobj(mp, struct fhk_mut_check);
	if(UNLIKELY(!checkH)) return ecode(INVAL);

	struct fhk_mut_graph *M = mgraph(mp);
	struct fhk_mut_check *check = mrefp(M, checkH);
	struct fhk_mut_model *model = handle_assertref(M, modelH, MTAG(model));
	struct fhk_mut_guard *guard = handle_assertref(M, guardH, MTAG(guard));

	check->tag = MTAG(check);
	check->nextG = guard->fwd;
	check->nextM = model->backC;
	check->guard = guardH;
	check->model = modelH;
	check->penalty = penalty;
	if(UNLIKELY(!edge_unpack_map((struct fhk_mut_edge *) check, model, mrefp(M, guard->var), map)))
		return ecode(INVAL);

	mgraph_invalidate(M);
	mgraph_commit(M);

	guard->fwd = checkH;
	model->backC = checkH;

	return checkH;
}

void fhk_mut_set_dsym(fhk_mut_ref *mp, fhk_mhandle handle, const char *sym){
#if FHK_DSYM
	if(!mhandle_isref(handle))
		return;

	struct fhk_mut_graph *M = mgraph(mp);
	int tag = mtagT(mref_tag(M, handle));
	if(!mtagT_isVMG(tag))
		return;

	fhkX_dsym dsym = fhk_debug_sym_add(&M->dsym, sym);
	switch(tag){
		case MTAG(var): ((struct fhk_mut_var *) mrefp(M, handle))->dsym = dsym; break;
		case MTAG(model): ((struct fhk_mut_model *) mrefp(M, handle))->dsym = dsym; break;
		case MTAG(guard): ((struct fhk_mut_guard *) mrefp(M, handle))->dsym = dsym; break;
	}
#else
	(void)mp;
	(void)handle;
	(void)sym;
#endif
}

void fhk_mut_set_costM(fhk_mut_ref *M, fhk_mhandle modelH, float k, float c){
	struct fhk_mut_model *model = mrefp(mgraph(M), modelH);
	model->k = k;
	model->c = c;
	model->clo = k;
	model->chi = INFINITY;
	mgraph_invalidate(mgraph(M));
}

fhk_status fhk_mut_set_sizeV(fhk_mut_ref *mp, fhk_mhandle varH, uint16_t size){
	struct fhk_mut_var *var = mrefp(mgraph(mp), varH);
	if(UNLIKELY(size_isset(var->size))) return ecode(WRITE) | etagA(HANDLE, varH);
	var->size = size;
	return 0;
}

fhk_status fhk_mut_set_opcodeG(fhk_mut_ref *mp, fhk_mhandle guardH, int opcode, fhk_gvalue arg){
	struct fhk_mut_guard *guard = mrefp(mgraph(mp), guardH);
	if(UNLIKELY(guard_isset(guard->opcode))) return ecode(WRITE) | etagA(HANDLE, guardH);
	guard->opcode = opcode;
	guard->arg = arg;
	return 0;
}
