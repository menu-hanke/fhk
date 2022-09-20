/* graph building. */

#include "build.h"
#include "conf.h"
#include "debug.h"
#include "def.h"

#include <assert.h>
#include <math.h>
#include <stdalign.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* ---- size tables ---------------------------------------- */

/* mutgraph object size table. */
static const uint8_t MTYPE_SIZE[FHK_MTYPE__num] = {
#define OBJSIZE(_, ct) sizeof(ct),
	MUT_OBJDEF(OBJSIZE)
#undef OBJSIZE
};
#define mtype_size(t)   MTYPE_SIZE[(t)]

/* predicate size table. */
static const uint8_t PRED_SIZE[FHK_PRED__num] = {
#define PREDSIZE(operator, operand) sizeof(operand),
	FHK_PREDEF(PREDSIZE)
#undef PREDSIZE
};
#define pred_size(p)    PRED_SIZE[(p)]

/* ---- buffer management ---------------------------------------- */

static fhk_mref32 mgraph_alloc_up(fhk_mut_ref *mp, fhk_mref32 size) {
	assert(!(size & (alignof(fhk_mref32)-1)));
	fhk_mut_graph *M = mrefM(mp);
	fhk_mref32 ptr = M->uused;
	M->uused += size;
	if(UNLIKELY(ptr+size > M->ucap)) {
		// don't need a loop here.
		// we don't have any variable size allocs so we know everything will fit
		// after one doubling.
		M->ucap <<= 1;
		fhk_mref32 dcap = M->dcap;
		M = realloc((void*)M - dcap, dcap + M->ucap);
		if(UNLIKELY(!M))
			return 0;
		mrefM(mp) = (void*)M + dcap;
	}
	return ptr;
}

#if FHK_DSYM

static fhk_mref32 mgraph_alloc_down(fhk_mut_ref *mp, fhk_mref32 size) {
	// don't require alignment here. this is where debug info goes.
	fhk_mut_graph *M = mrefM(mp);
	M->dused += size;
	ptrdiff_t dcap = M->dcap;
	if(UNLIKELY(M->dused > dcap)) {
		if(UNLIKELY(!dcap))
			M->dcap = MUT_INIT_DOWN;
		while(M->dused > M->dcap)
			M->dcap <<= 1;
		fhk_mut_graph *MM = malloc(M->dcap+M->ucap);
		if(UNLIKELY(!MM))
			return 0;
		fhk_mref32 used = M->dused-size;
		memcpy((void*)MM+M->dcap-used, (void*)M-used, used+M->uused);
		mrefM(mp) = (void*)MM + M->dcap;
		free((void*)M-dcap);
		M = mrefM(mp);
	}
	return -M->dused;
}

#endif

/* ---- mutation ---------------------------------------- */

fhk_status fhk_create_mut(fhk_mut_ref *mp) {
	fhk_mut_graph *M = malloc(sizeof(*M) + MUT_INIT_UP);
	if(UNLIKELY(!M)) return ecode(MEM);
	M->ucap = sizeof(*M) + MUT_INIT_UP;
	M->uused = MREF_USER;
	M->dcap = 0;
	M->dused = 0;
	M->k = INIT_K;
	M->c = INIT_C;
	mrefM(mp) = M;
	// identity map
	fhk_mut_var *id = mrefp(M, MREF_IDENT);
	id->tag = MTYPE(var) | MTAG_MARK | MTAG_MAP | MTAG_IDX;
	id->idx = 0xff;
	id->lc = LC_NONE;
	id->size = sizeof(fhk_subset);
	id->group = ~0;
	id->inverse = MREF_IDENT;
	// global map
	fhk_mut_var *g = mrefp(M, MREF_GLOBAL);
	g->tag = MTYPE(var) | MTAG_MARK | MTAG_MAP | MTAG_IDX;
	g->idx = 0;
	g->lc = LC_NONE;
	g->size = sizeof(fhk_subset);
	g->group = MREF_GLOBAL;
	g->inverse = 0;
#if FHK_DSYM
	id->sym = 0;
	g->sym = 0;
#endif
	return 0;
}

void fhk_destroy_mut(fhk_mut_ref *mp) {
	fhk_mut_graph *M = mrefM(mp);
	free((void*)M - M->dcap);
	mrefM(mp) = NULL;
}

void fhk_mut_set_default_cost(fhk_mut_ref *mp, float k, float c) {
	fhk_mut_graph *M = mrefM(mp);
	M->k = k;
	M->c = c;
}

static int obj_setmap(fhk_mut_graph *M, fhk_mref32 varH) {
	if(UNLIKELY(varH <= 0)) return 0;
	fhk_mut_var *var = mrefp(M, varH);
	if(LIKELY(var->tag & MTAG_MAP)) return 1;
	if(UNLIKELY((var->tag & MTAG_VARTYPE) != MTYPE(var))) return 0;
	if(UNLIKELY(var->size != sizeof(fhk_subset) && var->size != MSIZE_UNSET)) return 0;
	var->tag = MTYPE(var) | MTAG_MAP;
	var->size = sizeof(fhk_subset);
	var->inverse = 0;
	return 1;
}

static int obj_setguard(fhk_mut_graph *M, fhk_mref32 varH) {
	if(UNLIKELY(varH <= 0)) return 0;
	fhk_mut_var *var = mrefp(M, varH);
	if(LIKELY(var->tag & MTAG_GUARD)) return 1;
	if(UNLIKELY((var->tag & MTAG_VARTYPE) != MTYPE(var))) return 0;
	var->tag = MTYPE(var) | MTAG_GUARD;
	var->size = 0;
	var->predicate = 0;
	return 1;
}

fhk_status fhk_mut_add_var(fhk_mut_ref *mp, fhk_mref32 groupH) {
	if(UNLIKELY(!obj_setmap(mrefM(mp), groupH)))
		return ecode(TYPE) | etagA(HANDLE, groupH);
	fhk_mref32 varH = mgraph_alloc_up(mp, sizeof(fhk_mut_var));
	if(UNLIKELY(!varH)) return ecode(MEM);
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_var *var = mrefp(M, varH);
	var->tag = MTYPE(var);
	var->size = MSIZE_UNSET;
	var->group = groupH;
#if FHK_DSYM
	var->sym = 0;
#endif
	return varH;
}

fhk_status fhk_mut_set_lhs(fhk_mut_ref *mp, fhk_mref32 guardH, fhk_mref32 varH) {
	fhk_mut_graph *M = mrefM(mp);
	if(UNLIKELY(!obj_setguard(M, guardH))) return ecode(TYPE) | etagA(HANDLE, guardH);
	fhk_mut_var *guard = mrefp(M, guardH);
	fhk_mut_var *var = mrefp(M, varH);
	if(UNLIKELY(guard->group != var->group)) return ecode(GROUP) | etagA(HANDLE, varH);
	guard->back = varH;
	return 0;
}

fhk_status fhk_mut_set_inverse(fhk_mut_ref *mp, fhk_mref32 mapH, fhk_mref32 inverseH) {
	fhk_mut_graph *M = mrefM(mp);
	if(UNLIKELY(!obj_setmap(M, mapH))) return ecode(TYPE) | etagA(HANDLE, mapH);
	if(UNLIKELY(!obj_setmap(M, inverseH))) return ecode(TYPE) | etagA(HANDLE, inverseH);
	fhk_mut_var *map = mrefp(M, mapH);
	fhk_mut_var *inverse = mrefp(M, inverseH);
	if(UNLIKELY(map->inverse && map->inverse != inverseH))
		return ecode(INVERSE) | etagA(HANDLE, mapH) | etagB(HANDLE, map->inverse);
	if(UNLIKELY(inverse->inverse && inverse->inverse != mapH))
		return ecode(INVERSE) | etagA(HANDLE, inverseH) | etagB(HANDLE, inverse->inverse);
	map->inverse = inverseH;
	inverse->inverse = mapH;
	return 0;
}

fhk_status fhk_mut_set_size(fhk_mut_ref *mp, fhk_mref32 varH, uint16_t size) {
	if(UNLIKELY(varH < 0)) return ecode(TYPE) | etagA(HANDLE, varH);
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_var *var = mrefp(M, varH);
	if(UNLIKELY((var->tag & MTAG_TYPE) != MTYPE(var))) return ecode(TYPE) | etagA(HANDLE, varH);
	if(UNLIKELY(var->size != MSIZE_UNSET)) return ecode(WRITE) | etagA(HANDLE, varH);
	var->size = size;
	return 0;
}

fhk_status fhk_mut_add_model(fhk_mut_ref *mp, fhk_mref32 groupH) {
	if(UNLIKELY(!obj_setmap(mrefM(mp), groupH)))
		return ecode(TYPE) | etagA(HANDLE, groupH);
	fhk_mref32 modH = mgraph_alloc_up(mp, sizeof(fhk_mut_model));
	if(UNLIKELY(!modH)) return ecode(MEM);
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_model *mod = mrefp(M, modH);
	mod->tag = MTYPE(model);
	mod->group = groupH;
	mod->k = M->k;
	mod->c = M->c;
#if FHK_DSYM
	mod->sym = 0;
#endif
	return modH;
}

void fhk_mut_set_cost(fhk_mut_ref *mp, fhk_mref32 modelH, float k, float c) {
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_model *mod = mrefp(M, modelH);
	mod->k = k;
	mod->c = c;
}

/* can mapH point away from groupH? */
static int map_checkgroup(fhk_mut_graph *M, fhk_mref32 mapH, fhk_mref32 groupH) {
	fhk_mut_var *map = mrefp(M, mapH);
	return mapH == MREF_IDENT || map->group == MREF_GLOBAL || map->group == groupH;
}

static fhk_status checkedge(fhk_mut_graph *M, fhk_mref32 modelH, fhk_mref32 varH, fhk_mref32 mapH) {
	if(UNLIKELY((*(fhk_mtag *)mrefp(M, modelH) & MTAG_TYPE) != MTYPE(model)))
		return ecode(TYPE) | etagA(HANDLE, modelH);
	if(UNLIKELY((*(fhk_mtag *)mrefp(M, varH)) & MTAG_TYPE) != MTYPE(var))
		return ecode(TYPE) | etagA(HANDLE, varH);
	if(UNLIKELY(!obj_setmap(M, mapH)))
		return ecode(TYPE) | etagA(HANDLE, mapH);
	fhk_mut_model *mod = mrefp(M, modelH);
	if(UNLIKELY(!map_checkgroup(M, mapH, mod->group)))
		return ecode(GROUP) | etagA(HANDLE, mapH) | etagB(HANDLE, mod->group);
	return 0;
}

static fhk_status addedge(fhk_mut_ref *mp, fhk_mref32 modelH, fhk_mref32 varH, fhk_mref32 mapH,
		fhk_mtag tag) {
	fhk_status err;
	if(UNLIKELY(err = checkedge(mrefM(mp), modelH, varH, mapH))) return err;
	fhk_mref32 edgeH = mgraph_alloc_up(mp, sizeof(fhk_mut_edge));
	if(UNLIKELY(!edgeH)) return ecode(MEM);
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_edge *edge = mrefp(M, edgeH);
	edge->tag = tag;
	edge->mapMV = mapH;
	edge->var = varH;
	edge->model = modelH;
	return edgeH;
}

fhk_status fhk_mut_add_param(fhk_mut_ref *mp, fhk_mref32 modelH, fhk_mref32 varH, fhk_mref32 mapH) {
	return addedge(mp, modelH, varH, mapH, MTYPE(edgeP));
}

fhk_status fhk_mut_add_return(fhk_mut_ref *mp, fhk_mref32 modelH, fhk_mref32 varH, fhk_mref32 mapH) {
	return addedge(mp, modelH, varH, mapH, MTYPE(edgeR));
}

fhk_status fhk_mut_add_check(fhk_mut_ref *mp, fhk_mref32 modelH, fhk_mref32 guardH, fhk_mref32 mapH,
		float penalty) {
	fhk_status err;
	if(UNLIKELY(err = checkedge(mrefM(mp), modelH, guardH, mapH))) return err;
	if(UNLIKELY(!obj_setguard(mrefM(mp), guardH))) return ecode(TYPE) | etagA(HANDLE, guardH);
	fhk_mref32 checkH = mgraph_alloc_up(mp, sizeof(fhk_mut_check));
	if(UNLIKELY(!checkH)) return ecode(MEM);
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_check *check = mrefp(M, checkH);
	check->tag = MTYPE(check);
	check->mapMV = mapH;
	check->guard = guardH;
	check->model = modelH;
	check->penalty = penalty;
	return checkH;
}

fhk_status fhk_mut_add_rcheck(fhk_mut_ref *mp, fhk_mref32 edge, fhk_mref32 check, float penalty) {
	(void)mp;
	(void)edge;
	(void)check;
	(void)penalty;
	return ecode(NYI);
}

fhk_status fhk_mut_add_predicate(fhk_mut_ref *mp) {
	fhk_mref32 preH = mgraph_alloc_up(mp, sizeof(fhk_mut_predicate));
	if(UNLIKELY(!preH)) return ecode(MEM);
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_predicate *pre = mrefp(M, preH);
	pre->tag = MTYPE(predicate);
	pre->operator = PRED(_unset);
	return preH;
}

fhk_status fhk_mut_set_operator(fhk_mut_ref *mp, fhk_mref32 preH, int operator, fhk_operand *operand) {
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_predicate *pre = mrefp(M, preH);
	if(UNLIKELY((pre->tag & MTAG_TYPE) != MTYPE(predicate))) return ecode(TYPE) | etagA(HANDLE, preH);
	pre->operator = operator;
	// make sure the operand doesn't contain uninitialized bits, so we can compare them directly.
	memset(&pre->operand, 0, sizeof(pre->operand));
	memcpy(&pre->operand, operand, pred_size(operator));
	return 0;
}

fhk_status fhk_mut_set_predicate(fhk_mut_ref *mp, fhk_mref32 obj, fhk_mref32 pre) {
	fhk_mut_graph *M = mrefM(mp);
	fhk_mtag tag = *(fhk_mtag *) mrefp(M, obj);
	switch(tag & MTAG_TYPE) {
		case MTYPE(rcheck):
		{
			fhk_mut_retcheck *rc = mrefp(M, obj);
			rc->predicate = pre;
			return 0;
		}
		case MTYPE(var):
			if(LIKELY(obj_setguard(M, obj))) {
				fhk_mut_var *guard = mrefp(M, obj);
				guard->tag |= MTAG_PREGRD;
				guard->predicate = pre;
			}
			return 0;
	}
	return ecode(TYPE) | etagA(HANDLE, obj);
}

void fhk_mut_set_sym(fhk_mut_ref *mp, fhk_mref32 ref, const char *sym) {
#if FHK_DSYM
	fhk_mtag tag = *(fhk_mtag *) mrefp(mrefM(mp), ref);
	if(UNLIKELY(!mtype_isobj(tag & MTAG_TYPE))) return;
	size_t num = strlen(sym)+1;
	fhk_mref32 ptr = mgraph_alloc_down(mp, num);
	if(UNLIKELY(!ptr)) return;
	fhk_mut_graph *M = mrefM(mp);
	memcpy(mrefp(M, ptr), sym, num);
	fhk_mut_obj *obj = mrefp(M, ref);
	obj->sym = ptr;
#else
	(void)mp; (void)ref; (void)sym;
#endif
}

void fhk_mut_disable(fhk_mut_ref *mp, fhk_mref32 obj) {
	fhk_mut_graph *M = mrefM(mp);
	*(fhk_mtag *) mrefp(M, obj) |= MTAG_SKIP;
}

/* ---- intern ---------------------------------------- */

// intern predicates and guards.
// this doesn't relink the lists, relink must be run after this.
// note: this function overwrites var->next.
static void intern(fhk_mut_graph *M) {
	fhk_mtag tag;
	// intern checks, reset var->next.
	fhk_mref32 head = 0;
	for(fhk_mref32 ref=MREF_START; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_TYPE)) {
			case MTYPE(predicate):
			{
				fhk_mut_predicate *pre = mrefp(M, ref);
				fhk_mut_predicate *p;
				for(fhk_mref32 r=head; r; r=p->link) {
					p = mrefp(M, r);
					if(pre->operator == p->operator
							&& !memcmp(&pre->operand, &p->operand, sizeof(p->operand))) {
						pre->tag |= MTAG_SKIP;
						pre->link = r;
						trace(INTRPRED, ref, fhk_mut_debug_sym(M, ref), fhk_mut_debug_sym(M, r));
						goto nextp;
					}
				}
				pre->link = head;
				head = ref;
				break;
			}
			case MTYPE(var):
			{
				fhk_mut_var *var = mrefp(M, ref);
				var->next = 0;
				break;
			}
		}
nextp: continue;
	}
	// intern guards.
	for(fhk_mref32 ref=MREF_USER; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_PREGRD|MTAG_TYPE)) {
			case MTAG_PREGRD|MTYPE(var):
			{
				fhk_mut_var *guard = mrefp(M, ref);
				fhk_mut_var *var = mrefp(M, guard->back);
				fhk_mut_predicate *pre = mrefp(M, guard->predicate);
				fhk_mref32 ph = (pre->tag & MTAG_SKIP) ? pre->link : guard->predicate;
				fhk_mut_var *g;
				for(fhk_mref32 gh=var->next; gh; gh=g->next) {
					g = mrefp(M, gh);
					if(g->predicate == ph) {
						guard->tag |= MTAG_SKIP;
						guard->next = gh;
						trace(INTRGRD, ref, fhk_mut_debug_sym(M, ref), fhk_mut_debug_sym(M, gh));
						goto nextg;
					}
				}
				guard->next = var->next;
				var->next = ref;
				break;
			}
			case MTYPE(check):
			{
				fhk_mut_check *check = mrefp(M, ref);
				fhk_mut_var *guard = mrefp(M, check->guard);
				if(guard->tag & MTAG_SKIP)
					check->guard = guard->next;
				break;
			}
			case MTYPE(rcheck):
			{
				fhk_mut_retcheck *rc = mrefp(M, ref);
				fhk_mut_predicate *pre = mrefp(M, rc->predicate);
				if(pre->tag & MTAG_SKIP)
					rc->predicate = pre->link;
				break;
			}
		}
nextg: continue;
	}
}

/* ---- relink ---------------------------------------- */

static void linkvar(fhk_mut_graph *M, fhk_mref32 ref) {
	fhk_mut_var *var = mrefp(M, ref);
	var->next = M->var;
	if(!(var->tag & MTAG_PREGRD)) var->back = 0;
	var->fwdM = 0;
	var->nm = 0;
	M->var = ref;
	trace(LINKVAR, ref, fhk_mut_debug_sym(M, ref));
}

static void linkmodel(fhk_mut_graph *M, fhk_mref32 ref) {
	fhk_mut_model *mod = mrefp(M, ref);
	mod->next = M->model;
	mod->backV = 0;
	mod->backC = 0;
	mod->fwdR = 0;
	mod->fwdRC = 0;
	mod->nc = 0;
	mod->np = 0;
	mod->nr = 0;
	mod->nrc = 0;
	M->model = ref;
	trace(LINKMOD, ref, fhk_mut_debug_sym(M, ref));
}

static void linkpredicate(fhk_mut_graph *M, fhk_mref32 ref) {
	// nothing to link here.
	(void)M;
	(void)ref;
	trace(LINKPRED, ref, fhk_mut_debug_sym(M, ref));
}

static void linkrcheck(fhk_mut_graph *M, fhk_mref32 ref) {
	(void)M;
	(void)ref;
	assert(!"TODO");
}

static void linkcheck(fhk_mut_graph *M, fhk_mref32 ref) {
	fhk_mut_check *check = mrefp(M, ref);
	fhk_mut_model *mod = mrefp(M, check->model);
	assert(!((check->tag|mod->tag|((fhk_mut_var *) mrefp(M, check->guard))->tag) & MTAG_SKIP));
	check->nextM = mod->backC;
	mod->backC = ref;
	mod->nc++;
	trace(LINKCHECK, ref, fhk_mut_debug_sym(M, check->model), fhk_mut_debug_sym(M, check->guard),
			check->penalty);
}

static void linkparam(fhk_mut_graph *M, fhk_mref32 ref) {
	fhk_mut_edge *edge = mrefp(M, ref);
	fhk_mut_model *mod = mrefp(M, edge->model);
	fhk_mut_var *var = mrefp(M, edge->var);
	assert(!((edge->tag|mod->tag|var->tag) & MTAG_SKIP));
	edge->nextV = var->fwdM;
	edge->nextM = mod->backV;
	var->fwdM = ref;
	mod->backV = ref;
	mod->np++;
	trace(LINKPARAM, ref, fhk_mut_debug_sym(M, edge->model), fhk_mut_debug_sym(M, edge->var));
}

static void linkreturn(fhk_mut_graph *M, fhk_mref32 ref) {
	fhk_mut_edge *edge = mrefp(M, ref);
	fhk_mut_model *mod = mrefp(M, edge->model);
	fhk_mut_var *var = mrefp(M, edge->var);
	assert(!((edge->tag|mod->tag|var->tag) & MTAG_SKIP));
	edge->nextV = var->back;
	edge->nextM = mod->fwdR;
	var->back = ref;
	mod->fwdR = ref;
	mod->nr++;
	var->nm++;
	trace(LINKRET, ref, fhk_mut_debug_sym(M, edge->model), fhk_mut_debug_sym(M, edge->var));
}

static void relink(fhk_mut_graph *M) {
	M->var = 0;
	M->model = 0;
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_START; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_TYPE)) {
			case MTYPE(var):
				linkvar(M, ref);
				break;
			case MTYPE(model):
				linkmodel(M, ref);
				break;
			case MTYPE(predicate):
				linkpredicate(M, ref);
				break;
			case MTYPE(rcheck):
				linkrcheck(M, ref);
				break;
			case MTYPE(check):
				linkcheck(M, ref);
				break;
			case MTYPE(edgeP):
				linkparam(M, ref);
				break;
			case MTYPE(edgeR):
				linkreturn(M, ref);
				break;
			default:
				trace(LINKSKIP, ref, fhk_mut_debug_sym(M, ref));
				break;
		}
	}
}

/* ---- bound analysis ---------------------------------------- */

static void bound_skipchain(fhk_mut_graph *M, fhk_mref32 back) {
	fhk_mut_var *lhs = mrefp(M, back);
	if(UNLIKELY((lhs->tag & (MTAG_PREGRD|MTAG_SKIP)) == MTAG_PREGRD)) {
		bound_skipchain(M, lhs->back);
		lhs->tag |= *((fhk_mtag *) mrefp(M, lhs->back)) & MTAG_SKIP;
	}
}

// group skipped             ->   skip+unlink vars, models
// var, map, model skipped   ->   skip+unlink edges
// lhs skipped               ->   skip guard
// edge skipped              ->   partial skip model (set k=inf, but don't unlink)
static void bound_setskip(fhk_mut_graph *M) {
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_USER; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		switch(tag & MTAG_TYPE) {
			case MTYPE(var):
			case MTYPE(model):
			{
				fhk_mut_obj *obj = mrefp(M, ref);
				fhk_mut_var *group = mrefp(M, obj->group);
				if(group->tag & MTAG_SKIP)
					obj->tag |= MTAG_SKIP;
				if(UNLIKELY((tag & (MTAG_PREGRD|MTAG_SKIP)) == MTAG_PREGRD)) {
					fhk_mut_var *guard = (fhk_mut_var *) obj;
					if(UNLIKELY(guard->back > ref))
						bound_skipchain(M, guard->back);
					obj->tag |= *((fhk_mtag *) mrefp(M, guard->back)) & MTAG_SKIP;
				}
				break;
			}
			case MTYPE(edgeP):
			case MTYPE(edgeR):
			case MTYPE(check):
			{
				fhk_mut_edge *edge = mrefp(M, ref);
				fhk_mut_var *var = mrefp(M, edge->var);
				fhk_mut_model *model = mrefp(M, edge->model);
				fhk_mut_var *map = mrefp(M, edge->mapMV);
				if((tag | var->tag | map->tag | model->tag) & MTAG_SKIP) {
					edge->tag |= MTAG_SKIP;
					model->k = INFINITY;
				} else if((tag & MTAG_TYPE) == MTYPE(edgeR)) {
					if(map->inverse) {
						fhk_mut_var *inverse = mrefp(M, map->inverse);
						if(inverse->tag & MTAG_SKIP) {
							edge->tag |= MTAG_SKIP;
							model->k = INFINITY;
						}
					}
				}
				break;
			}
		}
	}
}

static int bheap_new(fhk_heapref *hp) {
	fhk_bheap *H = malloc(sizeof(fhk_bheap) + BHEAP_INIT*sizeof(fhk_bound));
	if(UNLIKELY(!H)) return 0;
	H->used = 0;
	H->cap = BHEAP_INIT;
	*hp = H;
	return 1;
}

static int bheap_insert(fhk_heapref *hp, uint64_t bound) {
	fhk_bheap *H = *hp;
	if(UNLIKELY(H->used == H->cap)) {
		uint32_t cap = H->cap << 1;
		H = realloc(H, sizeof(fhk_bheap) + cap*sizeof(fhk_bound));
		if(UNLIKELY(!H)) return 0;
		H->cap = cap;
		*hp = H;
	}
	int64_t idx = ++H->used;
	uint64_t *heap = bheap_data(H);
	while(idx > 1) {
		int64_t idxp = idx >> 1;
		uint64_t parent = heap[idxp];
		if(parent <= bound) break;
		heap[idx] = parent;
		idx = idxp;
	}
	heap[idx] = bound;
	return 1;
}

static uint64_t bheap_remove(fhk_bheap *H) {
	assert(H->used > 0);
	uint64_t *heap = bheap_data(H);
	uint64_t root = heap[1];
	uint64_t e = heap[H->used];
	int64_t end = --H->used;
	int64_t idx = 1;
	for(;;) {
		int64_t l = idx << 1;
		if(l > end) break;
		if(l+1 <= end && heap[l+1] <= heap[l]) l++;
		if(e <= heap[l]) break;
		heap[idx] = heap[l];
		idx = l;
	}
	heap[idx] = e;
	return root;
}

static void bheap_destroy(fhk_heapref *hp) {
	free(*hp);
}

/* is the edge guaranteed to point to a nonempty subset of the variable,
 * given that the model's space is nonempty? */
static int isnonemptyMV(fhk_mut_graph *M, fhk_mut_edge *e) {
	return e->mapMV == MREF_IDENT
		|| e->mapMV == MREF_GLOBAL
		|| e->mapMV == ((fhk_mut_model *) mrefp(M, e->model))->group;
}

/* is the edge guaranteed to point to a nonempty subset of the variable,
 * given that the variable's space is nonempty? */
static int isnonemptyVV(fhk_mut_graph *M, fhk_mut_edge *e) {
	return e->mapMV == MREF_IDENT
		|| (((fhk_mut_model *) mrefp(M, e->model))->group == MREF_GLOBAL
				&& e->mapMV == ((fhk_mut_var *) mrefp(M, e->var))->group);
}

static fhk_status bound_visit_model_low(fhk_mut_graph *M, fhk_heapref *hp, fhk_mut_model *mod) {
	float cost = 0;
	fhk_mut_edge *e;
	for(fhk_mref32 eh=mod->backV; eh; eh=e->nextM) {
		e = mrefp(M, eh);
		if(!isnonemptyMV(M, e))
			continue;
		fhk_mut_var *var = mrefp(M, e->var);
		assert(isfinitecx(var->clo));
		assert(!((e->tag|var->tag) & MTAG_SKIP));
		cost += var->clo;
	}
	trace(BNDLOMOD, fhk_mut_debug_sym(M, pmref(M, mod)), costf(mod, cost), cost);
	cost = costf(mod, cost);
	mod->clo = cost;
	if(LIKELY(!(mod->tag & MTAG_SKIP) && cost < INFINITY)) {
		for(fhk_mref32 eh=mod->fwdR; eh; eh=e->nextM) {
			e = mrefp(M, eh);
			assert(!((e->tag & ((fhk_mut_var *) mrefp(M, e->var))->tag) & MTAG_SKIP));
			if(UNLIKELY(!bheap_insert(hp, bound_newL(cost, e->var))))
				return ecode(MEM);
		}
	}
	return 0;
}

static fhk_status bound_visit_model_high(fhk_mut_graph *M, fhk_heapref *hp, fhk_mut_model *mod) {
	float cost = 0;
	fhk_mut_check *c;
	for(fhk_mref32 ch=mod->backC; ch; ch=c->nextM) {
		c = mrefp(M, ch);
		cost += c->penalty;
	}
	// TODO: return checks
	fhk_mut_edge *e;
	for(fhk_mref32 eh=mod->backV; eh; eh=e->nextM) {
		e = mrefp(M, eh);
		fhk_mut_var *var = mrefp(M, e->var);
		// even for high bounds infinities should never propagate.
		assert(isfinitecx(var->chi));
		assert(!((e->tag|var->tag) & MTAG_SKIP));
		cost += var->chi;
	}
	trace(BNDHIMOD, fhk_mut_debug_sym(M, pmref(M, mod)), costf(mod, cost), cost);
	cost = costf(mod, cost);
	mod->chi = cost;
	if(!(mod->tag & MTAG_SKIP) && cost < INFINITY) {
		for(fhk_mref32 eh=mod->fwdR; eh; eh=e->nextM) {
			e = mrefp(M, eh);
			assert(!((e->tag & ((fhk_mut_var *) mrefp(M, e->var))->tag) & MTAG_SKIP));
			if(!isnonemptyVV(M, e))
				continue;
			if(UNLIKELY(!bheap_insert(hp, bound_newH(cost, e->var))))
				return ecode(MEM);
		}
	}
	return 0;
}

static fhk_status bound_init_heap(fhk_mut_graph *M, fhk_heapref *hp) {
	fhk_status err;
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_START; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE))  {
		tag = *(fhk_mtag *) mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_TYPE)) {
			case MTYPE(var):
			{
				fhk_mut_var *var = mrefp(M, ref);
				var->clo = INFINITY;
				var->chi = INFINITY;
				if(!var->back && !(tag & MTAG_PREGRD)) {
					if(UNLIKELY(!bheap_insert(hp, bound_newL(0, ref)))) return ecode(MEM);
					if(UNLIKELY(!bheap_insert(hp, bound_newH(0, ref)))) return ecode(MEM);
					trace(BNDGIVEN, fhk_mut_debug_sym(M, ref));
				}
				break;
			}
			case MTYPE(model):
			{
				fhk_mut_model *model = mrefp(M, ref);
				int remlo = 0, remhi = 0;
				fhk_mut_edge *e;
				for(fhk_mref32 eh=model->backV; eh; eh=e->nextM) {
					e = mrefp(M, eh);
					remlo += !!isnonemptyMV(M, e);
					remhi++;
				}
				if(remlo > 0) model->clo = uf32(-remlo);
				else if(UNLIKELY(err = bound_visit_model_low(M, hp, model))) return err;
				if(remhi > 0) model->chi = uf32(-remhi);
				else if(UNLIKELY(err = bound_visit_model_high(M, hp, model))) return err;
				break;
			}
		}
	}
	return 0;
}

static fhk_status bound_propagate(fhk_mut_graph *M, fhk_heapref *hp) {
	while((*hp)->used) {
		fhk_bound bound = bheap_remove(*hp);
		int hi = bound_isH(bound);
		fhk_mut_var *var = mrefp(M, bound_ref(bound));
		assert(!(var->tag & MTAG_SKIP));
		float *cv = &var->clo + hi;
		if(isfinitecx(*cv)) {
			assert(*cv <= uf32(bound_ucost(bound)));
			continue;
		}
		*(uint32_t *)cv = bound_ucost(bound);
		if(hi) trace(BNDHIVAR, fhk_mut_debug_sym(M, bound_ref(bound)), uf32(bound_ucost(bound)));
		else   trace(BNDLOVAR, fhk_mut_debug_sym(M, bound_ref(bound)), uf32(bound_ucost(bound)));
		fhk_mut_edge *e;
		for(fhk_mref32 eh=var->fwdM; eh; eh=e->nextV) {
			e = mrefp(M, eh);
			if(!hi && !isnonemptyMV(M, e)) continue;
			fhk_mut_model *mod = mrefp(M, e->model);
			float *cm = &mod->clo + hi;
			assert(!isfinitecx(*cm));
			uint32_t rem = fu32(*cm) + 1;
			if(!rem) {
				fhk_status err;
				err = hi ? bound_visit_model_high(M, hp, mod) : bound_visit_model_low(M, hp, mod);
				if(UNLIKELY(err)) return err;
			} else {
				*cm = uf32(rem);
			}
		}
	}
	return 0;
}

static void bound_normalize(fhk_mut_graph *M) {
	fhk_mut_model *mm;
	for(fhk_mref32 ref=M->model; ref; ref=mm->next) {
		mm = mrefp(M, ref);
		if(!isfinitecx(mm->clo)) mm->clo = INFINITY;
		if(!isfinitecx(mm->chi)) mm->chi = INFINITY;
	}
}

fhk_status fhk_mut_analyze(fhk_mut_ref *mp) {
	bound_setskip(mrefM(mp));
	relink(mrefM(mp));
	fhk_heapref hp;
	if(UNLIKELY(!bheap_new(&hp))) return ecode(MEM);
	fhk_status err = 0;
	fhk_mut_graph *M = mrefM(mp);
	if(UNLIKELY(err = bound_init_heap(M, &hp))) goto out;
	if(UNLIKELY(err = bound_propagate(M, &hp))) goto out;
	bound_normalize(M);
out:
	bheap_destroy(&hp);
	return err;
}

/* ---- subgraph marking ---------------------------------------- */

static void mark_visit_var(fhk_mut_graph *M, fhk_mref32 varH);
static void mark_visit_model(fhk_mut_graph *M, fhk_mref32 modH);

static void mark_visit_edgeMV(fhk_mut_graph *M, fhk_mut_edge *e) {
	e->tag |= MTAG_MARK;
	mark_visit_var(M, e->mapMV);
	mark_visit_var(M, e->var);
}

static void mark_visit_edgeVM(fhk_mut_graph *M, fhk_mut_edge *e) {
	e->tag |= MTAG_MARK;
	fhk_mut_var *map = mrefp(M, e->mapMV);
	if(map->inverse)
		mark_visit_var(M, map->inverse);
	mark_visit_model(M, e->model);
}

static void mark_visit_model(fhk_mut_graph *M, fhk_mref32 modH) {
	fhk_mut_model *mod = mrefp(M, modH);
	if(mod->tag & MTAG_MARKREC) return;
	trace(MARKMOD, fhk_mut_debug_sym(M, modH), mod->clo, mod->chi);
	mod->tag |= MTAG_MARK;
	mark_visit_var(M, mod->group);
	fhk_mut_check *c;
	for(fhk_mref32 ch=mod->backC; ch; ch=c->nextM) {
		c = mrefp(M, ch);
		c->tag |= MTAG_MARK;
		mark_visit_var(M, c->mapMV);
		mark_visit_var(M, c->guard);
	}
	// TODO: return checks, visit predicates
	fhk_mut_edge *e;
	for(fhk_mref32 eh=mod->backV; eh; eh=e->nextM) {
		e = mrefp(M, eh);
		mark_visit_edgeMV(M, e);
	}
	for(fhk_mref32 eh=mod->fwdR; eh; eh=e->nextM) {
		e = mrefp(M, eh);
		fhk_mut_var *var = mrefp(M, e->var);
		e->tag |= MTAG_RETAIN;
		var->tag |= MTAG_RETAIN;
		mark_visit_var(M, e->mapMV);
	}
}

static void mark_visit_var(fhk_mut_graph *M, fhk_mref32 varH) {
	fhk_mut_var *var = mrefp(M, varH);
	if(var->tag & MTAG_MARKREC) return;
	trace(MARKVAR, fhk_mut_debug_sym(M, varH), var->clo, var->chi);
	var->tag |= MTAG_MARK;
	mark_visit_var(M, var->group);
	// given variable?
	if(!var->back) return;
	// predicated guard?
	// must have var->back here because we unlinked guards of skipped variables
	// just before analysis.
	if(var->tag & MTAG_PREGRD) {
		((fhk_mut_predicate *) mrefp(M, var->predicate))->tag |= MTAG_MARK;
		mark_visit_var(M, var->back);
		return;
	}
	// else: it's a computed variable.
	// infinite low bound means all model low bounds are infinite, ie: this var is uncomputable.
	// since it's asked to be kept we'll pick any model and fail at runtime.
	if(UNLIKELY(!isfinitecx(var->clo))) {
		mark_visit_edgeVM(M, mrefp(M, var->back));
		return;
	}
	// else (the common case): we must pick:
	// (1) all models with model->clo < var->chi
	// (2) if var->chi is finite: any model that guarantees var->chi: ie. a model with nonempty
	//     return set and model->chi = var->chi. this must exist since it's the only way var->chi
	//     can get set.
	uint32_t chi = fu32(var->chi);
	uint32_t beta = ~(uint32_t)0;
	fhk_mut_edge *e;
	for(fhk_mref32 eh=var->back; eh; eh=e->nextV) {
		e = mrefp(M, eh);
		fhk_mut_model *mod = mrefp(M, e->model);
		uint32_t clo = fu32(mod->clo);
		if(clo < chi) {
			if(isnonemptyVV(M, e))
				beta = min(beta, fu32(mod->chi));
			mark_visit_edgeVM(M, e);
		}
	}
	// pick a model that satisfies (2), if we still need one.
	if(chi < beta) {
		for(fhk_mref32 eh=var->back; eh; eh=e->nextV) {
			e = mrefp(M, eh);
			fhk_mut_model *mod = mrefp(M, e->model);
			if(isnonemptyVV(M, e) && fu32(mod->chi) == chi) {
				mark_visit_edgeVM(M, e);
				return;
			}
		}
	}
}

fhk_status fhk_mut_mark(fhk_mut_ref *mp, fhk_mref32 ref) {
	fhk_mut_graph *M = mrefM(mp);
	fhk_mtag tag = *(fhk_mtag *) mrefp(M, ref);
	if(!mtype_isobj(tag & (MTAG_TYPE|MTAG_MARKREC))) return 0;
	if(UNLIKELY(tag & MTAG_SKIP)) return ecode(SKIP);
	fhk_mut_obj *obj = mrefp(M, ref);
	if(UNLIKELY(!isfinitecx(obj->clo))) return ecode(CHAIN) | etagA(HANDLE, ref);
	switch(tag & MTAG_TYPE) {
		case MTYPE(var):
			mark_visit_var(M, ref);
			break;
		case MTYPE(model):
			mark_visit_model(M, ref);
			break;
		default: UNREACHABLE();
	}
	return 0;
}

/* ---- layout ---------------------------------------- */

static void layout_setskip(fhk_mut_graph *M) {
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_START; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		if(!(tag & MTAG_RETAIN))
			*(fhk_mtag *) mrefp(M, ref) |= MTAG_SKIP;
	}
}

static void layout_classify(fhk_mut_graph *M) {
	fhk_mtag tag;
	// don't classify builtins.
	for(fhk_mref32 ref=MREF_USER; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *)mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_TYPE|MTAG_PREGRD|MTAG_DERIVE)) {
			case MTYPE(var):
			{
				fhk_mut_var *var = mrefp(M, ref);
				if(var->nm == 1) {
					fhk_mut_edge *e = mrefp(M, var->back);
					fhk_mut_model *mod = mrefp(M, e->model);
					if(e->mapMV == MREF_IDENT && mod->nr == 1 && mod->nrc == 0) {
						var->tag |= MTAG_DERIVE;
						mod->tag |= MTAG_DERIVE;
						// treat the variable as unlayouted and the model as layouted.
						// it doesn't really matter which one we pick as layouted,
						// as long as we only pick one.
						// choosing the model makes jump table generation a bit simpler,
						// since the jtab entry is generated by the model, not the variable.
						var->lc = LC_NONE;
						mod->lc = (tag & MTAG_MAP)
							? var->group == MREF_GLOBAL ? LC_KMAPD : LC_IMAPD : LC_DERIVE;
						break;
					}
				}
				var->lc = (tag & MTAG_MAP)
					? var->group == MREF_GLOBAL
						? (var->back ? LC_KMAPC : LC_KMAPG)
						: (var->back ? LC_IMAPC : LC_IMAPG)
					: var->back ? LC_COMPUTED : LC_GIVEN;
				break;
			}
			case MTAG_PREGRD|MTYPE(var):
			{
				// TODO given/computed guards
				fhk_mut_var *var = mrefp(M, ref);
				var->lc = LC_COMPUTED;
				break;
			}
			case MTYPE(model):
			{
				fhk_mut_model *mod = mrefp(M, ref);
				mod->lc = LC_NDMODEL;
				break;
			}
		}
	}
}

static fhk_status layout_count(fhk_mut_graph *M) {
	memset(M->nlc, 0, sizeof(M->nlc));
	fhk_mtag tag;
	// don't count builtins.
	for(fhk_mref32 ref=MREF_USER; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *)mrefp(M, ref);
		if(mtype_isobj(tag & (MTAG_SKIP|MTAG_TYPE))) {
			fhk_mut_obj *obj = mrefp(M, ref);
			if(obj->lc != LC_NONE)
				M->nlc[obj->lc]++;
		}
	}
	return 0;
}

static void layout_order_set(fhk_layout_state *ls, fhk_mut_obj *obj) {
	int64_t lc = obj->lc;
	int64_t i = ls->curi[lc];
	int cur = ls->cursor[lc];
	if(cur == ls->end[lc][i]) {
		i++;
		ls->curi[lc] = i;
		assert(ls->start[lc][i] >= cur);
		cur = ls->start[lc][i];
		assert(i < LAYOUT_MAXINTERVAL);
	}
	obj->idx = cur;
	ls->cursor[lc] = cur+1;
}

static void layout_order_walk_model(fhk_mut_graph *M, fhk_layout_state *ls, fhk_mref32 modelH);

static void layout_order_walk_var(fhk_mut_graph *M, fhk_layout_state *ls, fhk_mref32 varH) {
	fhk_mut_var *var = mrefp(M, varH);
	if(var->tag & MTAG_IDX) return;
	var->tag |= MTAG_IDX;
	layout_order_walk_var(M, ls, var->group);
	if(var->back) {
		if(var->tag & MTAG_PREGRD) {
			layout_order_walk_var(M, ls, var->back);
		} else {
			fhk_mut_edge *e;
			for(fhk_mref32 eh=var->back; eh; eh=e->nextV) {
				e = mrefp(M, eh);
				fhk_mut_var *mapMV = mrefp(M, e->mapMV);
				if(mapMV->inverse)
					layout_order_walk_var(M, ls, mapMV->inverse);
				layout_order_walk_model(M, ls, e->model);
			}
			// model will layout derived vars.
			if(var->lc == LC_NONE) {
				// right?
				assert(var->idx == ((fhk_mut_model *) mrefp(M, e->model))->idx);
				return;
			}
		}
	}
	layout_order_set(ls, (fhk_mut_obj *) var);
}

static void layout_order_walk_model(fhk_mut_graph *M, fhk_layout_state *ls, fhk_mref32 modelH) {
	fhk_mut_model *model = mrefp(M, modelH);
	if(model->tag & MTAG_IDX) return;
	model->tag |= MTAG_IDX;
	layout_order_walk_var(M, ls, model->group);
	fhk_mut_check *c;
	for(fhk_mref32 ch=model->backC; ch; ch=c->nextM) {
		c = mrefp(M, ch);
		layout_order_walk_var(M, ls, c->mapMV);
		layout_order_walk_var(M, ls, c->guard);
	}
	fhk_mut_edge *e;
	for(fhk_mref32 eh=model->backV; eh; eh=e->nextM) {
		e = mrefp(M, eh);
		layout_order_walk_var(M, ls, e->mapMV);
		layout_order_walk_var(M, ls, e->var);
	}
	layout_order_set(ls, (fhk_mut_obj *) model);
	if(model->tag & MTAG_DERIVE) {
		fhk_mut_edge *e = mrefp(M, model->fwdR);
		fhk_mut_var *v = mrefp(M, e->var);
		assert(!e->nextM && v->lc == LC_NONE);
		v->idx = model->idx;
	}
}

static int layout_put_class(fhk_layout_state *ls, int cls, int cursor, int direction, int end) {
	int n = ls->n[cls];
	int step = min(n, abs(end-cursor));
	if(step > 0) {
		ls->n[cls] = n - step;
		int i = ls->curi[cls];
		if(direction > 0) {
			ls->start[cls][i] = cursor;
			ls->end[cls][i] = cursor + step;
		} else {
			ls->start[cls][i] = cursor - step + 1;
			ls->end[cls][i] = cursor+1;
		}
		ls->curi[cls] = i+1;
		cursor += step*direction;
	}
	return cursor;
}

static void layout_hole(fhk_mut_graph *M, fhk_mref32 start, fhk_mref32 end) {
	if(end <= start) return;
	for(int i=0;;i++) {
		// can extend an existing hole?
		if(M->endhole[i] == start) {
			M->endhole[i] = end;
			return;
		}
		// create new hole?
		if(!M->endhole[i]) {
			M->hole[i] = start;
			M->endhole[i] = end;
			return;
		}
		assert(i < LAYOUT_MAXHOLE);
	}
}

/*
 * 0            .      global           XV..                   + G hole 0
 *                                                             +
 *        (7)   ^.7    computed         XV.G
 *        (6)   ^.3 *  kmapc            XV.G
 *        (5)   ^.6    ndmodel          X.JG     * J<0xff
 *        (4)   ^.5    derive           XVJG     *
 *        (3)   ^.2 *  kmapd            XVJG     *
 *        (2)   ^.4    given            XVJ.     *             + G hole 1
 * 0x7f   (1)   ^.1 *  kmapg            XVJ.     *             +
 * 0x80   (8)   v.1 *  imapg            XVJ.     *             +
 *        (9)   v.4    given            XVJ.     *             +
 *        (10)  v.2 *  imapd            XVJG     *
 *        (11)  v.5    derive           XVJG     *
 *        (12)  v.7    ndmodel          X.JG     *
 *        (13)  v.3 *  imapc            XV.G
 *        (14)  v.6    computed         XV.G
 *                                                             + G hole 2
 * 0xff         .      ident            XV..                   +
 *        (15)  v.1    computed         XV.G
 *        (16)  v.2    given            XVJ.     * J>0xff      + G hole 3
 *        (17)  v.3    derive           XVJG     *
 *        (18)  v.4    ndmodel          X.JG     *                                 > V hole
 */
static fhk_status layout_order(fhk_mut_graph *M) {
	fhk_layout_state ls;
	memset(M->hole, 0, sizeof(M->hole));
	memset(M->endhole, 0, sizeof(M->endhole));
	memset(&ls, 0, sizeof(ls));
	memcpy(&ls.n, M->nlc, sizeof(ls.n));
	// TODO: map count error checking, either here or in count.
	// (1)
	int cursor = layout_put_class(&ls, LC_KMAPG, OBJ_MAXKMAPG, -1, 0);
	M->kmapg = cursor;
	// (2) - must leave at least 1 spot at the beginning so that jump table offsets are non-negative
	cursor = layout_put_class(&ls, LC_GIVEN, cursor, -1, ls.n[LC_KMAPD]+max(ls.n[LC_KMAPC], 1));
	int hole1 = cursor+1;
	// (3)
	cursor = layout_put_class(&ls, LC_KMAPD, cursor, -1, 0);
	// (4) - must leave at least 1 spot at beginning
	cursor = layout_put_class(&ls, LC_DERIVE, cursor, -1, max(ls.n[LC_KMAPC], 1));
	// (5) - must leave at least 1 spot. prefer computed to models, so that we can put models at the end.
	cursor = layout_put_class(&ls, LC_NDMODEL, cursor, -1, max(1,ls.n[LC_KMAPC]+ls.n[LC_COMPUTED]));
	M->j[0] = cursor-1; // 0 = error, 1 = ok.    cursor+1-2 = cursor-1.
	// (6)
	cursor = layout_put_class(&ls, LC_KMAPC, cursor, -1, 0);
	// (7)
	cursor = layout_put_class(&ls, LC_COMPUTED, cursor, -1, 0);
	layout_hole(M, 0, (cursor+1)*sizeof(void *));
	// (8)
	cursor = layout_put_class(&ls, LC_IMAPG, OBJ_MAXKMAPG+1, 1, OBJ_IDENT);
	// (9)
	cursor = layout_put_class(&ls, LC_GIVEN, cursor, 1, OBJ_IDENT-(ls.n[LC_IMAPC]+ls.n[LC_IMAPD]));
	layout_hole(M, hole1*sizeof(void *), cursor*sizeof(void *));
	// (10)
	cursor = layout_put_class(&ls, LC_IMAPD, cursor, 1, OBJ_IDENT);
	// (11)
	cursor = layout_put_class(&ls, LC_DERIVE, cursor, 1, OBJ_IDENT-ls.n[LC_IMAPC]);
	// (12) - prefer computed to models.
	cursor = layout_put_class(&ls, LC_NDMODEL, cursor, 1, OBJ_IDENT-(ls.n[LC_IMAPC]+ls.n[LC_COMPUTED]));
	int nj0 = cursor - M->j[0];
	// (13)
	cursor = layout_put_class(&ls, LC_IMAPC, cursor, 1, OBJ_IDENT);
	// (14)
	cursor = layout_put_class(&ls, LC_COMPUTED, cursor, 1, OBJ_IDENT);
	layout_hole(M, cursor*sizeof(void *), 0x100*sizeof(void *));
	// (15)
	cursor = layout_put_class(&ls, LC_COMPUTED, OBJ_IDENT+1, 1, 0xffff);
	// (16)
	M->j[1] = cursor - nj0;
	int hole3 = cursor;
	cursor = layout_put_class(&ls, LC_GIVEN, cursor, 1, 0xffff);
	layout_hole(M, hole3*sizeof(void *), cursor*sizeof(void *));
	// (17)
	cursor = layout_put_class(&ls, LC_DERIVE, cursor, 1, 0xffff);
	M->nv = cursor;
	// (18)
	cursor = layout_put_class(&ls, LC_NDMODEL, cursor, 1, 0xffff);
	M->nx = cursor;
	layout_hole(M, cursor*sizeof(void *), 0x7fffffff);
	// note: we could create another hole here before the allocation,
	// but that's not really useful. the whole graph will fit in 2GB anyway.
	memset(&ls.curi, 0, sizeof(ls.curi));
	for(int i=0; i<LC__NUM; i++) ls.cursor[i] = ls.start[i][0];
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_USER; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_TYPE|MTAG_IDX)) {
			case MTYPE(var):
				layout_order_walk_var(M, &ls, ref);
				break;
			case MTYPE(model):
				layout_order_walk_model(M, &ls, ref);
				break;
		}
	}
	return 0;
}

static fhk_mref32 layout_reserve(fhk_mut_graph *M, fhk_mref32 size, fhk_mref32 align) {
	fhk_mref32 mask = align - 1;
	for(int i=0;; i++) {
		fhk_mref32 hole = (M->hole[i] + mask) & ~mask;
		if(hole+size <= M->endhole[i]) {
			M->hole[i] = hole + size;
			return hole;
		}
		assert(i < LAYOUT_MAXHOLE);
	}
}

static void layout_offsets(fhk_mut_graph *M) {
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_USER; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *)mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_TYPE|MTAG_PREGRD|MTAG_DERIVE)) {
			case MTYPE(var):
			{
				fhk_mut_var *var = mrefp(M, ref);
				if(var->nm > 0) {
					// we DON'T align heap, just the variable itself
					fhk_mref32 hsize = var->nm * sizeof(fhk_edgeH);
					fhk_mref32 off = layout_reserve(M, hsize+sizeof(fhk_var), alignof(uint32_t));
					var->offset = off + hsize;
				}
				break;
			}
			case MTAG_PREGRD|MTYPE(var):
			{
				fhk_mut_var *guard = mrefp(M, ref);
				fhk_mut_predicate *pre = mrefp(M, guard->predicate);
				size_t psize = pred_size(pre->operator);
				guard->offset = psize+layout_reserve(M, psize+sizeof(fhk_pregrd), psize);
				break;
			}
			case MTYPE(model):
			case MTAG_DERIVE|MTYPE(model):
			{
				fhk_mut_model *mod = mrefp(M, ref);
				fhk_mref32 off = layout_reserve(M,
						sizeof(fhk_model)
						+ mod->nc*sizeof(fhk_edgeC)
						+ (mod->np+mod->nr)*sizeof(fhk_edgeX)
						+ mod->nrc*sizeof(fhk_edgeCR),
						alignof(fhk_model)
				);
				mod->offset = off + mod->nc*sizeof(fhk_edgeC);
				break;
			}
			case MTYPE(rcheck):
			{
				assert(!"TODO: rcheck");
				break;
			}
		}
	}
}

#if FHK_DSYM

static void layout_symtab(fhk_mut_graph *M) {
	M->symtab = layout_reserve(M, M->nx*sizeof(fhk_mref32), alignof(fhk_mref32));
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_START; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		if(!mtype_isobj(tag & (MTAG_SKIP|MTAG_TYPE)))
			continue;
		fhk_mut_obj *obj = mrefp(M, ref);
		if(!obj->sym)
			continue;
		// for derives, if both have a symbol, layout only the variable's sym.
		if((tag & (MTAG_DERIVE|MTAG_TYPE)) == (MTAG_DERIVE|MTYPE(model))) {
			fhk_mut_edge *e = mrefp(M, ((fhk_mut_model *) obj)->fwdR);
			fhk_mut_var *var = mrefp(M, e->var);
			if(var->sym) {
				obj->symofs = 0;
				continue;
			}
		}
		obj->symofs = layout_reserve(M, strlen(mrefp(M, obj->sym))+1, 1);
	}
}

#endif

#if FHK_TRACEON(build)

static void layout_trace(fhk_mut_graph *M) {
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_START; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		switch(tag & (MTAG_SKIP|MTAG_TYPE)) {
			case MTYPE(var):
			{
				fhk_mut_var *var = mrefp(M, ref);
				if(var->tag & MTAG_DERIVE)
					trace(LAYODVAR, var->idx, var->idx-M->j[jidx(var->idx)], fhk_mut_debug_sym(M, ref));
				else if(var->tag & MTAG_PREGRD)
					trace(LAYOPGRD, var->idx, fhk_mut_debug_sym(M, ref), var->offset);
				else if(var->back)
					trace(LAYOCOMP, var->idx, fhk_mut_debug_sym(M, ref), var->offset);
				else
					trace(LAYOGIVEN, var->idx, var->idx-M->j[jidx(var->idx)], fhk_mut_debug_sym(M, ref));
				break;
			}
			case MTYPE(model):
			{
				fhk_mut_model *mod = mrefp(M, ref);
				if(mod->tag & MTAG_DERIVE)
					trace(LAYODMOD, mod->idx, mod->idx-M->j[jidx(mod->idx)], fhk_mut_debug_sym(M, ref), mod->offset);
				else
					trace(LAYOMOD, mod->idx, mod->idx-M->j[jidx(mod->idx)], fhk_mut_debug_sym(M, ref), mod->offset);
				break;
			}
		}
	}
}

#endif

fhk_status fhk_mut_layout(fhk_mut_ref *mp) {
	fhk_mut_graph *M = mrefM(mp);
	fhk_status err;
	layout_setskip(M);
	intern(M);
	relink(M);
	layout_classify(M);
	if(UNLIKELY(err = layout_count(M))) return err;
	if(UNLIKELY(err = layout_order(M))) return err;
	layout_offsets(M);
#if FHK_DSYM
	layout_symtab(M);
#endif
#if FHK_TRACEON(build)
	layout_trace(M);
#endif
	return 0;
}

size_t fhk_mut_size(fhk_mut_ref *mp) {
	fhk_mut_graph *M = mrefM(mp);
	for(int i=LAYOUT_MAXHOLE-1;; i--) {
		assert(i >= 0);
		if(M->endhole[i])
			return ALIGN(M->nx*sizeof(fhk_meta), alignof(void *))   // meta table
				+ sizeof(fhk_graph)                                 // graph
				+ M->hole[i];                                       // graph data (including object table)
	}
}

/* ---- build ---------------------------------------- */

static void build_ident_meta(fhk_Gref G) {
	fhk_meta *meta = &grefmeta(G, ~OBJ_IDENT);
	meta->tag = TAG_GIVEN | TAG_MAP;
	meta->group = 0; // this should never be accessed.
	meta->size = sizeof(fhk_subset);
}

static fhk_status build_var_meta(fhk_mut_graph *M, fhk_Gref G, fhk_mref32 varH) {
	fhk_mut_var *var = mrefp(M, varH);
	if(UNLIKELY(var->size == MSIZE_UNSET)) return ecode(UNSET);
	fhk_meta *meta = &grefmeta(G, ~(xidx)var->idx);
	meta->size = var->size;
	fhk_mut_var *group = mrefp(M, var->group);
	meta->group = group->idx;
	uint8_t tag = 0;
	if(var->tag & MTAG_DERIVE)
		tag |= TAG_DERIVE;
	else if(var->back && !(var->tag & MTAG_PREGRD))
		tag |= TAG_COMPUTED;
	else if(!var->back)
		tag |= TAG_GIVEN;
	if(var->tag & MTAG_GUARD)
		tag |= TAG_GUARD;
	if(var->tag & MTAG_MAP)
		tag |= TAG_MAP;
	// TODO: presolve (literally iff derive and clo=chi<inf)
	meta->tag = tag;
	return 0;
}

static void build_var_obj(fhk_mut_graph *M, fhk_Gref G, fhk_mref32 varH) {
	fhk_mut_var *vm = mrefp(M, varH);
	fhk_var *vg = mrefp(G, vm->offset);
	grefobj(G, vm->idx) = vg;
	vg->cost = vm->clo;
	fhk_mut_edge *e;
	fhk_edgeH *h = vg->heap;
	for(fhk_mref32 eh=vm->back; eh; eh=e->nextV) {
		e = mrefp(M, eh);
		fhk_mut_model *mod = mrefp(M, e->model);
		// make sure the index table entry is set, because we will be referencing it
		// for writing back the reverse edge indices.
		// (build_model_obj may or may not be called yet).
		grefobj(G, mod->idx) = mrefp(G, mod->offset);
		h--;
		h->c = mod->clo;
		h->idx = mod->idx;
		fhk_mref32 invH;
		if(e->mapMV == vm->group) {
			// the inverse for a space map is the other side's space map.
			invH = mod->group;
		} else {
			// otherwise the map should have a user defined inverse.
			fhk_mut_var *mapMV = mrefp(M, e->mapMV);
			invH = mapMV->inverse;
			assert(invH);
		}
		h->map = ((fhk_mut_var *) mrefp(M, invH))->idx;
		// ugly reverse index scan.
		// there's a million better ways to do this.
		// most models have just 1 or 2 returns so whatever.
		fhk_mut_edge *e2;
		int idx = mod->np;
		for(fhk_mref32 eh2=mod->fwdR; eh2; eh2=e2->nextM, idx++) {
			if(eh2 == eh) break;
			e2 = mrefp(M, eh2);
		}
		// h->ei is the reverse index here.
		// it will be written back to the return edge and patched to the heap index
		// after building the heap.
		h->ei = idx;
	}
	// build the initial heap.
	vg->nh = vm->nm;
	int64_t end = -vm->nm;
	for(int64_t i=end>>1; i<0; i++) {
		uint64_t vi = vheap(vg, i)->u64;
		int64_t j = i;
		for(;;) {
			int64_t l = j << 1;
			if(l < end) break;
			if(l > end && vheap(vg, l-1)->u32[EH_COST] <= vheap(vg, l)->u32[EH_COST]) l--;
			if((int32_t)vi <= (int32_t)vheap(vg, l)->u32[EH_COST]) break;
			vheap(vg, j)->u64 = vheap(vg, l)->u64;
			j = l;
		}
		vheap(vg, j)->u64 = vi;
	}
	// write back indices.
	// heap indices are positive here. ~(u64)idx is the corresponding negative index.
	for(int64_t i=end; i<0; i++) {
		fhk_model *mod = grefobj(G, vheap(vg, i)->idx);
		mod->ex[vheap(vg, i)->ei].info = ~i;
		vheap(vg, i)->ei = ~i;
	}
	// heap[-1].c is initial delta.
	float delta = INFINITY;
	if(end <= -2) delta = vheap(vg, -2)->c;
	if(end <= -3) delta = vheap(vg, -3)->c;
	vheap(vg, -1)->c = delta;
}

static void build_pguard_obj(fhk_mut_graph *M, fhk_Gref G, fhk_mref32 guardH) {
	fhk_mut_var *vm = mrefp(M, guardH);
	fhk_pregrd *gg = mrefp(G, vm->offset);
	grefobj(G, vm->idx) = gg;
	fhk_mut_predicate *pre = mrefp(M, vm->predicate);
	fhk_mut_var *var = mrefp(M, vm->back);
	gg->operator = pre->operator;
	gg->idx = var->idx;
	size_t sz = pred_size(pre->operator);
	memcpy((void *)gg - sz, &pre->operand, sz);
}

static void build_model_meta(fhk_mut_graph *M, fhk_Gref G, fhk_mref32 modelH) {
	fhk_mut_model *mod = mrefp(M, modelH);
	fhk_meta *meta = &grefmeta(G, ~(xidx)mod->idx);
	meta->tag = TAG_MODEL;
}

static void build_model_obj(fhk_mut_graph *M, fhk_Gref G, fhk_mref32 modelH) {
	fhk_mut_model *mm = mrefp(M, modelH);
	fhk_model *mg = mrefp(G, mm->offset);
	grefobj(G, mm->idx) = mg;
	mg->k = mm->k;
	mg->c = mm->c;
	mg->ki = -mg->k/mg->c;
	mg->ci = 1/mg->c;
	// TODO: bonus
	mg->bonus = 0;
	// build checks.
	int64_t nc = mm->nc;
	mg->e_check = nc;
	fhk_edgeC *ec = mg->ec - nc;
	fhk_mut_check *c;
	for(fhk_mref32 ch=mm->backC; ch; ch=c->nextM, ec++) {
		c = mrefp(M, ch);
		ec->idx = ((fhk_mut_var *) mrefp(M, c->guard))->idx;
		ec->map = ((fhk_mut_var *) mrefp(M, c->mapMV))->idx;
		ec->penalty = c->penalty;
	}
	// reorder checks. highest penalty goes first.
	ec = mg->ec - nc;
	for(int64_t i=1; i<nc; i++) {
		fhk_edgeC ci = ec[i];
		int64_t j = i;
		for(; j>0; j--) {
			if(ec[j-1].penalty >= ci.penalty) break;
			ec[j] = ec[j-1];
		}
		ec[j] = ci;
	}
	// build parameters.
	uint32_t order[MAX_PARAM];
	fhk_edgeX *ex = mg->ex;
	fhk_mut_edge *e;
	int ncp = 0;
	int nx = 0;
	int ng = 0;
	int np = mm->np;
	int pi = 0;
	for(fhk_mref32 eh=mm->backV; eh; eh=e->nextM, ex++) {
		e = mrefp(M, eh);
		fhk_mut_var *var = mrefp(M, e->var);
		if(var->back) {
			// TODO: precomputed (should get -2)
			ncp++;
			order[pi] = fu32(var->chi - var->clo);
		} else {
			ng++;
			order[pi] = -1;
		}
		pi++;
		ex->info = np - pi;
		if(var->tag & MTAG_DERIVE) ex->info |= 0x80;
		ex->idx = var->idx;
		ex->map = ((fhk_mut_var *) mrefp(M, e->mapMV))->idx;
	}
	// reorder parameters:
	//   [computed params in *increasing* order of cost difference]
	//   [precomputed params (cost diff=0)]
	//   [given params]
	mg->e_cparam = ncp;
	mg->e_xcparam = ncp + nx;
	mg->e_param = np;
	for(int64_t i=1; i<np; i++) {
		fhk_edgeX ei = mg->ex[i];
		uint32_t o = order[i];
		int64_t j = i;
		for(; j>0; j--) {
			if(order[j-1] <= o) break;
			order[j] = order[j-1];
			mg->ex[j] = mg->ex[j-1];
		}
		order[j] = o;
		mg->ex[j] = ei;
	}
	if(mm->tag & MTAG_DERIVE) {
		mg->e_return = np;
		mg->n_rcheck = 0;
		return;
	}
	// build return edges.
	// er->info is filled in by build_var_obj.
	fhk_edgeX *er = mg->ex + np + mm->nr;
	mg->e_return = np + mm->nr;
	for(fhk_mref32 eh=mm->fwdR; eh; eh=e->nextM) {
		e = mrefp(M, eh);
		er--;
		er->idx = ((fhk_mut_var *) mrefp(M, e->var))->idx;
		er->map = ((fhk_mut_var *) mrefp(M, e->mapMV))->idx;
	}
	// build return checks.
	// TODO
	if(mm->nrc)
		assert(!"TODO");
	mg->n_rcheck = 0;
}

#if FHK_DSYM

static void build_symtab(fhk_mut_graph *M, fhk_Gref G) {
	grefG(G)->symtab = M->symtab;
	fhk_mref32 *tab = mrefp(G, M->symtab);
	memset(tab, 0, M->nx*sizeof(*tab));
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_START; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *) mrefp(M, ref);
		if(!mtype_isobj(tag & (MTAG_SKIP|MTAG_TYPE)))
			continue;
		fhk_mut_obj *obj = mrefp(M, ref);
		if(obj->sym && obj->sym) {
			fhk_mref32 ofs = obj->symofs;
			strcpy(mrefp(G, ofs), mrefp(M, obj->sym));
			tab[obj->idx] = ofs;
		}
	}
}

#endif

fhk_status fhk_mut_build(fhk_mut_ref *mp, void *buf) {
	fhk_mut_graph *M = mrefM(mp);
	buf += M->nx * sizeof(fhk_meta);
	buf += sizeof(fhk_graph);
	buf = ALIGN(buf, alignof(void *));
	fhk_Gref G = (fhk_Gref) buf;
	assert(ALIGN(grefG(G), max(alignof(fhk_meta), alignof(fhk_graph))) == grefG(G));
#if FHK_DSYM
	build_symtab(M, G);
#endif
	grefG(G)->nx = M->nx;
	grefG(G)->nv = M->nv;
	memcpy(grefG(G)->j, M->j, sizeof(M->j));
	grefG(G)->kmapg = M->kmapg;
	build_ident_meta(G);
	fhk_mtag tag;
	for(fhk_mref32 ref=MREF_GLOBAL; ref<M->uused; ref+=mtype_size(tag & MTAG_TYPE)) {
		tag = *(fhk_mtag *)mrefp(M, ref);
		if(mtype_isobj(tag & (MTAG_SKIP|MTAG_TYPE))) {
			fhk_mut_obj *obj = mrefp(M, ref);
			fhk_mut_var *group = mrefp(M, obj->group);
			fhk_meta *ometa = &grefmeta(G, ~(xidx)obj->idx);
			fhk_meta *gmeta = &grefmeta(G, ~(xidx)group->idx);
			ometa->group = group->idx;
			gmeta->tag |= TAG_GROUP;
		}
		switch(tag & (MTAG_SKIP|MTAG_TYPE)) {
			case MTYPE(var):
			{
				fhk_status err;
				if(UNLIKELY(err = build_var_meta(M, G, ref)))
					return err;
				fhk_mut_var *var = mrefp(M, ref);
				if(tag & MTAG_PREGRD)
					build_pguard_obj(M, G, ref);
				else if(var->back && !(tag & MTAG_DERIVE))
					build_var_obj(M, G, ref);
				break;
			}
			case MTYPE(model):
			{
				if(!(tag & MTAG_DERIVE))
					build_model_meta(M, G, ref);
				build_model_obj(M, G, ref);
				break;
			}
			case MTYPE(edgeR):
			{
				fhk_mut_edge *e = mrefp(M, ref);
				fhk_mut_var *var = mrefp(M, e->var);
				if(grefmeta(G, ~(xidx)var->idx).tag & TAG_GROUP) {
					fhk_mut_model *mod = mrefp(M, e->model);
					grefmeta(G, ~(xidx)mod->idx).tag |= TAG_GROUP;
				}
				break;
			}
		}
	}
	return (fhk_status) grefG(G);
}

/* ---- query ---------------------------------------- */

fhk_query fhk_mut_query(fhk_mut_ref *mp, fhk_mref32 ref) {
	fhk_mut_graph *M = mrefM(mp);
	fhk_mut_obj *obj = mrefp(M, ref);
	if(!mtype_isobj(obj->tag & (MTAG_SKIP|MTAG_TYPE))) return QUERY_PRUNED;
	switch(obj->lc) {
		case LC_KMAPG:
		case LC_KMAPD:
		case LC_IMAPG:
		case LC_IMAPD:
		case LC_GIVEN:
		case LC_DERIVE:
		case LC_NDMODEL:
			return query_newJ(obj->idx, obj->idx - M->j[jidx(obj->idx)]);
		default:
			return query_newI(obj->idx);
	}
}


