#pragma once

#include "def.h"
#include "fhk.h"
#include "solve.h"

#include <stdalign.h>
#include <stdint.h>

// you might want to turn this off when e.g. generating bindings
#ifndef FHK_STATIC_ASSERT
#define FHK_STATIC_ASSERT static_assert
#endif

#define issigned(t)  ((t)(-1) < (t)0)
#define maxofU(t)    ((t) ~(uint64_t)0) /* 0xff...ff */
#define maxofS(t)    ((1ULL << (8*sizeof(t)-1))-1) /* 0x7f..ff */
#define maxof(t)     (issigned(t) ? maxofS(t) : maxofU(t))
#define minof(t)     ((t) (1ULL << (8*sizeof(t)-1)))
#define ftypeof(s,f) typeof(((s*)0)->f)

/* data type sanity checks */
FHK_STATIC_ASSERT(MAX_GROUP <= maxof(fhkP_group), "MAX_GROUP too large");
FHK_STATIC_ASSERT(MAX_IDX <= maxof(fhkP_idx), "MAX_IDX too large");
FHK_STATIC_ASSERT(MIN_IDX >= minof(fhkP_idx), "MIN_IDX too small");
FHK_STATIC_ASSERT(MAX_INST <= maxof(fhkP_inst), "MAX_INST too large");
FHK_STATIC_ASSERT(MAX_MAPK <= maxof(ftypeof(fhk_edge, map)), "MAX_MAPK too large");
FHK_STATIC_ASSERT(MIN_MAPI >= minof(ftypeof(fhk_edge, map)), "MIN_MAPI too small");
FHK_STATIC_ASSERT(-MAX_CHECK <= -minof(ftypeof(struct fhk_model, p_check)), "MAX_CHECK too large");
FHK_STATIC_ASSERT(MAX_PARAM <= maxof(ftypeof(struct fhk_model, p_param)), "MAX_PARAM too large");
FHK_STATIC_ASSERT(MAX_RETURN <= maxof(ftypeof(struct fhk_model, p_return)), "MAX_RETURN too large");
FHK_STATIC_ASSERT(MAX_MOD <= maxof(ftypeof(struct fhk_var, n_mod)), "MAX_MOD too large");

/* this is used to pack indices */
FHK_STATIC_ASSERT(maxof(ftypeof(fhk_edge, ex)) >= maxof(fhkP_ei), "fhk_edge->ex too small");

/* vars and shadows must both be accessible through the VAL in fhk_graph */
FHK_STATIC_ASSERT(sizeof(struct fhk_var) == sizeof(struct fhk_guard),
		"node size mismatch: sizeof(fhk_var) != sizeof(fhk_guard)");

/* subsets */
FHK_STATIC_ASSERT(subsetI_first(subsetI_newZ(0, MAX_INST)) == MAX_INST, "subset: inst(MAX_INST) unrepresentable");
FHK_STATIC_ASSERT(subsetIE_znum(subsetI_newZ(MAX_INST, 0)) == MAX_INST, "subset: znum(MAX_INST) unrepresentable");

/* solver */
FHK_STATIC_ASSERT(sizeof(ftypeof(struct fhk_solver, stateM[0])) == sizeof(void *), "size mismatch: S->stateM");
FHK_STATIC_ASSERT(sizeof(ftypeof(struct fhk_solver, stateV[0])) == sizeof(void *), "size mismatch: S->stateV");
FHK_STATIC_ASSERT(sizeof(ftypeof(struct fhk_solver, stateG[0])) == sizeof(void *), "size mismatch: S->stateG");
FHK_STATIC_ASSERT(sizeof(ftypeof(struct fhk_solver, stateC[0])) == sizeof(void *), "size mismatch: S->stateC");

/* map state */
FHK_STATIC_ASSERT(sizeof(ftypeof(fhkX_anymap, imap)) == sizeof(ftypeof(fhkX_anymap, kmap)), "size mismatch: anymap");

/* search state */
FHK_STATIC_ASSERT(spV_inst(SP_FLAGS | spV_newchain(MAX_INST, 0)) == MAX_INST, "sp: MAX_INST unrepresentable");
FHK_STATIC_ASSERT(spV_edge(SP_FLAGS | spV_newchain(0, MAX_MOD)) == MAX_MOD, "sp: MAX_MOD unrepresentable");

/* external */

/* mgraph */
FHK_STATIC_ASSERT(offsetof(struct fhk_mut_edge, mapMV) == offsetof(struct fhk_mut_check, mapMG),
		"mut: edge/check map layout mismatch");
FHK_STATIC_ASSERT(offsetof(struct fhk_mut_var, gid) == offsetof(struct fhk_mut_model, gid),
		"mut: VM gid layout mismatch");
FHK_STATIC_ASSERT(offsetof(struct fhk_mut_var, order) == offsetof(struct fhk_mut_model, order),
		"mut: VMG order layout mismatch");
FHK_STATIC_ASSERT(offsetof(struct fhk_mut_var, order) == offsetof(struct fhk_mut_guard, order),
		"mut: VMG order layout mismatch");

#define CHECKALIGN(_,t) FHK_STATIC_ASSERT(alignof(t) == alignof(fhkX_mref), "mut: packed array has holes");
MUT_OBJDEF(CHECKALIGN)
#undef CHECKALIGN
