#pragma once

#include "def.h"

#include <stdint.h>

/* mutable graph objects.
 * this must be placed before mtag definitions, see below for the structs.
 * do not change the order, see mtag_isnode()/mtag_isedge() macros.
 */
#define MUT_OBJDEF(_) \
	_(edgeP,  struct fhk_mut_edge)  \
	_(edgeR,  struct fhk_mut_edge)  \
	_(check,  struct fhk_mut_check) \
	_(guard,  struct fhk_mut_guard) \
	_(var,    struct fhk_mut_var)   \
	_(model,  struct fhk_mut_model)

enum {
#define OBJDEF(name, _) FHKX_MTAG_##name,
	MUT_OBJDEF(OBJDEF)
#undef OBJDEF
	FHKX_MTAG__max
};

/* tags
 *
 * +-------+-----+---+---+------+
 * |   7   |  6  | 5 | 4 | 3..0 |
 * +-------+-----+---+---+------+
 * | prune | pin | a | b | type |
 * +-------+-----+---+---+------+
 *
 * flags: prune    do not include in graph, unlink on next layout (any node)
 *        pin      always include in graph, never prune (only variables may be pinned)
 *        a, b     work markers for graph algorithms (prune, toposort)
 */
typedef int8_t fhkX_mtag;
#define MTAG_PRUNE         0x80
#define MTAG_PIN           0x40
#define MTAG_A             0x20
#define MTAG_B             0x10
#define MTAG_AB            (MTAG_A|MTAG_B)
#define MTAG_FLAGS         (MTAG_PRUNE|MTAG_PIN|MTAG_AB)
#define MTAG(x)            FHKX_MTAG_##x
#define mtagT(t)           ((t) & 0xf)  /* type only */
#define mtagTP(t)          ((t) & 0x8f) /* type including prune */
#define mtagT_isedge(t)    ((uint32_t)(t) < MTAG(check))
#define mtagT_isanyedge(t) ((uint32_t)(t) <= MTAG(check))
#define mtagT_isVMG(t)     ((uint32_t)((t)-MTAG(guard)) <= (MTAG(model)-MTAG(guard)))
#define mtagT_isVM(t)      ((uint32_t)((t)-MTAG(var)) <= (MTAG(model)-MTAG(var)))
#define mtag_ispruned(t)   ((t) & MTAG_PRUNE)
#define mtag_ispinned(t)   ((t) & MTAG_PIN)
#define mtag_isA(t)        ((t) & MTAG_A)
#define mtag_isB(t)        ((t) & MTAG_B)

NOAPI const uint8_t fhkX_mtag_size[FHKX_MTAG__max];
#define mtag_size(t)      fhkX_mtag_size[mtagT(t)]

/* handles
 *
 *                     +----+--------+-------+
 *                     | 31 | 30..28 | 27..0 |
 * +-------------------+----+--------+-------+
 * | reference         | 0  |      mref      |
 * +-------------------+----+--------+-------+
 * | L-map             | 1  |   0    |  map  |  map >= 0
 * +-------------------+----+--------+-------+
 * | J-map             | 1  |   0    |  map  |  map < 0
 * +-------------------+----+--------+-------+
 * | target group      | 1  |   1    |   -1  |
 * +-------------------+----+--------+-------+
 * | group / space map | 1  |   1    | group |
 * +-------------------+----+--------+-------+
 * | identity map      | 1  |   2    |   -1  |
 * +-------------------+----+--------+-------+
 */
#define MHANDLE_IDENT       ((fhk_mhandle)0xafffffff)
#define MHANDLE_SPACE       ((fhk_mhandle)0x9fffffff)
#define mhandleT(h)         ((uint32_t)(h) >> 28)
#define mhandleV(h)         (((h) << 4) >> 4)  /* sign-extended */
#define mhandleU(h)         ((h) & 0x0fffffff)   /* unsigned */
#define mhandle_isref(h)    ((h) >= 0)
#define mhandle_ismapL(h)   ((h) < (fhk_mhandle)0x88000000) /* L-map (user defined constant map) */
#define mhandle_ismapJ(h)   (((uint32_t)(h) >> 27) == 0x11) /* J-map (user defined nonconstant map) */
#define mhandle_isgroup(h)  (mhandleT(h) == 0x9) /* group/space map */
#define mhandle_ismapu(h)   ((h) < (fhk_mhandle)0x90000000) /* any user defined map */
#define mhandle_ismap(h)    ((h) < (fhk_mhandle)0xb0000000) /* any map */
#define mhandle_istarget(h) ((h) == MHANDLE_SPACE) /* target space pseudo-map */
#define mhandle_isident(h)  ((h) == MHANDLE_IDENT) /* ident pseudo-map */
#define mhandle_newT(t)     ((uint32_t)(t) << 28)
#define mhandle_newV(v)     ((v) & 0x0fffffff)
#define mhandle_newmapL(m)  (mhandle_newT(0x8) | (m))
#define mhandle_newmap(m)   (mhandle_newT(0x8) | mhandle_newV(m))
#define mhandle_newgroup(g) (mhandle_newT(0x9) | (g))

/* mhandle2 packs */
#define mhandle2_lo(h2)     ((fhk_mhandle)(h2))
#define mhandle2_hi(h2)     ((fhk_mhandle)((h2) >> 32))

/* query
 *   +--------+-------+
 *   | 63..32 | 31..0 |
 *   +--------+-------+
 *   |  slot  |  idx  |
 *   +--------+-------+
 */
#define QUERY_PRUNED        ((fhk_query)(-1))
#define QUERY_INCLUDE       ((fhk_query)(-2))
#define query_new(idx,slot) (((uint32_t)(idx))|((fhk_query)(slot)<<32))
#define query_idx(idx)      query_new((idx),0ull)

/* edges */
struct fhk_mut_edge {
	fhkX_mtag tag;
	fhk_mhandle mapMV;
	fhk_mhandle mapVM;
	fhk_mref nextV; // next edge in var->back or var->fwdM
	fhk_mref nextM; // next edge in model->backV or model->fwd
	fhk_mref var;
	fhk_mref model;
};

/* checks.
 * layout must match fhk_mut_edge.
 */
struct fhk_mut_check {
	fhkX_mtag tag;
	fhk_mhandle mapMG;
	fhk_mhandle mapGM;
	fhk_mref nextG; // next edge in guard->fwd
	fhk_mref nextM; // next edge in model->back
	fhk_mref guard;
	fhk_mref model;
	float penalty;
};

/* variables */
struct fhk_mut_var {
	fhkX_mtag tag;
	uint16_t gid;   // must be after tag
	int32_t order;  // must be after gid
	float clo, chi; // must be after order
	uint16_t size;
	fhk_mref next; // next variable
	fhk_mref back; // model edge linked list
	fhk_mref fwdM; // model edge linked list
	fhk_mref fwdG; // guard linked list
	fhkX_dsym dsym;
};

#define SIZE_UNSET     0xffff
#define size_isset(s)  ((s) != SIZE_UNSET)

/* models */
struct fhk_mut_model {
	fhkX_mtag tag;
	uint16_t gid;    // must be after tag
	int32_t order;   // must be after gid
	float clo, chi;  // must be after order
	fhk_mref next;  // next model
	fhk_mref backV; // parameter edge linked list
	fhk_mref backC; // check edge linked list
	fhk_mref fwd;   // return edge linked list
	float k, c;
	fhkX_dsym dsym;
};

// infinity is considered set.
#define cost_isset(x)    ((fu64(x) & 0x7ff8000000000000) <= 0x7ff8000000000000)

/* guards */
struct fhk_mut_guard {
	fhkX_mtag tag;
	uint8_t opcode;
	int32_t order;   // must be next word after tag
	fhk_mref next;  // next guard
	fhk_mref nextV; // unmerged: next guard in var->fwd    merged: the canonical guard
	fhk_mref fwd;   // check edge linked list
	fhk_mref var;   // guarded variable
	fhkX_uvalue arg;
	fhkX_dsym dsym;
};

#define GUARD_UNSET      0xff
#define guard_isset(op)  ((op) != GUARD_UNSET)

/* mutable graph */
struct fhk_mut_graph {
	fhk_mref cap, used, committed;

	// running counters.
	// these are monotonic: layouting won't reset them.
	uint16_t c_group; // group id
	uint16_t c_mapK, c_mapI; // kmap id, imap id

	// linked list heads.
	// nodes are inserted in lifo order.
	fhk_mref var;
	fhk_mref model;
	fhk_mref guard;

	fhkX_dsym_ref dsym;

	// layouter.
	// these are only valid when the layout is recomputed.
	fhkP_smap *maptable;
	uint32_t ne;
	uint32_t nc;
	int32_t bn;
	int32_t bk;
	int32_t bi;
	uint8_t layout_valid;
	fhkP_idxN nz;
	fhkP_idxN nv;
	fhkP_idxN nx;
	fhkP_idxN nm;
	fhkP_group ng;
	fhkP_mapN ni;
	fhkP_mapN nk;

	fhk_mref mem[];
};

#define MGRAPH_FIRSTOBJ      offsetof(struct fhk_mut_graph, mem)
#define mgraph(ref)          (ref)->M
#define mobj_tag(o)          *((fhkX_mtag *)(o))
#define mref_tag(M,r)        mobj_tag(mrefp(M, r))
#define mobjVMG_order(o)     ((struct fhk_mut_var *) o)->order
#define mrefVMG_order(M,r)   mobjVMG_order(mrefp(M,r))
#define mrefVM_gid(M,r)      ((struct fhk_mut_var *) mrefp(M,r))->gid
#define mgraph_maptable(M)   ((M)->maptable + (M)->c_mapI)
#define mgraph_invalidate(M) (M)->layout_valid = 0

NOAPI void fhk_mut_unflag(struct fhk_mut_graph *M);
