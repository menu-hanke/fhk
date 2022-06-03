#pragma once

// fhk internal definitions

#include "conf.h"
#include "fhk.h"
#include "trace.h"

#include <assert.h>
#include <stdint.h>
#include <string.h>

/* useful macros */
#define min(a, b)         ({ typeof(a) _a = (a); typeof(b) _b = (b); _a < _b ? _a : _b; })
#define max(a, b)         ({ typeof(a) _a = (a); typeof(b) _b = (b); _a > _b ? _a : _b; })
#define uf32(u32)         ((union { float f; uint32_t u; }){.u=(u32)}).f
#define fu32(f32)         ((union { float f; uint32_t u; }){.f=(f32)}).u
#define fu64(f64)         ((union { double f; uint64_t u; }){.f=(f64)}).u
#define F32_SIGN          0x80000000
#define LIKELY(x)         __builtin_expect(!!(x), 1)
#define UNLIKELY(x)       __builtin_expect(!!(x), 0)
#define ALIGN(n, m)       ((typeof(n)) (((uintptr_t)(n) + (m) - 1) & ~((uintptr_t)(m) - 1)))
#define GUESS_ALIGN(size) min(8, (size))

#if FHK_DEBUG
#include <assert.h>
#define UNREACHABLE()     assert(!"unreachable")
#else
#define UNREACHABLE       __builtin_unreachable
#endif

/* function attributes */
#define AINLINE           __attribute__((always_inline)) inline
#define COLD              __attribute__((cold))
#define NOAPI             __attribute__((visibility("hidden"))) extern
#define ERRFUNC           __attribute__((cold, noinline, noreturn))

/* subsets
 *
 *               +----+--------+--------+-------+
 *               | 63 | 62..43 | 42..20 | 19..0 |
 *  +------------+----+--------+--------+-------+
 *  | interval   | 0  |  znum  |   0    | first |
 *  +------------+----+--------+--------+-------+
 *  | complex    |        ~ (pk pointer)        |
 *  +------------+------------------------------+
 *  | empty set  |             -1               |
 *  +------------+------------------------------+
 *  | undef set  |             -2               |
 *  +------------+------------------------------+
 *
 *  note: znum = zero-based size, ie. remaining elements after the first one
 */
#define SUBSET_EMPTY      (-1)
#define SUBSET_UNDEF      (-2)
#define subset_isI(ss)    ((ss) > -1)   // is it a nonempty interval?
#define subset_isE(ss)    ((ss) == -1)  // is it the empty set?
#define subset_isIE(ss)   ((ss) >= -1)  // is it an empty set or interval?
#define subset_isU(ss)    ((ss) == -2)  // is it undefined?
#define subset_isC(ss)    ((ss) < -2)   // is it a complex subset?
#define subset_isUC(ss)   ((ss) < -1)   // is it complex or undefined?
#define subset_is1(ss)    ((uint64_t)(ss) <= 0xfffff) // is it an interval containing exactly one element?
#define subsetI_newZ(zs,first) ((first) | ((fhk_subset)(zs) << 43))
#define subsetI_first(ss) ((int32_t)(ss))
#define subsetIE_znum(ss) ((ss) >> 43)  // note: subsetIE_znum(SUBSET_EMPTY) = -1
#define subsetIE_size(ss) (1 + subsetIE_znum(ss))
#define subsetC_pk(ss)    ((fhkX_pkref) ~(ss))
#define subsetC_new(pk)   (~(fhk_subset)(pk))

/* packed ranges (PKs)
 *
 * a range is two 20-bit numbers (inst,znum) packed in 40 bits:
 *     +--------+-------+
 *     | 39..20 | 19..0 |
 *     +--------+-------+
 *     |  znum  | first |
 *     +--------+-------+
 *
 * a list of ranges must be terminated with 3 0-bytes.
 */
typedef int8_t *fhkX_pkref;
#define PKWORD_OVERLAP  5
#define PKWORD_FULL     8
#define PKWORD_ALIGN    1
#define pkref_next(pk)  ((pk) + 5)
#define pkref_nth(pk,n) ((pk) + 5*(n))
#define pkref_first(pk) (pkref_load32(pk) & 0xfffff)
#define pkref_znum(pk)  ((pkref_load32((pk)+2) >> 4) & 0xfffff)
#define pkref_size(pk)  (1 + pkref_znum(pk))
#define pkref_more(pk)  ((pkref_load32((pk)+5)) & 0xffffff)

AINLINE static uint64_t pkref_load64(fhkX_pkref pk){
	uint64_t pk64;
	memcpy(&pk64, pk, sizeof(pk64));
	return pk64;
}

AINLINE static uint32_t pkref_load32(fhkX_pkref pk){
	uint32_t pk32;
	memcpy(&pk32, pk, sizeof(pk32));
	return pk32;
}

/* maps
 *
 * each graph has max 256 valid maps.
 * negative maps are instance maps (imaps, value depends on instance),
 * while positive maps are constant maps (kmaps, value doesn't depend on instance).
 *
 * reserved maps:
 *     -128 : identity
 *     [0, maxgroup] : space map
 */
#define MAP_IDENT       (-128)
#define map_isI(map)    ((map) < 0)     // is it any instance map?
#define map_isID(map)   ((map) == -128) // is it the identity map?
#define map_isE(map)    (!map_isID(map)) // map has an associated explicit subset?
#define map_isJ(map)    ((uint8_t)(map) > 128) // is it a user instance map?
#define map_isK(map)    ((map) > 0)     // is it any constant map?
#define map_isL(map,g)  ((map) >= (g))  // is it a user constant map?
#define map_isU(map,g)  (((uint32_t)(map) - (uint32_t)(g)) <= 128) // is it any user map?
#define mapL_toext(map,ng)   ((map) - (ng))
#define mapL_fromext(map,ng) ((map) + (ng))

/* statuses
 *
 * all routines that return a status code (this includes the solver) follow the
 * same protocol:
 *     +-------------+-------------+
 *     |    63..60   |    59..0    |
 *     +-------------+-------------+
 *     | status code | status info |
 *     +-------------+-------------+
 *
 * where status code < 0 -> error
 *                   = 0 -> ok (done)
 *                   > 0 -> yield
 *
 * error returns have the following structure:
 *          +--------+--------+--------+--------+--------+-------+------+
 *          | 63..60 | 59..40 | 39..20 | 19..14 | 13..11 | 10..8 | 7..0 |
 *    +-----+--------+--------+--------+--------+--------+-------+------+
 *    | AB  |   -1   | infoB  | infoA  |    0   |  tagB  | tagA  | code |
 *    +-----+--------+--------+--------+--------+--------+-------+------+
 *    |  E  |   -1   |          info            | TAG_E  |  tag  | code |
 *    +-----+--------+--------------------------+--------+-------+------+
 *
 * solver return values have the following structure:
 *     +---------------+--------+--------+--------+-------+
 *     |    63..60     | 59..36 | 35..32 | 31..16 | 15..0 |
 *     +---------------+--------+--------+--------+-------+
 *     | FHK_OK        |                 0                |
 *     +---------------+-----------------+--------+-------+
 *     | FHKS_SHAPE    |             0            | group |
 *     +---------------+--------+--------+--------+-------+
 *     | FHKS_VREF     |        |       inst      |  idx  |
 *     +---------------+--------+--------+--------+-------+
 *     | FHKS_MAPCALLK |             0            |  map  |
 *     +---------------+--------+--------+--------+-------+
 *     | FHKS_MAPCALLI |        |       inst      |  map  |
 *     +---------------+--------+--------+--------+-------+
 *     | FHKS_MODCALL  |       fhk_modcall pointer        |
 *     +---------------+----------------------------------+
 *
 * builder return values have the following structure:
 *     +--------+--------+---------------+
 *     | 63..60 | 59..32 |     31..0     |
 *     +--------+--------+---------------+
 *     | FHK_OK |   0    | object handle |
 *     +--------+--------+---------------+
 */
#define scode(code)       ((int64_t)(FHKS_##code) << 60)
#define ecode(c)          (((int64_t)FHK_ERROR << 60) | (FHK_ERR_##c))
#define etagA(f,x)        ((FHK_ETAG_##f << 8) | (((fhk_status)(x)&0xfffff) << 20))
#define etagB(f,x)        ((FHK_ETAG_##f << 11) | (((fhk_status)(x)&0xfffff) << 40))
#define etagE(f,x)        ((FHK_ETAG_##f << 8) | (FHK_ETAG_EXT << 11) | ((fhk_status)(x)&0xffffffffffc) << 14)

/* model calls */
#define mcall_params(mc)  (mc)->edges
#define mcall_returns(mc) ((mc)->edges + (mc)->np)

/* nodes
 *
 * index >= 0 -> variable-like (variable or guard)
 *       < 0  -> model
 */
#define idx_isX(idx)      ((idx) >= 0)
#define idx_isM(idx)      ((idx) < 0)

/* groups */
#define GROUP_INVALID     0xff
#define group_isvalid(g)  ((uint32_t)(g) < 0xff)

/* debug syms */
#define FHK_DSYM          (!!TRACE(FHK_TRACE))

struct fhkX_dsym_tab {
	uint32_t cap, used;
	uint8_t mem[];
};

#if FHK_DSYM
typedef struct fhkX_dsym_tab *fhkX_dsym_ref;
typedef uint32_t fhkX_dsym;
#define DSYM_NONE  0
#define DSYM_NOTAB NULL
#define dsym_tabsize(dsref)  (sizeof(*(dsref)) + (dsref)->used)
#else
typedef struct {} fhkX_dsym_ref __attribute__((aligned(1)));
typedef struct {} fhkX_dsym __attribute__((aligned(1)));
#define DSYM_NONE  ((fhkX_dsym){})
#define DSYM_NOTAB ((fhkX_dsym_ref){})
#define dsym_tabsize(...)  0
#endif

/* packed data types */
typedef uint8_t  fhkP_group;  // group
typedef int16_t  fhkP_idx;    // index
typedef uint16_t fhkP_idxN;   // index counter
typedef int32_t  fhkP_inst;   // instance
typedef int8_t   fhkP_map;    // map
typedef uint8_t  fhkP_mapN;   // map counter
typedef int8_t   fhkP_ei;     // edge index
typedef uint8_t  fhkP_eN;     // edge counter

/* labels to make solver code a bit more readable */
#define xgroup   int64_t
#define xidx     int64_t
#define xinst    int64_t
#define xmap     int64_t
#define xedge    int64_t
#define xguard   int64_t

/* limits */
#define MAX_GROUP  0xfe  /* 0xff is invalid */
#define MAX_IDX    0x7fff
#define MIN_IDX    ((fhkP_idx)0x8000)
#define MAX_INST   0xfffff
#define MAX_MAPK   0x7f
#define MIN_MAPI   ((fhkP_map)0x80)
#define MAX_CHECK  0x80
#define MAX_PARAM  0x7f
#define MAX_RETURN 0x7f
#define MAX_MOD    0xff

/* graph structure */

// regular edge: model->var or var->model
typedef struct {
	fhkP_idx idx;
	fhkP_map map;
	uint8_t ex;
} fhk_edge;

// check edge: model->guard
typedef struct {
	fhkP_idx idx;
	fhkP_map map;
	int8_t flags;
	float penalty;
} fhk_check;

#define CHECK_COMPUTED  0x80
#define check_isC(f)    ((f) & CHECK_COMPUTED)

// models
// checks:              checks  [p_check, 0)
// computed parameters: params  [0, p_cparam)            ex: original edge index
// given parameters:    params  [p_cparam, p_param)      ex: original edge index
// returns:             returns [0, p_return)            ex: reverse edge index
struct fhk_model {
	union {
		fhk_edge *params;
		fhk_check *checks;
	};
	fhkP_group group;
	fhkP_ei p_check;
	fhkP_ei p_cparam;
    fhkP_ei p_param;
	fhkP_ei p_return;
	// uint8_t unused
	// uint16_t unused
	float k, c;
	float ki, ci;
	float cmin;
	// uint32_t unused
	fhk_edge *returns;
	fhkX_dsym dsym;
};

#define edgeR_reverse(e) ((e).ex)
#define edgeP_order(e)   ((e).ex)

#define costf(m, s) ({ typeof(m) _m = (m); _m->k + _m->c*(s); })
#define costf_inv(m, x) ({ typeof(m) _m = (m); _m->ki + _m->ci*(x); })

// variables.
struct fhk_var {
	fhk_edge *models;          // ex: unused
	fhkP_eN n_mod;
	fhkP_group group;
	uint16_t size;
	fhkX_dsym dsym;
} __attribute__((packed));

// note: use these macros only for debug assertions.
// use the edge ordering for algorithms.
#define var_isG(x) (!(x)->n_mod)  // is it given?
#define var_isC(x) (!var_isG(x))  // or is it computed?

// guards
typedef fhk_gvalue fhkX_uvalue __attribute__((aligned(1)));

struct fhk_guard {
	fhkX_uvalue arg;
	uint8_t opcode;
	fhkP_group group;
	fhkP_idx xi;
	fhkX_dsym dsym;
} __attribute__((packed));

struct fhk_graph {
	struct fhk_model models[0];

	fhkP_idxN nv; // variable count
	fhkP_idxN nx; // variable-like count (variables+guards)
	fhkP_idxN nm; // model count
	fhkP_group ng;  // group count
	fhkP_mapN nk; // constant map count (including groups)
	fhkP_mapN ni; // nonconstant map count
	fhkP_group *assoc_mapJ; // nonconstant umap source group association

	fhkX_dsym_ref dsym;

	union {
		struct fhk_guard guards[0];
		struct fhk_var vars[0];
	};
};

/* mutable graphs */

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
#define mhandleT(h)         ((uint32_t)(h) >> 28)
#define mhandleV(h)         (((h) << 4) >> 4)  /* sign-extended */
#define mhandleU(h)         ((h) & 0x0fffffff)   /* unsigned */
#define mhandle_isref(h)    ((h) >= 0)
#define mhandle_ismapL(h)   ((h) < (fhk_mhandle)0x88000000) /* L-map (user defined constant map) */
#define mhandle_ismapJ(h)   (((uint32_t)(h) >> 27) == 0x11) /* J-map (user defined nonconstant map) */
#define mhandle_isgroup(h)  (mhandleT(h) == 0x9) /* group/space map */
#define mhandle_ismapu(h)   ((h) < (fhk_mhandle)0x90000000) /* any user defined map */
#define mhandle_ismapss(h)  ((h) < (fhk_mhandle)0xafffffff) /* any map with an associated subset */
#define mhandle_ismap(h)    ((h) < (fhk_mhandle)0xb0000000) /* any map */
#define mhandle_istarget(h) ((h) == FHK_MHANDLE_SPACE) /* target space pseudo-map */
#define mhandle_isident(h)  ((h) == FHK_MHANDLE_IDENT) /* ident pseudo-map */
#define mhandle_newT(t)     ((uint32_t)(t) << 28)
#define mhandle_newV(v)     ((v) & 0x0fffffff)
#define mhandle_newmapL(m)  (mhandle_newT(0x8) | (m))
#define mhandle_newmap(m)   (mhandle_newT(0x8) | mhandle_newV(m))
#define mhandle_newgroup(g) (mhandle_newT(0x9) | (g))

/* mhandle2 packs */
#define mhandle2_lo(h2)     ((fhk_mhandle)(h2))
#define mhandle2_hi(h2)     ((fhk_mhandle)((h2) >> 32))

/* mut-graph reference.
 * this mut always point to an mtag.  */
typedef int32_t fhkX_mref;

/* edges */
struct fhk_mut_edge {
	fhkX_mtag tag;
	fhk_mhandle mapMV;
	fhk_mhandle mapVM;
	fhkX_mref nextV; // next edge in var->back or var->fwdM
	fhkX_mref nextM; // next edge in model->backV or model->fwd
	fhkX_mref var;
	fhkX_mref model;
};

/* checks.
 * layout must match fhk_mut_edge.
 */
struct fhk_mut_check {
	fhkX_mtag tag;
	fhk_mhandle mapMG;
	fhk_mhandle mapGM;
	fhkX_mref nextG; // next edge in guard->fwd
	fhkX_mref nextM; // next edge in model->back
	fhkX_mref guard;
	fhkX_mref model;
	float penalty;
};

/* variables */
struct fhk_mut_var {
	fhkX_mtag tag;
	uint16_t gid;   // must be after tag
	int32_t order;  // must be after gid
	float clo, chi; // must be after order
	uint16_t size;
	fhkX_mref next; // next variable
	fhkX_mref back; // model edge linked list
	fhkX_mref fwdM; // model edge linked list
	fhkX_mref fwdG; // guard linked list
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
	fhkX_mref next;  // next model
	fhkX_mref backV; // parameter edge linked list
	fhkX_mref backC; // check edge linked list
	fhkX_mref fwd;   // return edge linked list
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
	fhkX_mref next;  // next guard
	fhkX_mref nextV; // unmerged: next guard in var->fwd    merged: the canonical guard
	fhkX_mref fwd;   // check edge linked list
	fhkX_mref var;   // guarded variable
	fhkX_uvalue arg;
	fhkX_dsym dsym;
};

#define GUARD_UNSET      0xff
#define guard_isset(op)  ((op) != GUARD_UNSET)

/* mutable graph */
struct fhk_mut_graph {
	fhkX_mref cap, used, committed;

	// running counters.
	// these are monotonic: layouting won't reset them.
	uint16_t c_group; // group id
	uint16_t c_mapK, c_mapI; // kmap id, imap id

	// linked list heads.
	// nodes are inserted in lifo order.
	fhkX_mref var;
	fhkX_mref model;
	fhkX_mref guard;

	fhkX_dsym_ref dsym;

	// layouter.
	// these are only valid when the layout is recomputed.
	fhkP_map *maptable;
	uint32_t ne;
	uint32_t nc;
	uint8_t layout_valid;
	fhkP_idxN nv;
	fhkP_idxN nx;
	fhkP_idxN nm;
	fhkP_group ng;
	fhkP_mapN ni;
	fhkP_mapN nk;

	fhkX_mref mem[];
};

#define MGRAPH_FIRSTOBJ      offsetof(struct fhk_mut_graph, mem)
#define mgraph(ref)          (ref)->M
#define mref_ptr(M,r)        ((void *)((intptr_t)(M) + (r)))
#define ptr_mref(M,p)        ((intptr_t)(p) - (intptr_t)(M))
#define mobj_tag(o)          *((fhkX_mtag *)(o))
#define mref_tag(M,r)        mobj_tag(mref_ptr(M, r))
#define mobjVMG_order(o)     ((struct fhk_mut_var *) o)->order
#define mrefVMG_order(M,r)   mobjVMG_order(mref_ptr(M,r))
#define mrefVM_gid(M,r)      ((struct fhk_mut_var *) mref_ptr(M,r))->gid
#define mgraph_maptable(M)   ((M)->maptable + (M)->c_mapI)
#define mgraph_invalidate(M) (M)->layout_valid = 0

NOAPI void fhk_mut_unflag(struct fhk_mut_graph *M);
