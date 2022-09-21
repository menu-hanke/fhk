#pragma once

#include "trace.h"

#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* relative memory references */
typedef int32_t fhk_mref32;
#define mrefp(b,r)   (((void*)(b)) + (ptrdiff_t)(r))  // relative to full pointer
#define pmref(b,p)   ((intptr_t)(p) - (intptr_t)(b))  // full pointer to relative

/* useful macros */
#define min(a, b)         ({ typeof(a) _a = (a); typeof(b) _b = (b); _a < _b ? _a : _b; })
#define max(a, b)         ({ typeof(a) _a = (a); typeof(b) _b = (b); _a > _b ? _a : _b; })
#define uf32(u32)         ((union { float f; uint32_t u; }){.u=(u32)}).f
#define fu32(f32)         ((union { float f; uint32_t u; }){.f=(f32)}).u
#define fu64(f64)         ((union { double f; uint64_t u; }){.f=(f64)}).u
#define LIKELY(x)         __builtin_expect(!!(x), 1)
#define UNLIKELY(x)       __builtin_expect(!!(x), 0)
#define ALIGN(n, m)       ((typeof(n)) (((uintptr_t)(n) + (m) - 1) & ~((uintptr_t)(m) - 1)))
#define F32INF            0x7f800000
#define F32INFN           0xff800000
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
#define DEBUGFUNC         NOAPI __attribute__((section("fhkdbg")))
#define NO_ASAN           __attribute__((no_sanitize_address))

/* ---- indexing ---------------------------------------- */

#define xidx     int64_t
#define xinst    int64_t

/* ---- limits ---------------------------------------- */

#define MAX_PARAM  (1 << 7)
#define MAX_MODEL  (1 << 8)
#define MAX_INST   (1 << 20)

/* ---- debug symbols ---------------------------------------- */

#define FHK_DSYM          (!!TRACE(FHK_TRACE))

/* ---- error values ---------------------------------------- */
/*  +--------+--------+--------+--------+-------+
 *  | 63..58 | 57..55 | 54..52 | 51..32 | 31..0 |
 *  +--------+--------+--------+--------+-------+
 *  |  -code |  tagB  |  tagA  |  infoB | infoA |
 *  +--------+--------+--------+--------+-------+
 *      i6       u3       u3       u20     i32
 */
typedef int64_t fhk_status;

/* ecode values */
enum {
	FHK_ERR_NYI = 1,  // not yet implemented
	FHK_ERR_MEM,      // not enough memory
	FHK_ERR_CYCLE,    // solver found cycle
	FHK_ERR_CHAIN,    // no chain with finite cost
	FHK_ERR_TYPE,     // wrong object type
	FHK_ERR_GROUP,    // map cannot point from group
	FHK_ERR_INVERSE,  // nonsymmetric inverse
	FHK_ERR_WRITE,    // overwrite value
	FHK_ERR_SIZE,     // exceeded max graph size
	FHK_ERR_UNSET,    // unset value
	FHK_ERR_SKIP,     // object was skipped from graph
};

/* etag values */
enum {
	FHK_ETAG_OBJ = 1, // var, model, guard, derive
	FHK_ETAG_INST,    // instance
	FHK_ETAG_EDGE,    // edge
	FHK_ETAG_HANDLE   // handle
};

#define ecode(code)       ((int64_t)((uint64_t)(-(FHK_ERR_##code)) << 58))
#define etagA(f,x)        (((fhk_status)FHK_ETAG_##f << 52) | (uint32_t)(x))
#define etagB(f,x)        (((fhk_status)FHK_ETAG_##f << 55) | (((fhk_status)(x)) << 32))

/* ---- predicates ---------------------------------------- */

/* (operator, operand, sym) */
#define FHK_PREDEF(_)   \
	_(f32le,   float)   \
	_(f32ge,   float)   \
	_(f64le,   double)  \
	_(f64ge,   double)  \
	_(isn,     uint64_t)

#define PRED(operator)   FHK_PRED_##operator

enum {
#define FHK_DEFREDICATE(operator, operand) PRED(operator),
	FHK_PREDEF(FHK_DEFREDICATE)
#undef FHK_DEFREDICATE
	FHK_PRED__num,
};

// won't appear in graph, only used by the builder before the predicate is defined.
#define FHK_PRED__unset  0xff

typedef union fhk_operand {
	float f32;
	double f64;
	uint64_t u64;
} fhk_operand;

/* ---- graph ---------------------------------------- */

/* edge info.
 *            +----------+---------+
 *            |   7      |  6..0   |
 * +----------+----------+---------+
 * | m->v (p) | isderive |  order  |
 * +----------+----------+---------+
 * | m->v (r) |      reverse       |
 * +----------+----------+---------+
 * | m->c     |                    |
 * +----------+----------+---------+
 */
#define edgeP_isderive(info)   ((info) < 0)
#define edgeP_order(info)      ((info) & 0x7f)

typedef struct fhk_edgeX {
	uint16_t idx;
	uint8_t map;
	int8_t info;
} fhk_edgeX;

typedef struct fhk_edgeC {
	uint16_t idx;
	uint8_t map;
	// int8_t info;  // unused for checks
	float penalty;
} fhk_edgeC;

typedef struct fhk_edgeCR {
	fhk_mref32 predicate;
	float penalty;
	uint8_t edge;
	// u8+u16 unused
} fhk_edgeCR;

typedef struct fhk_rcheck {
	float pmax;
	fhk_edgeCR cr[];
} fhk_rcheck;

/*
 * heap entry/edge.
 * note: cost is the least significant 32 bits.
 * only the low 32 bits must be used in heap operations.
 */
typedef union fhk_edgeH {
	struct {
		float c;          // for index < -1: low cost bound, for index = -1: initial delta
		uint16_t idx;     // model index
		uint8_t map;      // v->m map
		uint8_t ei;       // original heap index (note: 0-based. ~(u64)ei is the negative index.)
	};
	uint32_t u32[2];
	uint64_t u64;
} fhk_edgeH;

#define EH_COST   0
#define EH_EDGE   1

typedef struct fhk_var {
	fhk_edgeH heap[0];   // initial heap
	uint32_t cost;       // initial cost   [presolve: true cost]
	uint8_t nh;          // heap size (num of models)
} fhk_var;

#define vheap(v,i)      ((fhk_edgeH *)(v) + (i))

/* predicated guard. */
typedef struct fhk_pregrd {
	// predicate operand is below the guard.
	// (this way we won't have a massive hole in the struct if the operand needs
	// 64-bit alignment.)
	uint8_t operator;
	uint16_t idx;
} fhk_pregrd;

/* raw predicate (for return checks) */
typedef struct fhk_predicate {
	// like guards, operand is below the operator.
	// predicated guards are castable to predicates.
	uint8_t operator;
} fhk_predicate;

/*
 *                                                               derives end here
 *                                                                       |
 *                                                                       v
 * +--------+-------+-----------------+-------------------+--------------+---------+---------------+
 * | checks | model | computed params | pre-solved params | given params | returns | return checks |
 * +--------+-------+-----------------+-------------------+--------------+---------+---------------+
 * ^                                  ^                   ^              ^         ^
 * -e_check                    e_cparam           e_xcparam        e_param  e_return
 *                                                                                 |---------------|
 *                                                                                      n_rcheck
 */
typedef struct fhk_model {
	fhk_edgeC ec[0];              // <-- checks
	float k, c;                   // cost                                   [presolve: k=true cost]
	float ki, ci;                 // cost inverse                                [presolve: unused]
	float bonus;                  // extra delta cost if all checks pass         [presolve: unused]
	uint8_t e_check;              // checks start index (nonpositive, inclusive)      [presolve: 0]
	uint8_t e_cparam;             // computed params end edge (exclusive)
	uint8_t e_xcparam;            // computed+presolved params end edge (exclusive)
	uint8_t e_param;              // params end edge (exclusive)
	uint8_t e_return;             // returns end edge (exclusive)               [derive: e_param+1]
	uint8_t n_rcheck;             // num of return checks                      [derive/presolve: 0]
	fhk_edgeX ex[];               // edges -->
} fhk_model;

#define costf(m, s)     ({ typeof(m) _m = (m); _m->k + _m->c*(s); })
#define costf_inv(m, x) ({ typeof(m) _m = (m); _m->ki + _m->ci*(x); })

/* tag byte. */
// object types. at most one of the following is set (predicated guards have none):
#define TAG_DERIVE        0x80     // derived variable.
#define TAG_COMPUTED      0x40     // true computed variable (not set on derives).
#define TAG_GIVEN         0x20     // given variable.
#define TAG_MODEL         0x10     // true model (not set on derives).
// value types. at most one of the following is set (regular variables have none):
#define TAG_MAP           0x08
#define TAG_GUARD         0x04
// presolved tag, must be combined with derive/computed/model
#define TAG_PRESOLVED     0x02
// group tag.
//   set on variable -> it's the space map of some group.
//   set on model -> it returns the space map of some group.
#define TAG_GROUP         0x01
// masks
#define TAGM_ISMOD        (TAG_DERIVE | TAG_MODEL)
#define TAGM_ISCOMP       (TAG_DERIVE | TAG_COMPUTED)

typedef struct fhk_meta {
	uint8_t tag;
	uint8_t group;
	uint16_t size;
} fhk_meta;

typedef struct fhk_graph {
	uint16_t nx;       // number of xslots
	uint16_t nv;       // number of vslots
	uint8_t j[2];      // jump table offsets
	int8_t kmapg;      // kmapg start index
#if FHK_DSYM
	fhk_mref32 symtab; // -> mref32[] sym table
#endif
} fhk_graph;

#define jidx(i)            ((i)>0xff)

/* special indices. */
#define OBJ_GLOBAL         0
#define OBJ_MAXKMAPG       0x7f
#define OBJ_IDENT          0xff

/*
 *                              +-------+
 *                              | idx[] |
 * +-------+--------+-----------+-------+---------+
 * | sym[] | meta[] | fhk_graph | graph data ...  |
 * +-------+--------+-----------+-----------------+
 *                              ^- fhk_Gref
 */
typedef intptr_t fhk_Gref;

#define grefG(G)           ((fhk_graph *)(G)-1)
#define G2ref(G)           ((fhk_Gref)((fhk_graph *)(G)+1))

#define grefobj(G, idx)    ((void **)(G))[(idx)]
#define grefmeta(G, idxn)  ((fhk_meta *)grefG(G))[(idxn)]
#define grefsym(G, idx)    mrefp((G), (void*)(G)-((fhk_graph *)(G))-)

/* ---- subsets ---------------------------------------- */
/*
 *              +--------+--------+--------+-------+
 *              | 63..52 | 51..32 | 31..20 | 19..0 |
 *  +-----------+--------+--------+--------+-------+
 *  | interval  |    0   |  znum  |    0   | first |
 *  +-----------+--------+--------+--------+-------+
 *  | complex   |          ~ (pk pointer)          |
 *  +-----------+----------------------------------+
 *  | empty set |                -1                |
 *  +-----------+----------------------------------+
 *  | undef set |                -2                |
 *  +-----------+----------------------------------+
 *
 *  note: znum = zero-based size, ie. remaining elements after the first one
 */
typedef int64_t fhk_subset;

#define SUBSET_EMPTY      (-1)
#define SUBSET_UNDEF      (-2)
#define subset_isI(ss)    ((ss) > -1)   // is it a nonempty interval?
#define subset_isE(ss)    ((ss) == -1)  // is it the empty set?
#define subset_isIE(ss)   ((ss) >= -1)  // is it nonempty or interval
#define subset_isU(ss)    ((ss) == -2)  // is it the undefined set?
#define subset_isUE(ss)   ((uint64_t)(ss) >= (uint64_t)(-2)) // is it undefined or empty?
#define subset_isC(ss)    ((ss) < -2)   // is it a complex set?
#define subset_is1(ss)    ((uint64_t)(ss) <= 0xfffff) // is it an interval containing exactly one element?
#define subsetI_first(ss) ((int32_t)(ss))  // note: subsetI_first(SUBSET_EMPTY) = -1
#define subsetI_new(first, zn) ((fhk_subset)(zn)<<32 | (first))
#define subsetIE_znum(ss) ((ss) >> 32)  // note: subsetIE_znum(SUBSET_EMPTY) = -1
#define subsetIE_size(ss) (1 + subsetIE_znum(ss))
#define subsetC_pk(ss)    ((fhk_pkref)~(ss))
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
typedef int8_t *fhk_pkref;
#define pkref_next(pk)    ((pk) + 5)
#define pkref_prev(pk)    ((pk) - 5)
#define pkref_first(pk)   (pkref_load32(pk) & 0xfffff)
#define pkref_znum(pk)    ((pkref_load32((pk)+2) >> 4) & 0xfffff)
#define pkref_size(pk)    (1 + pkref_znum(pk))
#define pkref_more(pk)    ((pkref_load32((pk)+5)) & 0xffffff)
// TODO: pkref_unpack: unpack first/znum with one 64-bit load.

AINLINE static uint64_t pkref_load64(fhk_pkref pk) {
	uint64_t pk64;
	memcpy(&pk64, pk, sizeof(pk64));
	return pk64;
}

AINLINE static uint32_t pkref_load32(fhk_pkref pk) {
	uint32_t pk32;
	memcpy(&pk32, pk, sizeof(pk32));
	return pk32;
}

AINLINE static void pkref_write(fhk_pkref pk, xinst first, xinst znum) {
	pk[0] = first;
	pk[1] = first >> 8;
	pk[2] = (first >> 16) | ((znum & 0xf) << 4);
	pk[3] = znum >> 4;
	pk[4] = znum >> 12;
	// NOTE: another way is to do this write in two parts:
	// *(uint32_t *) pk = first | znum << 20;
	// pk[4] = znum >> 12;
}

/* ---- maps ---------------------------------------- */

#define map_isI(map)      ((int8_t)(map) < 0)
