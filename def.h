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
#define GUESS_ALIGN(size) min((typeof(size))8, (size))

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

/* maps:
 *   -128..-2    user imaps
 *         -1    identity
 *      0..ng    group space maps
 *  ng+1..127    user kmaps
 */
#define MAP_IDENT       (-1)
#define map_zext(map)   ((uint8_t) (map))            // signed -> unsigned
#define map_sext(map)   ((int8_t) (map))             // unsigned -> signed
#define map_isI(map)    (map_sext(map) <= MAP_IDENT) // is it an i-map?
#define map_isJ(map)    (map_sext(map) < MAP_IDENT)  // is it a user-defined i-map?
#define map_isK(map)    (map_sext(map) >= 0)         // is it a k-map?

/* error status structure:
 *  +--------+--------+--------+--------+-------+
 *  | 63..58 | 57..55 | 54..52 | 51..32 | 31..0 |
 *  +--------+--------+--------+--------+-------+
 *  |  -code |  tagB  |  tagA  |  infoB | infoA |
 *  +--------+--------+--------+--------+-------+
 *      i6       u3       u3       u20     i32
 */

/* ecode values */
enum {
	// input validation errors
	FHK_ERR_BOUND = 1, // s b    index (node/map/instance/group) out of bounds
	FHK_ERR_INVAL,     // s      invalid user value
	FHK_ERR_GIVEN,     // s      expected given variable
	// semantic errors
	FHK_ERR_NOVALUE,   // s      value expected but missing
	FHK_ERR_WRITE,     // s b    overwrite readonly value
	FHK_ERR_MAPASSOC,  //   b    map not associated with unique group
	FHK_ERR_UNSET,     //   b    unset value
	FHK_ERR_NOLAYOUT,  //   b    layout not computed
	// operational errors
	FHK_ERR_NYI,       // s      not yet implemented
	FHK_ERR_DEPTH,     // s      solver stack overflow
	FHK_ERR_CHAIN,     // sp     no chain with finite cost
	FHK_ERR_MEM,       // s b    failed to allocate memory
};

/* etag values */
enum {
	FHK_ETAG_NODE = 1, // var, model or guard
	FHK_ETAG_MAP,      // imap or kmap
	FHK_ETAG_INST,     // instance
	FHK_ETAG_GROUP,    // group
	FHK_ETAG_EDGE,     // edge index
	FHK_ETAG_HANDLE    // mgraph handle
};

#define ecode(code)       ((uint64_t)(-(FHK_ERR_##code)) << 58)
#define etagA(f,x)        (((fhk_status)FHK_ETAG_##f << 52) | (uint32_t)(x))
#define etagB(f,x)        (((fhk_status)FHK_ETAG_##f << 55) | (((fhk_status)(x)) << 32))

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

/* memory references */
typedef int32_t  fhk_mref;  // relative memory reference
typedef uint16_t fhk_sref;  // short memory reference (note sign!)
#define mrefp(b,r) (((void*)(b)) + (ptrdiff_t)(r))  // mem ref to pointer
#define pmref(b,p) ((intptr_t)(p) - (intptr_t)(b))  // pointer to mem ref

/* packed data types */
typedef uint8_t  fhkP_group;  // group
typedef int16_t  fhkP_idx;    // index
typedef uint16_t fhkP_idxN;   // index counter
typedef int32_t  fhkP_inst;   // instance
typedef uint8_t  fhkP_map;    // map
typedef int8_t   fhkP_smap;   // signed map
typedef uint8_t  fhkP_mapN;   // map counter
typedef int8_t   fhkP_ei;     // edge index
typedef uint8_t  fhkP_eN;     // edge counter

/* labels to make solver code a bit more readable */
#define xgroup   int64_t
#define xidx     int64_t
#define xinst    int64_t
#define xmap     uint64_t     // unsigned, always zero-extend maps.
#define xedge    int64_t
#define xguard   int64_t

/* limits */
#define MAX_IDX    0x7fff
#define MIN_IDX    ((fhkP_idx)0x8000)
#define MAX_INST   0xfffff
#define MAX_MAPK   0x7f
#define MIN_MAPI   ((int8_t)0x80)
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
	uint8_t exp;               // default expand flag?
	uint8_t fwdj;              // have a forward j-map?
	// uint8_t unused
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
#define var_isG(x)   (!(x)->n_mod)  // is it given?
#define var_isC(x)   (!var_isG(x))  // or is it computed?

// guards
typedef fhk_gvalue fhkX_uvalue __attribute__((aligned(1)));

struct fhk_guard {
	fhkX_uvalue arg;
	uint8_t opcode;
	fhkP_group group;
	fhkP_idx xi;
	fhkX_dsym dsym;
} __attribute__((packed));

enum {
	FHK_GUARD_F32_GE,
	FHK_GUARD_F32_LE,
	FHK_GUARD_F64_GE,
	FHK_GUARD_F64_LE,
	FHK_GUARD_U8_M64,
	FHK_GUARD__MAX
};

struct fhk_graph {
	struct fhk_model models[0];
	fhkP_group *mapg;  // imap -> group lookup table
	int32_t bn;        // node(var+model) index bias   = 2+nm
	int32_t bk;        // mapk index bias              = 2+nm+nz
	int32_t bi;        // mapi index bias              = 2+nm+nz+nk+ni
	fhkP_idxN nz;      // given variable count
	fhkP_idxN nv;      // variable count
	fhkP_idxN nx;      // variable-like count (variables+guards)
	fhkP_idxN nm;      // model count
	fhkP_group ng;     // group count
	fhkP_mapN nk;      // constant map count (including groups)
	fhkP_mapN ni;      // nonconstant map count (including ident)
	fhkX_dsym_ref dsym;
	union {
		struct fhk_guard guards[0];
		struct fhk_var vars[0];
	};
};
