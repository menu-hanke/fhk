#pragma once

#include "def.h"

#include <stdint.h>

/* ---- layouting ---------------------------------------- */

// increase as needed, see layout_order()
#define LAYOUT_MAXHOLE     5
#define LAYOUT_MAXINTERVAL 3

/* layout classes */
#define LC_NONE            0xff     // not layouted
#define LC_KMAPG           0        // given k-map
#define LC_KMAPD           1        // derived k-map
#define LC_KMAPC           2        // computed k-map
#define LC_IMAPG           3        // given i-map
#define LC_IMAPD           4        // derived i-map
#define LC_IMAPC           5        // computed i-map
#define LC_GIVEN           6        // given variable
#define LC_DERIVE          7        // derived model (derived variables get LC_NONE)
#define LC_NDMODEL         8        // nonderived model
#define LC_COMPUTED        9        // computed variable
#define LC__NUM            10

typedef struct fhk_layout_state {
	uint16_t start[LC__NUM][LAYOUT_MAXINTERVAL];
	uint16_t end[LC__NUM][LAYOUT_MAXINTERVAL];
	uint8_t curi[LC__NUM];
	uint16_t cursor[LC__NUM];
	uint16_t n[LC__NUM];
} fhk_layout_state;

/* ---- graph building ---------------------------------------- */

#define MUT_OBJDEF(_)               \
	_(var,       fhk_mut_var)       \
	_(model,     fhk_mut_model)     \
	_(predicate, fhk_mut_predicate) \
	_(rcheck,    fhk_mut_retcheck)  \
	_(check,     fhk_mut_check)     \
	_(edgeP,     fhk_mut_edge)      \
	_(edgeR,     fhk_mut_edge)

#define MTYPE(t) FHK_MTYPE_##t

enum {
#define MUT_DEFTYPE(t, _) MTYPE(t),
	MUT_OBJDEF(MUT_DEFTYPE)
#undef MUT_DEFTYPE
	FHK_MTYPE__num
};
#define mtype_isobj(t)  ((t) <= MTYPE(model))

/* tags */
typedef uint16_t fhk_mtag;
#define MTAG_TYPE      0x0007   // type mask, see MTYPE(...)
#define MTAG_MAP       0x0008   // variable is a map.
#define MTAG_GUARD     0x0010   // variable is a guard.
#define MTAG_VARTYPE   (MTAG_TYPE|MTAG_MAP|MTAG_GUARD)
#define MTAG_PREGRD    0x0020   // variable is a guard with a builtin predicate.
#define MTAG_DERIVE    0x0040   // var or model is derived.
#define MTAG_SKIP      0x0100   // object will not be included in graph
#define MTAG_SKIPNEXT  0x0200   // skip if not cleared
#define MTAG_IDX       0x0400   // object has a layouted index
#define MTAG_RETAIN    0x0800   // retain in graph, but does not imply recursively marked
#define MTAG_MARKREC   0x1000   // recursively marked
#define MTAG_MARK      (MTAG_RETAIN|MTAG_MARKREC)

typedef struct fhk_mut_edge {
	fhk_mtag tag;
	fhk_mref32 mapMV;     // model->var map                                 --> mut var
	fhk_mref32 nextV;     // next edge in var->back or var->fwdM            --> mut edge
	fhk_mref32 nextM;     // next edge in model->backV or model->fwdR       --> mut edge
	fhk_mref32 var;       // the variable                                   --> mut var
	fhk_mref32 model;     // the model                                      --> mut model
} fhk_mut_edge;

// note: fhk_mut_check must be castable to fhk_mut_edge
typedef struct fhk_mut_check {
	fhk_mtag tag;
	fhk_mref32 mapMV;     // model->guard map                               --> mut var
	fhk_mref32 nextV;     // next edge in var->fwdC                         --> mut check
	fhk_mref32 nextM;     // next edge in model->backC                      --> mut check
	fhk_mref32 guard;     // the guard                                      --> mut var
	fhk_mref32 model;     // the model                                      --> mut model
	float penalty;        // penalty if guard failed
} fhk_mut_check;

typedef struct fhk_mut_retcheck {
	fhk_mtag tag;
	fhk_mref32 edge;      // return edge                                    --> mut edge
	fhk_mref32 nextM;     // next edge in model->fwdRC                      --> mut retcheck
	fhk_mref32 predicate; // predicate                                      --> mut predicate
	fhk_mref32 model;     // the model                                      --> mut model
	float penalty;        // penalty if check failed
} fhk_mut_retcheck;

#if FHK_DSYM
#define MUT_OBJ_SYM fhk_mref32 sym, symofs;
#else
#define MUT_OBJ_SYM
#endif

#define MUT_OBJ_HEADER \
	fhk_mtag tag;      \
	uint8_t lc;        \
	uint16_t idx;      \
	fhk_mref32 group;  \
	MUT_OBJ_SYM        \
	float clo, chi

typedef struct fhk_mut_obj {
	MUT_OBJ_HEADER;
} fhk_mut_obj;

typedef struct fhk_mut_var {
	MUT_OBJ_HEADER;
	uint8_t nm;           // number of models                               (layout)
	uint16_t size;        // variable size (bytes)
	fhk_mref32 offset;    // offset in graph (only computed vars)           (layout)
	fhk_mref32 next;      // next variable                                  --> mut var
	fhk_mref32 back;      // model back list / guarded var (guards)         --> mut edge | mut var
	fhk_mref32 fwdM;      // model forward list head                        --> mut edge
	union {
		fhk_mref32 predicate; // predicate (predicated guards only)         --> mut predicate
		fhk_mref32 inverse;  // inverse map (maps only)                     --> mut var
	};
} fhk_mut_var;

typedef struct fhk_mut_model {
	MUT_OBJ_HEADER;
	fhk_mref32 offset;    // position in graph                              (layout)
	fhk_mref32 next;      // next model                                     --> mut model
	fhk_mref32 backV;     // parameter edge list head                       --> mut edge
	fhk_mref32 backC;     // check edge list head                           --> mut check
	fhk_mref32 fwdR;      // return edge list head                          --> mut edge
	fhk_mref32 fwdRC;     // return check list head                         --> mut retcheck
	float k, c;           // cost
	uint8_t nc;           // number of checks                               (layout)
	uint8_t np;           // number of parameters                           (layout)
	uint8_t nr;           // number of returns                              (layout)
	uint8_t nrc;          // number of return checks                        (layout)
} fhk_mut_model;

typedef union fhk_v64 {
	uint64_t u64;
	float f32;
	double f64;
} fhk_v64;

typedef struct fhk_mut_predicate {
	fhk_mtag tag;
	uint8_t operator;     // operator (see def.h)
	fhk_mref32 link;      // next or interned predicate                     (layout)
	fhk_operand operand;  // operand. unused bits are always zeroed, so these can be compared with memcmp
} fhk_mut_predicate;

typedef struct fhk_mut_graph {
	fhk_mref32 ucap, uused; // allocated/used memory UP
	fhk_mref32 dcap, dused; // allocated/used memory DOWN
	fhk_mref32 var;         // variable linked list head                            --> mut var
	fhk_mref32 model;       // model linked list head                               --> mut model
	float k, c;             // initial cost params
	fhk_mref32 hole[LAYOUT_MAXHOLE];   // hole offset (from objtable base)                 (layout)
	fhk_mref32 endhole[LAYOUT_MAXHOLE]; // hole end offset (from objtable base)            (layout)
	fhk_mref32 tail;        // alloc tail (from objtable base)                             (layout)
	fhk_mref32 symtab;      // symtab offset (from G)                                      (layout)
	uint16_t nx;            // solver xtable size: total layouted objects                  (layout)
	uint16_t nv;            // solver vtable size: tail models excluded                    (layout)
	uint16_t nlc[LC__NUM];  // object count by layout class                                (layout)
	uint8_t j[2];           // jump table offsets                                          (layout)
	int8_t kmapg;           // given k-map offset                                          (layout)
	fhk_mref32 mem[];       // memory (defined as mref32 for alignment)
} fhk_mut_graph;

typedef struct fhk_mut_ref {
	fhk_mut_graph *mp;
} fhk_mut_ref;

// the order [ident -> global -> user] is important.
#define MREF_START              offsetof(fhk_mut_graph, mem)
#define MREF_IDENT              MREF_START
#define MREF_GLOBAL             (MREF_IDENT + sizeof(fhk_mut_var))
#define MREF_USER               (MREF_GLOBAL + sizeof(fhk_mut_var))

#define MSIZE_UNSET             ((uint16_t)-1)

#define mrefM(r)                (r)->mp

/* ---- analysis ---------------------------------------- */

/*
 * prune bound info.
 *   +-------------------------------+------------+
 *   |             cost              |    state   |
 *   +-------+-----------+-----------+----+-------+
 *   | 63(s) | 62..55(e) | 54..32(m) | 31 | 30..0 |
 *   +-------+-----------+-----------+----+-------+
 *   |   0   |  cost low/high bound  | hi | mref  |
 *   +-------+-----------------------+----+-------+
 */
typedef uint64_t fhk_bound;

/* dynamic bound heap. */
typedef struct fhk_bheap {
	uint32_t used, cap;
	fhk_bound heap[];
} fhk_bheap;

typedef fhk_bheap *fhk_heapref;

#define bheap_data(ref)         ((ref)->heap-1)
#define bound_newL(cost, ref)   (((fhk_bound)fu32(cost) << 32) | (ref))
#define bound_newH(cost, ref)   (((fhk_bound)fu32(cost) << 32) | (ref) | 0x80000000)
#define bound_isH(bound)        ((int32_t)(bound) < 0)
#define bound_ref(bound)        ((uint32_t)(bound) & 0x7fffffff)
#define bound_ucost(bound)      ((bound) >> 32)
#define isfinitecx(cx)          (fu32(cx) < F32INF)

/* ---- queries ---------------------------------------- */

/*
 * +--------+-------+
 * | 63..32 | 31..0 |
 * +--------+-------+
 * | index  | jump  |
 * +--------+-------+
 */
typedef uint64_t fhk_query;
#define QUERY_PRUNED            ((fhk_query)(-1))
#define query_newJ(idx,j)       (((fhk_query)(idx) << 32) | (j))
#define query_newI(idx)         query_newJ(idx, 0xffffffff)
