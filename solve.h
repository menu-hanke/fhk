#pragma once

#include "co.h"
#include "conf.h"
#include "def.h"
#include "fhk.h"
#include "trace.h"
#include "vm.h"

#include <stdint.h>
#include <string.h>

/* iterators
 *
 * +----+--------+----+--------+--------+-------+
 * | 63 | 62..43 | 42 | 41..32 | 31..20 | 19..0 |
 * +----+--------+----+--------+--------+-------+
 * | 0  | remain | cm |   0    |   0    | inst  |
 * +----+--------+----+--------+--------+-------+
 *
 * note: cm = complex mark: is this a complex subset iterator with more intervals left?
 */
typedef int64_t fhkX_iter;
#define ITER_STEP         0xfffff80000000001ll   /* decrement remain and increment inst */
#define ITER_CM           (1LL << 42)
#define iter_stepN(it,n)  ((fhkX_iter)((uint64_t)(it) + (uint64_t)(n)*ITER_STEP))
#define iter_step(it)     iter_stepN((it),1)
#define iter_inst(it)     ((int32_t)(it))
#define iter_remain(it)   ((it) >> 42)
#define iter_moreI(it)    ((it) >= 0) /* more in this interval? */
#define iter_moreC(it)    ((it) & ITER_CM) /* more intervals? this works on any iterator */
#define iter0_moreA(it)   ((it) > 0xfffff) /* more anything? this works on remain >= 0 */

AINLINE static fhkX_iter pkref_iter_first(fhkX_pkref pk){
	uint64_t pk64 = pkref_load64(pk);
	return (pk64 & 0xfffff) | ITER_CM | ((pk64 & 0xfffff00000) << 23);
}

AINLINE static fhkX_iter pkref_iter_next(fhkX_pkref pk){
	uint64_t pk64 = pkref_load64(pk);
	return (pk64 & 0xfffff) | (((uint64_t)!!(pk64 > 0xffffffffff)) << 42) | ((pk64 & 0xfffff00000) << 23);
}

/* search state
 *
 *                       +-------------------------------------+-------------------------------+
 *                       |                state                |             cost              |
 *                       +----+----+----+----+--------+--------+-------+-----------+-----------+
 *                       | 63 | 62 | 61 | 60 | 59..40 | 39..32 | 31(s) | 30..32(e) | 22..0 (m) |
 * +---------------------+----+----+----+----+--------+--------+-------+-----------+-----------+
 * | var/searching       |    |    |    |           0          |   1   |     0     |     0     |
 * +---------------------+ 0  | 0  | e  +----------------------+-------+-----------+-----------+
 * | var/no chain        |    |    |    |           0          |       |                       |
 * +---------------------+----+----+----+----+--------+--------+       |                       |
 * | var/chain+no value  |    | 0  |    |    |        |        |   0   |     cost low bound    |
 * +---------------------+ 1  +----+ 1  |    |  inst  |  edge  |       |                       |
 * | var/chain+value     |    | 1  |    |    |        |        |       |                       |
 * +=====================+====+====+====+====+========+========+=======+=======================+
 * | mod/no chain        | 0  |    | e  |                      |       |                       |
 * +---------------------+----+ 0  +----+                      |       |                       |
 * | mod/chain+no value  |    |    |    |          0           |   0   |     cost low bound    |
 * +---------------------+ 1  +----+ 1  |                      |       |                       |
 * | mod/chain+value     |    |  1 |    |                      |       |                       |
 * +---------------------+----+----+----+----------------------+-------+-----------------------+
 *
 * notes: * the same representation is currently shared for models/vars, but this isn't necessary.
 *        * the order of fields is very important here (and only works on little-endian, TODO?)
 *        * the most important invariant here is that truecost >= sp->cost, always for every node.
 *        * e = expanded flag
 */
typedef union {
	struct {
		float cost;
		uint32_t state;
	};
	uint64_t u64;
} fhkX_sp;

#define SP_CHAIN_BIT      31
#define SP_VALUE_BIT      30
#define SP_EXPANDED_BIT   29
#define SP_CHAIN          (1ULL << SP_CHAIN_BIT)
#define SP_VALUE          (1ULL << SP_VALUE_BIT)
#define SP_EXPANDED       (1ULL << SP_EXPANDED_BIT)
#define SP_FLAGS          (SP_CHAIN|SP_VALUE|SP_EXPANDED)
#define SP_MARK           uf32(F32_SIGN)
#define sp_new(s,c)       ((fhkX_sp){.state=(s), .cost=(c)})
#define sp_checkC(state)  ((state) & SP_CHAIN)
#define sp_checkV(state)  ((state) & SP_VALUE)
#define sp_checkE(state)  ((state) & SP_EXPANDED)
#define sp_checkM(sp)     ((sp).u64 & F32_SIGN)
#define sp_done(sp)       (((sp).u64 & ((1ULL << (32+SP_CHAIN_BIT)) | (uint32_t)~F32_SIGN)) >= fu32(FHK_MAX_COST))
#define spV_inst(state)   (((state) >> 8) & 0xfffff)
#define spV_edge(state)   ((state) & 0xff)
#define spV_newchain(i,e) (((i) << 8) | (e))

/* bitmaps */
typedef union { uint64_t u64; uint32_t u32[2]; } fhkX_bmword;
typedef fhkX_bmword *fhkX_bitmap;
#define bitmap_ref32(bm)  ((uint32_t *) (bm))
#define bitmap_ref64(bm)  ((uint64_t *) (bm))
#define bitmap_idx32(i)   ((i)>>5)
#define bitmap_shift32(i) ((i)%32)
#define bitmap_idx64(i)   ((i)>>6)
#define bitmap_shift64(i) ((i)%64)
#define bitmap_is1(bm,i)  (!!((bitmap_ref32(bm)[bitmap_idx32(i)])&(1<<bitmap_shift32(i))))
#define bitmap_is0(bm,i)  (!bitmap_is1(bm,i))
#define bitmap_size(n)    (8*(((n)+63)/64))
#define bitmapW_ffs32     __builtin_ctz
#define bitmapW_ffs64     __builtin_ctzll
#define bitmapW_64(x)     ((fhkX_bmword){.u64=(x)})
#define bitmapW_ones64(n) ((1LL << (n)) - 1)
#define bitmapW_zeros64(n)  ((~(uint64_t)0) << (n))
#define bitmapW_test64(w,j) (!!((w) & (1LL << (j))))

/* check bitmaps
 *
 * these are just bitmaps zipped like this:
 *     [ pass word1 ] [ eval word1 ] ... [ pass wordN ] [ eval wordN ]
 */
typedef fhkX_bmword fhkX_checkword;
typedef fhkX_checkword *fhkX_checkmap;
#define checkmap_refP(cm)     (cm)
#define checkmap_refE(cm)     ((cm)+1)
#define checkmap_checkP(cm,i) (!!(bitmap_ref64(cm)[2*bitmap_idx64(i)]&(1LL<<bitmap_shift64(i))))
#define checkmap_checkE(cm,i) (!!(bitmap_ref64(cm)[2*bitmap_idx64(i)+1]&(1LL<<bitmap_shift64(i))))

/* work stack */

typedef struct {
	int16_t idx;
	int16_t ei;
} fhkX_candinfo;

struct fhkX_cselector {
	fhkX_iter it;        // iterator
	fhkX_pkref pk;       // pk if iterator is complex
	fhkX_sp *sp;         // precomputed sp start
	fhkX_candinfo info;  // candidate info
};

struct fhkX_work {
	struct fhkX_cselector sel[0]; // candidate selectors go below this
	fhkX_sp *sp;         // variable sp
	void *edge;          // active edge
	fhkX_iter it;        // active iterator
	fhkX_pkref pk;       // active iterator pk
	fhkX_candinfo cinfo; // candidate info
	fhkP_inst cinst;     // this candidate instance
	float CI;            // saved CI
	float BI;            // saved BI
	float B;             // high bound (beta)
	float ecost;         // accumulated edge cost (parameter only)
	fhk_sref prev;       // previous frame link
	int16_t cnum;        // number of candidates
	int8_t where;        // param/check
#if FHK_TRACEON(solver)
	fhkP_idx idx;        // (debug) variable index
	fhkP_inst inst;      // (debug) variable instance
#endif
};

#define WHERE_CHECK   (-1)
#define WHERE_PARAM   0
#define where_isC(w)  ((w) < 0)
#define where_isP(w)  ((w) == 0)

/* mapping state */
typedef union {
	fhk_subset *imap;
	fhk_subset kmap;
} fhkX_anymap;

#define ANYMAP_UNDEF        ((fhkX_anymap){.kmap=SUBSET_UNDEF})
#define anymap_isU(am)      subset_isU((am).kmap)
#define anymapK(am)         (am).kmap
#define anymapI(am)         (am).imap
#define anymapII(am,inst)   (am).imap[(inst)]

/* scatter info */

struct fhkX_sbuf {
	int32_t size;
	fhk_mref vp;
	fhk_mref off;
};

struct fhkX_scatter {
	int32_t num;
	fhk_mref next;
	fhk_mref data;
	struct fhkX_sbuf sbuf[];
	// uint8_t data[...]
};

struct fhkX_scatter_state {
	struct fhk_mem *mem;
	void *mp;
	fhk_mref *prev;
	fhk_mref next;
	fhk_mref vp;
	fhkP_idx idx;
	uint16_t size;
	uint32_t templ;
};

#define scatter_prev(sct) ((struct fhkX_scatter *) (((void *)(sct)->prev)-offsetof(struct fhkX_scatter, next)))

/* value state */
typedef union {
	uint8_t *m; // models: 0 -> value not expanded, 1 -> value expanded
	void **v;   // vars: value buffer
} fhkX_valueref;

#define valueM(r,i)  (r).m[(i)]
#define valueV(r,i)  (r).v[(i)]

/* shared solver memory.
 *
 *   +------------------------------------- contiguous mmap --------------------------+
 *   |                                                                                |
 *   |                   +----------- single contiguous allocation -------------+     |
 *   |                   |                                                      |     |
 *   v                   v                                                      v     v
 *   +-----+-------+-----+----------------+--------+--------+--------+----------+-----+
 *   | map | ident | ... | <-- call stack | stateM | solver | stateV | work --> | ... |
 *   +-----+-------+-----+----------------+--------+--------+--------+----------+-----+
 *   ^     ^                               ^
 *   |     |                               |
 *   |     +--- interned ident map         |
 *   |                                     |
 *   +-- struct fhk_mem *                  +--- struct fhk_solver *
 *
 * the pointer can be copied and restored to rollback to restore state if no solver functions
 * have been called on any solver that was created before the copy was made. */
struct fhk_mem {
	fhkX_vmmap map;     // memory mapping
	fhkP_inst ident;    // ident map size
	fhk_mref ptr;       // alloc pointer
	fhk_subset ip[];    // ident map
};

/* model calls */
typedef struct fhk_cedge {
	void *p;
	size_t n;
} fhk_cedge;

/* root slots
 *
 *  +--------+--------+-------+------+
 *  | 63..48 | 47..28 | 27..8 | 7..0 |
 *  +--------+--------+-------+------+
 *  |  idx   | start  | znum  | buf  |
 *  +--------+--------+-------+------+
 */
typedef int64_t fhkX_root;
#define MAX_ROOT            0xff
#define root_znum(r)        (((r) >> 8) & 0xfffff)
#define root_size(r)        (1 + root_znum(r))
#define root_start(r)       (((r) >> 28) & 0xfffff)
#define root_buf(r)         ((uint8_t)(r))
#define root_idx(r)         ((r) >> 48)
#define root_newidx(idx)    ((fhkX_root)(idx) << 48)
#define root_newsubsetI(ss) (((ss) << 28) | ((ss) >> 35))
#define root_newpk(pk)      ({ uint64_t u64 = pkref_load64(pk); ((u64 & 0xfffff) << 28) | (u64 & 0xfffff00000) >> 12; })

struct fhkX_bucket {
	fhk_mref next;
	uint8_t num;
	uint8_t flags;
	fhkX_root roots[MAX_ROOT];
	void *ptr[]; // [MAX_ROOT] if BUCKET_COPY is set, otherwise [0]
};

#define BUCKET_GIVEN        0x40
#define BUCKET_COPY         0x80
#define bucket_checkG(f)    ((f) & BUCKET_GIVEN)
#define bucket_checkC(f)    ((f) & BUCKET_COPY)

/* solver state. */
struct fhk_solver {
	fhkX_sp *stateM[0];      // model search state (must be first)
	fhk_co C;                // coroutine (must be next)
	struct fhk_graph *G;     // graph
	fhkX_valueref value;     // value state
	fhk_mref mem;            // shared solver memory   (struct fhk_mem *)
	fhk_mref bucket;         // root bucket   (struct fhkX_bucket *)
	fhkP_inst ident;         // interned ident map size
	fhk_sref work;           // work stack head pointer    (void *)
	fhkP_idx idx;            // request idx (vref, modcall, mapcall)
	fhkP_inst inst;          // request instance (vref, modcall, mapcall/i)
	union {
		fhk_cedge *edges;    // request edges (modcall)
		fhk_status error;    // fail status if the solver returned 0
	};
	fhkX_anymap map[256];    // mapping state  (indexed by zero-extended map id)
	union {                  // variable-like states (must be last)
		fhkX_sp *stateV[0];  // computed variable search state
		fhkX_bitmap stateG[0]; // given variable missing state (1: missing, 0: have)
		fhkX_checkmap stateC[0]; // check state bitmap, see description above
	};
};
