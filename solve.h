#pragma once

#include "co.h"
#include "conf.h"
#include "def.h"
#include "fhk.h"
#include "trace.h"

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
#define bitmap_idx32(i)   ((i)/32)
#define bitmap_shift32(i) ((i)%32)
#define bitmap_idx64(i)   ((i)/64)
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
typedef int64_t fhkX_slot __attribute__((may_alias));
typedef fhkX_slot *fhkX_slotref;
#define slotref(p)            ((fhkX_slotref) (p))
#define slotnum(S,W)          (slotref(W) - (S)->stack)
#define slots(t)              ((sizeof(t)+7)/8)

typedef struct {
	int16_t idx;
	int16_t ei;
} fhkX_candinfo;

struct fhkX_cselector {
	// slot 0: iterator
	fhkX_iter it;

	// slot 1: iterator pk
	fhkX_pkref pk;

	// slot 2: precomputed start sp
	fhkX_sp *sp;

	// slot 3: candidate info
	fhkX_candinfo info;
};

struct fhkX_work {
	// slot 0
	int16_t prev;
	int8_t where;
	// 8 unused
	float ecost; // (parameter only)

	// slot 1
	fhkX_candinfo cinfo;
	uint32_t cinst;

	// slot 2: variable info
	fhkX_sp *sp;

	// slot 3: cost info
	float CI;
	float BI;

	// slot 4
	float B;
	int16_t cnum;
	// 16 unused

	// slot 5: active edge
	void *edge;

	// slot 6: active iterator
	fhkX_iter it;

	// slot 7: active iterator pk
	fhkX_pkref pk;

#if FHK_TRACEON(solver)
	// slot 8: debug info
	fhkP_idx idx;
	fhkP_inst inst;
#endif
};

#define WHERE_CHECK   (-1)
#define WHERE_PARAM   0
#define where_isC(w)  ((w) < 0)
#define where_isP(w)  ((w) == 0)

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
	struct fhkX_bucket *next;
	uint8_t used;
	uint8_t flags;
	fhkX_root roots[MAX_ROOT];
	// only valid if BUCKET_COPY is set
	void *p[];
};

#define BUCKET_GIVEN     0x40
#define BUCKET_COPY      0x80
#define bucket_checkG(f) ((f) & BUCKET_GIVEN)
#define bucket_checkC(f) ((f) & BUCKET_COPY)
#define bucket_size(f)   (sizeof(struct fhkX_bucket) + (bucket_checkC(f) ? (MAX_ROOT)*sizeof(void *) : 0))
#define bucket_free(b)   (MAX_ROOT - (b)->used)

/* mapping state */
typedef union {
	fhk_subset *imap;
	fhk_subset kmap;
} fhkX_anymap;

#define ANYMAP_UNDEF      ((fhkX_anymap){.kmap=SUBSET_UNDEF})
#define anymap_isU(am)    subset_isU((am).kmap)
#define anymapK(am)       (am).kmap
#define anymapI(am)       (am).imap
#define anymapII(am,inst) (am).imap[(inst)]

/* scatter info
 *
 *          +--------+--------+--------+--------+-------+
 *          | 63..60 | 59..40 | 39..32 | 32..20 | 19..0 |
 * +--------+--------+--------+--------+--------+-------+
 * | range  |   0    |  bpos  |      vpos       |  num  |
 * +--------+--------+--------+--------+--------+-------+
 * | header |   -1   |        0        |   edge index   |
 * +--------+--------+-----------------+----------------+
 * |  end   |                    -1                     |
 * +--------+-------------------------------------------+
 */
typedef int64_t fhkX_scatter;
#define SCATTER_END         (-1)
#define scatter_isR(s)      ((s) >= 0)
#define scatter_isH(s)      ((s) < -1)
#define scatter_isE(s)      ((s) == -1)
#define scatterR_num(s)     ((s) & 0xfffff)
#define scatterR_vpos(s)    (((s) >> 20) & 0xfffff)
#define scatterR_bpos(s)    (((s) >> 40) & 0xfffff)
#define scatterR_new(n,v,b) ((n) | ((int64_t)(v) << 20) | (int64_t)(b) << 40)
#define scatterH_edge(s)    ((int32_t)(s))
#define scatterH_new(e)     ((1LL << 63) | (e))
#define scatter_mark(sz)    ((void *) ~(intptr_t)(sz)) /* mark to allocate scatter later */
#define scatter_checkM(p)   ((intptr_t)(p) < 0)
#define scatterM_size(p)    (~(intptr_t)(p))

/* value state */
typedef union {
	uint8_t *m; // models: 0 -> value not expanded, 1 -> value expanded
	void **v;   // vars: value buffer
} fhkX_valueref;

#define valueM(r,i)         (r).m[(i)]
#define valueV(r,i)         (r).v[(i)]

/* scratch space */
struct fhkX_scratchref {
	uint32_t size;
	uint32_t used;
	uint32_t mark;
	void *p;
};

#define SCRATCH_ALIGN      8
#define SCRATCH_MINSIZE    (2*(sizeof(fhk_modcall) + (MAX_PARAM+MAX_RETURN)*sizeof(fhk_cedge)))
#define SCRATCH_NOMARK     (~(uint32_t)0)
#define scratch_checkM(m)  ((m) != SCRATCH_NOMARK)

/* solver state */
struct fhk_solver {
	fhkX_sp *stateM[0];      // model search state (must be first)
	fhk_co C;                // coroutine (must be next)

	struct fhk_graph *G;     // graph
	fhkX_anymap *mapstate;   // mapping state
	fhkX_valueref value;     // value state
	struct fhkX_scratchref scratch; // scratch space

	fhk_arena *arena;          // allocator
	struct fhkX_bucket *root; // root bucket head

	fhkX_slot stack[FHK_MAX_STACK]; // work stack

	union {                  // variable-like states (must be last)
		fhkX_sp *stateV[0];  // computed variable search state
		fhkX_bitmap stateG[0]; // given variable missing state (1: missing, 0: have)
		fhkX_checkmap stateC[0]; // check state bitmap, see description above
	};
};

/* coroutine entry point. */
NOAPI void fhk_yf_solver_main(fhk_solver *S);

/* state manipulation. */
NOAPI struct fhk_solver *fhk_solver_new(fhk_graph *G, fhk_arena *arena);
NOAPI fhk_subset *fhk_solver_newmapI(struct fhk_solver *S, xinst size);
NOAPI fhkX_sp *fhk_solver_newsp(struct fhk_solver *S, xinst size, fhkX_sp init);
NOAPI void *fhk_solver_newvalue(struct fhk_solver *S, xinst size, xinst num);
NOAPI fhkX_bitmap fhk_solver_newbitmap(struct fhk_solver *S, xinst size);
NOAPI fhkX_checkmap fhk_solver_newcheckmap(struct fhk_solver *S, xinst size);
NOAPI struct fhkX_bucket *fhk_solver_newbucket(struct fhk_solver *S, int flags);
