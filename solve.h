#pragma once

#include "conf.h"
#include "def.h"
#include "target.h"
#include "trace.h"

#include <stdint.h>

/* ---- bitmaps ---------------------------------------- */

typedef uint64_t fhk_bmword;
#define bitmap_idx(i)     ((i)>>6)
#define bitmap_shift(i)   ((i)&63)
#define bitmap_size(n)    (8*(((n)+63)&~63))
#define bitmapW_ffs       __builtin_ctzll
#define ones(n)          ((1LL<<(n))-1)
#define zeros(n)         ((~(fhk_bmword)0)<<(n))

/* ---- search state ---------------------------------------- */
/*
 * +----------------------------------------------+------------------------------+
 * |                 state                        |             cost             |
 * +----+----+----+----+--------+--------+--------+-------+-----------+----------+
 * | 63 | 62 | 61 | 60 | 59..48 | 47..40 | 39..32 | 31(s) | 30..23(e) | 22..0(m) |
 * +----+----+----+----+--------+--------+--------+-------+-----------+----------+
 * | c  | v  | k  |    |       inst      |  edge  |        cost (low bound)      |
 * +----+----+----+----+--------+--------+--------+------------------------------+
 */
typedef union fhk_sp {
	// note: the order of fields here is important, don't change.
	struct {
		float cost;
		uint32_t state;
	};
	uint8_t u8[8];
	uint16_t u16[4];
	uint32_t u32[2];
	uint64_t u64;
} fhk_sp;

#define SPC8            0x80 // does it have a chain? [var/derive/model]
#define SPV8            0x40 // does it have a value? [var/derive/model]
#define SPK8            0x20 // does it have checks that may fail?  [model only]
#define SP_FLAGS32(f)   ((f) << 24)
#define SP_FLAGS64(f)   ((uint64_t)(f) << 56)
#define SP32_COST       0
#define SP8_FLAGS       7
#define sp_ei(state)    ((state) & 0xff)
#define sp_inst(state)  (((state) >> 8) & 0xfffff)
#define sp_done(u64)    (((u64) & (SP_FLAGS64(SPC8) | 0x7fffffff)) >= (uint32_t)F32INF) // C | cost=inf ?

/* sp header byte */
#define HX              0x80 // search state expanded?
#define HV              0x40 // eval state expanded?

/* ---- work stack ---------------------------------------- */

/* solver work frame.
 *   +---------------------+-------+-----+----------+-----+----------+---------------------+
 *   | -/// read-only ///- | -1u64 | ... | heap[-n] | ... | heap[-1] |         top         |
 *   +---------------------+-------+-----+----------+-----+----------+---------------------+
 *           |---------------------|                                 |---------------------|
 *   |-------^-------------|                                         ^
 *   ^       |                                                       |
 *   |       W base link                                             W top
 *   W on enter
 */
typedef struct fhk_frameW {
	fhk_edgeH heap[0];  // heap grows down <--, current candidate is always at heap[-1]
	fhk_sp *v_sp;
	fhk_pkref p_pk;
	uint32_t m_inst;
	uint32_t v_inst;
	uint32_t p_inst;
	uint32_t p_znum;
	float beta;
	float ci;
	float bi;
	float p_ce;
#if FHK_TRACEON(solver)
	int16_t v_idx;
#endif
	union {
		struct {
			uint16_t link;
			uint8_t p_ei;
			uint8_t m_ei;
			uint8_t tol;
			uint8_t nh;
		};
		int64_t base;
	};
} fhk_frameW;

#define WBASE      (-1)
#define wheap(W)   ((fhk_edgeH *) (W))
#define wtop(W)    (&wheap(W)[-1])

typedef struct fhk_cedge {
	void *p;
	size_t n;
} fhk_cedge;

/* model call frame. */
typedef struct fhk_frameC {
	fhk_pkref c_pk;
	size_t *c_n;
	uint32_t m_inst;
	uint32_t p_inst;
	uint32_t p_znum;
	union {
		struct {
			uint16_t c_size;
			uint16_t link;
			uint16_t idx;
			uint8_t ei;
		};
		int64_t base;
	};
	fhk_cedge ce[];
} fhk_frameC;

/* ---- roots ---------------------------------------- */

/*
 * root info.
 * don't reorder the bitfields: the order is important for sorting.
 *   +----------+--------+--------+-------+-----+------+
 *   |    31    |   30   | 29..14 | 13..9 |  8  | 7..0 |
 *   +----------+--------+--------+-------+-----+------+
 *   | computed | deprio |  idx   |   0   | map | pos  |
 *   +----------+--------+--------+-------+-----+------+
 */
typedef uint32_t fhk_root;
typedef uint64_t fhk_selection;

#define BUCKET_SIZE                    32
#define ROOT_COMPUTED                  0x80000000
#define ROOT_DEPRIO                    0x40000000
#define ROOT_MAP                       0x00000100
#define root_newidx(idx)               ((idx) << 14)
#define root_newselection(var, inst)   (((uint64_t)(var) << 32) | (inst))
#define root_idx(root)                 ((uint16_t)((root) >> 14))
#define root_pos(root)                 ((uint8_t)(root))
#define select_idx(s)                  ((s) >> 32)
#define select_inst(s)                 ((uint32_t)(s))

typedef struct fhk_bucket {
	struct fhk_bucket *next;
	uint32_t num;
	fhk_root roots[BUCKET_SIZE];
	fhk_selection sel[BUCKET_SIZE];
} fhk_bucket;

/* ---- memory map ---------------------------------------- */

/*
 * +-----+-------+------------+----------------------------+-----+--------------------------------+-------+
 * | map | ident | call stack | work stack (temporary) --> | ... | <-- solver memory (persistent) | zeros |
 * +-----+-------+------------+----------------------------+-----+--------------------------------+-------+
 */
typedef struct fhk_mem {
#if FHK_WINDOWS
	intptr_t chead;         // lower committed pointer (grows upwards)
	intptr_t ctail;         // upper committed pointer (grows downwards)
#endif
	intptr_t tail;          // allocation pointer (grows downwards)
	int32_t ident;          // interned ident znum
} fhk_mem;

#define MEM_ZEROS           (MAX_INST>>6)
#define mem_id(mem)         ((fhk_subset *)((fhk_mem *)(mem)+1))
#define mem_stack(mem)      ((void *)(mem_id(mem)+MAX_INST))
#define mem_W(mem)          (mem_stack(mem)+MAX_STACK)
#define mem_zeros(mem)      ((void *)(mem)+VM_SIZE-MEM_ZEROS)
#define mem_tail            mem_zeros

/* ---- solver ---------------------------------------- */

typedef struct fhk_solver {
	void *sp;               // stack pointer, this must be first
	fhk_Gref G;             // graph
	fhk_mem *mem;           // shared memory area
	fhk_bucket *bucket;     // root bucket list head
	union {
		fhk_cedge *edges;   // current modcall edge pointer
		fhk_status err;     // current error
	};
	int32_t ident;          // ident znum (always >= IDENT_INTERN_ZNUM)
	int32_t inst;           // current callback var/mod instance
	int16_t idx;            // current callback var/mod index
} fhk_solver;

/* +-----+------------+-----+
 * | X[] | fhk_solver | V[] |
 * +-----+------------+-----+
 *                    ^- fhk_Sref
 */
typedef intptr_t fhk_Sref;

/*
 *                              V[idx]       X[~idx]
 * +--------------+-------+----------------+----------+
 * | model        | model                    h . sp-> |
 * +--------------+-------+----------------+----------+
 * | derive       | var           value->    h . sp-> |
 * |    /         | map           subset->   h . sp-> |
 * | computed     | check   <-M . F->        h . sp-> |  *** will not be implemented (?)
 * +--------------+-------+----------------+----------+
 * |              | var           value->        M->  |
 * |    given     | map           subset->       M->  |
 * |              | check   <-M . F->                 |  *** not (yet?) implemented
 * +--------------+-------+----------------+----------+
 * | pred. guard  | check   <-M . F->                 |
 * +--------------+-------+----------------+----------+
 */
#define S2ref(S)       ((fhk_Sref)((fhk_solver *)(S)+1))
#define srefS(S)       ((fhk_solver *)(S)-1)
#define srefV(S,idx)   ((void **)(S))[(idx)]
#define srefX(S,idxn)  ((void **)srefS(S))[(idxn)]
