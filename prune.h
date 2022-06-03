#pragma once

#include "def.h"

#include <stdint.h>

/* prune bound info
 *
 * +-------------------------------+------------+
 * |             cost              |    state   |
 * +-------+-----------+-----------+----+-------+
 * | 63(s) | 62..55(e) | 54..32(m) | 31 | 30..0 |
 * +-------+-----------+-----------+----+-------+
 * |   0   |  cost low/high bound  | hi | mref  |
 * +-------+-----------------------+----+-------+
 *
 * note: do not reorder fields, these must be ordered by (cost, color)
 */
typedef union {
	struct {
		uint32_t state;
		float cost;
	};
	uint64_t u64;
} fhkX_bound;

#define bound_ref(state) ((state) & 0x7fffffff)
#define bound_cmp(a,b)   ((a).u64 < (b).u64)
#define bound_isL(state) ((int32_t)(state) >= 0)
#define bound_isH(state) (!bound_isL(state))
#define bound_newL(r,c)  ((fhkX_bound){.cost=(c), .state=(r)})
#define bound_newH(r,c)  ((fhkX_bound){.cost=(c), .state=0x80000000|(r)})

/* bound heap */
struct fhkX_bheap {
	uint32_t used, cap;
	fhkX_bound heap[];
};

typedef struct fhkX_bheap *fhkX_href;

#define bheap_size(cap)    (sizeof(struct fhkX_bheap) + (cap)*sizeof(fhkX_bound))
#define bheap_heap1(H)     ((H)->heap - 1) /* for 1-based indexing */

/* progress info */
#define prog_isfinite(u32)  ((u32) < 0x7f800000)
