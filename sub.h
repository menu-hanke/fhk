#pragma once

#include "def.h"
#include "solve.h"
#include "target.h"

#include <stddef.h>
#include <stdint.h>

#define alignmask(size) (((int32_t)0x80000000 >> __builtin_clz(size)) | -7)

NOAPI void fhk_mem_newbufV(fhk_Sref S, xidx idx, xinst shape);
NOAPI void fhk_mem_newbitmapV(fhk_Sref S, xidx idx, xinst shape);
NOAPI void fhk_mem_newbufX(fhk_Sref S, xidx idx, xinst shape);
NOAPI void fhk_mem_newbitmapX(fhk_Sref S, xidx idx, xinst shape);
NOAPI void fhk_mem_grow_ident(fhk_Sref S, int32_t znum);

#if FHK_WINDOWS

NOAPI void fhk_mem_win_commit_head(fhk_mem *mem, intptr_t head);
NOAPI void fhk_mem_win_commit_tail(fhk_mem *mem, intptr_t tail);

static inline void fhk_mem_commit_head(fhk_mem *mem, intptr_t head) {
	if(UNLIKELY(head > mem->chead))
		fhk_mem_win_commit_head(mem, head);
}

static inline void fhk_mem_commit_tail(fhk_mem *mem, intptr_t tail) {
	if(UNLIKELY(tail < mem->ctail))
		fhk_mem_win_commit_tail(mem, tail);
}

#else

#define fhk_mem_commit_head(mem, head) do { (void)(mem); (void)(head); } while(0)
#define fhk_mem_commit_tail(mem, tail) do { (void)(mem); (void)(tail); } while(0)

#endif
