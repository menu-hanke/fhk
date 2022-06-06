#pragma once

#include "def.h"
#include "solve.h"

#include <stdalign.h>
#include <stddef.h>

#define fhk_mem_align(mem, align) (mem)->ptr = ALIGN((mem)->ptr, (align))
#define fhk_mem_alignT(mem, t)    fhk_mem_align((mem), alignof(t))
#define fhk_mem_bump(mem, size)   (mem)->ptr += size;
#define fhk_mem_bumpT(mem, t)     fhk_mem_bump((mem), sizeof(t))
#define fhk_mem_commitP(mem,p)    fhk_vm_commit(&(mem)->map, (intptr_t)(p))
#define fhk_mem_commit(mem)       fhk_mem_commitP((mem), (intptr_t)mrefp((mem), (mem)->ptr))

NOAPI fhk_subset *fhk_mem_newmapI(struct fhk_solver *S, int size);
NOAPI fhkX_sp *fhk_mem_newsp(struct fhk_solver *S, int size, fhkX_sp init);
NOAPI void *fhk_mem_newvalue(struct fhk_solver *S, int size, int num);
NOAPI fhkX_bitmap fhk_mem_newbitmap(struct fhk_solver *S, int size);
NOAPI fhkX_checkmap fhk_mem_newcheckmap(struct fhk_solver *S, int size);
NOAPI void fhk_mem_checkident(struct fhk_solver *S, int size);
