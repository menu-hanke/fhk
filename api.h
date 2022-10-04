#pragma once

#include "build.h"
#include "def.h"
#include "solve.h"
#include "target.h"

#ifndef FHK_API
#if __ELF__
#define FHK_API
#elif FHK_WINDOWS
#define FHK_API __declspec(dllexport)
#endif
#endif

/* asm */
FHK_API int fhk_continue(fhk_solver *S);

/* subroutines */
FHK_API fhk_mem *fhk_create_mem();
FHK_API void fhk_destroy_mem(fhk_mem *mem);
FHK_API void fhk_reset_mem(fhk_mem *mem);
FHK_API fhk_solver *fhk_create_solver(fhk_mem *mem, fhk_graph *G);
// TODO: fhk_solver *fhk_clone(fhk_mem *mem, fhk_solver *S, <list of indices to keep>)
FHK_API void *fhk_mem_alloc(fhk_mem *mem, size_t size, size_t align);
FHK_API void fhk_setrootK(fhk_solver *S, int idx, fhk_subset ss);
FHK_API void fhk_setrootM(fhk_solver *S, int idx, int map, int inst);
FHK_API void fhk_setvalue(fhk_solver *S, int idx, fhk_subset ss, void *p);
FHK_API void fhk_setvalueC(fhk_solver *S, int idx, fhk_subset ss, void *p);
FHK_API void *fhk_setvalueD(fhk_solver *S, int idx, fhk_subset ss);
FHK_API void fhk_getvalue(fhk_solver *S, int idx, fhk_subset ss, void *p);
FHK_API void *fhk_getvalueD(fhk_solver *S, int idx, fhk_subset ss);
FHK_API void fhk_sethook(fhk_solver *S, int jidx);
FHK_API void fhk_invert(fhk_mem *mem, fhk_subset *from, int fromshape, fhk_subset *to, int toshape);

/*
 * build. api usage:
 *
 *   create phase         fhk_create_mut
 *                        [ fhk_mut_add_*, fhk_mut_set_*, fhk_mut_disable ]+
 *
 *   analysis phase       fhk_mut_analyze
 *                        [ fhk_mut_mark ]+
 *
 *   layout phase         fhk_mut_layout
 *                        [ fhk_mut_size, fhk_mut_build, fhk_mut_query ]+
 *
 *   finally              fhk_destroy_mut
 */
FHK_API fhk_status fhk_create_mut(fhk_mut_ref *M);
FHK_API void fhk_destroy_mut(fhk_mut_ref *M);
FHK_API void fhk_mut_set_default_cost(fhk_mut_ref *M, float k, float c);
FHK_API fhk_status fhk_mut_add_var(fhk_mut_ref *M, fhk_mref32 group);
FHK_API fhk_status fhk_mut_set_inverse(fhk_mut_ref *M, fhk_mref32 map, fhk_mref32 inverse);
FHK_API fhk_status fhk_mut_set_lhs(fhk_mut_ref *M, fhk_mref32 guard, fhk_mref32 var);
FHK_API fhk_status fhk_mut_set_size(fhk_mut_ref *M, fhk_mref32 var, uint16_t size);
FHK_API fhk_status fhk_mut_add_model(fhk_mut_ref *M, fhk_mref32 group);
FHK_API void fhk_mut_set_cost(fhk_mut_ref *M, fhk_mref32 model, float k, float c);
FHK_API fhk_status fhk_mut_add_param(fhk_mut_ref *M, fhk_mref32 model, fhk_mref32 var, fhk_mref32 map);
FHK_API fhk_status fhk_mut_add_return(fhk_mut_ref *M, fhk_mref32 model, fhk_mref32 var, fhk_mref32 map);
FHK_API fhk_status fhk_mut_add_check(fhk_mut_ref *M, fhk_mref32 model, fhk_mref32 guard, fhk_mref32 map,
		float penalty);
FHK_API fhk_status fhk_mut_add_rcheck(fhk_mut_ref *M, fhk_mref32 edge, fhk_mref32 check, float penalty);
FHK_API fhk_status fhk_mut_add_predicate(fhk_mut_ref *M);
FHK_API fhk_status fhk_mut_set_operator(fhk_mut_ref *M, fhk_mref32 obj, int operator, fhk_operand *rhs);
FHK_API fhk_status fhk_mut_set_predicate(fhk_mut_ref *M, fhk_mref32 obj, fhk_mref32 pre);
FHK_API void fhk_mut_set_sym(fhk_mut_ref *M, fhk_mref32 obj, const char *sym);
FHK_API void fhk_mut_disable(fhk_mut_ref *M, fhk_mref32 obj);
FHK_API fhk_status fhk_mut_analyze(fhk_mut_ref *M);
FHK_API fhk_status fhk_mut_mark(fhk_mut_ref *M, fhk_mref32 ref);
FHK_API fhk_status fhk_mut_layout(fhk_mut_ref *M);
FHK_API size_t fhk_mut_size(fhk_mut_ref *M);
FHK_API fhk_status fhk_mut_build(fhk_mut_ref *M, void *buf);
FHK_API fhk_query fhk_mut_query(fhk_mut_ref *M, fhk_mref32 ref);
