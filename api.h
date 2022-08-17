#pragma once

#include "build.h"
#include "def.h"
#include "solve.h"

/* asm */
int fhk_continue(fhk_solver *S);

/* subroutines */
fhk_mem *fhk_create_mem();
void fhk_destroy_mem(fhk_mem *mem);
void fhk_reset_mem(fhk_mem *mem);
fhk_solver *fhk_create_solver(fhk_mem *mem, fhk_graph *G);
// TODO: fhk_solver *fhk_clone(fhk_mem *mem, fhk_solver *S, <list of indices to keep>)
void *fhk_mem_alloc(fhk_mem *mem, size_t size, size_t align);
void fhk_setrootK(fhk_solver *S, int idx, fhk_subset ss);
void fhk_setrootM(fhk_solver *S, int idx, int map, int inst);
void fhk_setvalue(fhk_solver *S, int idx, fhk_subset ss, void *p);
void fhk_setvalueC(fhk_solver *S, int idx, fhk_subset ss, void *p);
void *fhk_setvalueD(fhk_solver *S, int idx, fhk_subset ss);
void fhk_getvalue(fhk_solver *S, int idx, fhk_subset ss, void *p);
void *fhk_getvalueD(fhk_solver *S, int idx, fhk_subset ss);
void fhk_invert(fhk_mem *mem, fhk_subset *from, int fromshape, fhk_subset *to, int toshape);

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
fhk_status fhk_create_mut(fhk_mut_ref *M);
void fhk_destroy_mut(fhk_mut_ref *M);
void fhk_mut_set_default_cost(fhk_mut_ref *M, float k, float c);
fhk_status fhk_mut_add_var(fhk_mut_ref *M, fhk_mref32 group);
fhk_status fhk_mut_set_inverse(fhk_mut_ref *M, fhk_mref32 map, fhk_mref32 inverse);
fhk_status fhk_mut_set_lhs(fhk_mut_ref *M, fhk_mref32 guard, fhk_mref32 var);
fhk_status fhk_mut_set_size(fhk_mut_ref *M, fhk_mref32 var, uint16_t size);
fhk_status fhk_mut_add_model(fhk_mut_ref *M, fhk_mref32 group);
void fhk_mut_set_cost(fhk_mut_ref *M, fhk_mref32 model, float k, float c);
fhk_status fhk_mut_add_param(fhk_mut_ref *M, fhk_mref32 model, fhk_mref32 var, fhk_mref32 map);
fhk_status fhk_mut_add_return(fhk_mut_ref *M, fhk_mref32 model, fhk_mref32 var, fhk_mref32 map);
fhk_status fhk_mut_add_check(fhk_mut_ref *M, fhk_mref32 model, fhk_mref32 guard, fhk_mref32 map,
		float penalty);
fhk_status fhk_mut_add_rcheck(fhk_mut_ref *M, fhk_mref32 edge, fhk_mref32 check, float penalty);
fhk_status fhk_mut_add_predicate(fhk_mut_ref *M);
fhk_status fhk_mut_set_operator(fhk_mut_ref *M, fhk_mref32 obj, int operator, fhk_operand *rhs);
fhk_status fhk_mut_set_predicate(fhk_mut_ref *M, fhk_mref32 obj, fhk_mref32 pre);
void fhk_mut_disable(fhk_mut_ref *M, fhk_mref32 obj);
fhk_status fhk_mut_analyze(fhk_mut_ref *M);
fhk_status fhk_mut_mark(fhk_mut_ref *M, fhk_mref32 ref);
fhk_status fhk_mut_layout(fhk_mut_ref *M);
size_t fhk_mut_size(fhk_mut_ref *M);
fhk_status fhk_mut_build(fhk_mut_ref *M, void *buf);
fhk_query fhk_mut_query(fhk_mut_ref *M, fhk_mref32 ref);

/* debug */
void fhk_mut_set_dsym(fhk_mut_ref *M, fhk_mref32 obj, const char *sym);
