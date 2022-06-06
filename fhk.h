#pragma once

/* fhk api. */

#include <stddef.h>
#include <stdint.h>

/* common typedefs */
typedef int64_t fhk_subset;
typedef int64_t fhk_status;
typedef int32_t fhk_mhandle;
typedef int64_t fhk_mhandle2;
typedef int64_t fhk_query;
typedef struct fhk_mem fhk_mem;
typedef struct fhk_solver fhk_solver;
typedef struct fhk_graph fhk_graph;

typedef union fhk_gvalue {
	uint64_t u64;
	float f32;
	double f64;
} fhk_gvalue;

// this is wrapped in a struct to make it play nice with luajit's ffi.
typedef struct { struct fhk_mut_graph *M; } fhk_mut_ref;

/* memory */
fhk_mem *fhk_create_mem();
void fhk_destroy_mem(fhk_mem *mem);
void *fhk_mem_alloc(fhk_mem *mem, size_t size, size_t align);
void fhk_reset_mem(fhk_mem *mem);

/* solver */
fhk_solver *fhk_create_solver(fhk_graph *G, fhk_mem *mem);
int fhk_continue(fhk_solver *S);
void fhk_setshape(fhk_solver *S, int group, int shape);
void fhk_setshapeT(fhk_solver *S, uint32_t *shape);
void fhk_setroot(fhk_solver *S, int idx, fhk_subset ss);
void fhk_setrootC(fhk_solver *S, int idx, fhk_subset ss, void *p);
void *fhk_setrootD(fhk_solver *S, int idx, fhk_subset ss);
void fhk_setmapK(fhk_solver *S, int map, fhk_subset ss);
void fhk_setmapI(fhk_solver *S, int map, int inst, fhk_subset ss);
void fhk_setvalue(fhk_solver *S, int idx, fhk_subset ss, void *p);
void fhk_setvalueC(fhk_solver *S, int idx, fhk_subset ss, void *p);
void *fhk_setvalueD(fhk_solver *S, int idx, fhk_subset ss);
fhk_subset fhk_copysubset(fhk_solver *S, fhk_subset ss);

/* building */
fhk_status fhk_create_mut(fhk_mut_ref *M);
void fhk_destroy_mut(fhk_mut_ref *M);
fhk_status fhk_mut_layout(fhk_mut_ref *M);
fhk_query fhk_mut_query(fhk_mut_ref *M, fhk_mhandle handle);
int fhk_mut_size(fhk_mut_ref *M);
fhk_status fhk_mut_build(fhk_mut_ref *M, void *buf);
void fhk_mut_pin(fhk_mut_ref *M, fhk_mhandle e);
fhk_status fhk_mut_add_group(fhk_mut_ref *M);
fhk_status fhk_mut_add_mapK(fhk_mut_ref *M);
fhk_status fhk_mut_add_mapI(fhk_mut_ref *M);
fhk_status fhk_mut_add_model(fhk_mut_ref *M, fhk_mhandle group, float k, float c);
fhk_status fhk_mut_add_var(fhk_mut_ref *M, fhk_mhandle group);
fhk_status fhk_mut_add_guard(fhk_mut_ref *M, fhk_mhandle var);
fhk_status fhk_mut_add_param(fhk_mut_ref *M, fhk_mhandle model, fhk_mhandle var, fhk_mhandle2 map);
fhk_status fhk_mut_add_return(fhk_mut_ref *M, fhk_mhandle model, fhk_mhandle var, fhk_mhandle2 map);
fhk_status fhk_mut_add_check(fhk_mut_ref *M, fhk_mhandle model, fhk_mhandle guard, fhk_mhandle2 map,
		float penalty);
void fhk_mut_set_dsym(fhk_mut_ref *M, fhk_mhandle handle, const char *sym);
void fhk_mut_set_costM(fhk_mut_ref *M, fhk_mhandle model, float k, float c);
fhk_status fhk_mut_set_sizeV(fhk_mut_ref *M, fhk_mhandle var, uint16_t size);
fhk_status fhk_mut_set_opcodeG(fhk_mut_ref *M, fhk_mhandle guard, int opcode, fhk_gvalue arg);

/* prune */
fhk_status fhk_prune(fhk_mut_ref *M);

/* debug */
int fhk_is_dsym();
