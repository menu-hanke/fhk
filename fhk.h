#pragma once

/* fhk public header */

#include <stddef.h>
#include <stdint.h>

/* increment this when you break ABI.
 * use this for eg. assertions in lua code to fail when the ABI changes. */
#define FHK_ABI 1

/* subsets */
typedef int64_t fhk_subset;
#define FHK_EMPTYSET ((fhk_subset)(-1))

/* guards */
typedef union fhk_gvalue {
	uint64_t u64;
	float f32;
	double f64;
} fhk_gvalue;

enum {
	FHK_GUARD_F32_GE,
	FHK_GUARD_F32_LE,
	FHK_GUARD_F64_GE,
	FHK_GUARD_F64_LE,
	FHK_GUARD_U8_M64,
	FHK_GUARD__MAX
};

/* model calls */
typedef struct fhk_cedge {
	void *p;
	size_t n;
} fhk_cedge;

typedef struct fhk_modcall {
	uint32_t inst;
	int16_t idx;
	uint8_t np, nr;
	fhk_cedge edges[];
} fhk_modcall;

/* status */
typedef int64_t fhk_status;
#define fhk_status_iserr(s)    ((s) < 0)
#define fhk_status_isdone(s)   ((s) <= 0)
#define fhk_status_code(s)     ((s) >> 60)
#define fhk_status_mcall(s)    ((fhk_modcall *)((s) & 0x0fffffffffffffffll)) /* MODCALL */
#define fhk_status_inst(s)     ((uint32_t)((s) >> 16)) /* VREF, MAPCALLI */
#define fhk_status_idx(s)      ((int16_t)(s)) /* SHAPE, VREF, MAPCALLK, MAPCALLI */

/* mutable graph handles */
typedef int32_t fhk_mhandle;
typedef int64_t fhk_mhandle2; // pack of 2 mhandles
#define FHK_MHANDLE_IDENT ((fhk_mhandle)0xafffffff)
#define FHK_MHANDLE_SPACE ((fhk_mhandle)0x9fffffff)

/* query */
#define FHK_PRUNED ((int32_t)0x80000000)

enum {
	/* return statuses */
	FHK_ERROR     = 0b1111,
	FHK_OK        = 0b0000,
	FHKS_SHAPE    = 0b0001,
	FHKS_VREF     = 0b0010,
	FHKS_MAPCALLK = 0b0011,
	FHKS_MAPCALLI = 0b0100,
	FHKS_MODCALL  = 0b0101,
	// unused1      0b0110
	// unused2      0b0111
};

enum {
	/* fhk_ecode(...) values */
	// input validation errors
	FHK_ERR_BOUND = 1, // s b    index (node/map/instance/group) out of bounds
	FHK_ERR_INVAL,     // s      invalid user value
	FHK_ERR_GIVEN,     // s      expected given variable

	// semantic errors
	FHK_ERR_NOVALUE,   // s      value expected but missing
	FHK_ERR_WRITE,     // s b    overwrite readonly value
	FHK_ERR_MAPASSOC,  //   b    map not associated with unique group
	FHK_ERR_UNSET,     //   b    unset value
	FHK_ERR_NOLAYOUT,  //   b    layout not computed

	// operational errors
	FHK_ERR_NYI,       // s      not yet implemented
	FHK_ERR_DEPTH,     // s      solver stack overflow
	FHK_ERR_CHAIN,     // sp     no chain with finite cost
	FHK_ERR_MEM,       // s b    failed to allocate memory

	/* fhk_etag(...) values */
	FHK_ETAG_EXT = 1,  // extend tag
	FHK_ETAG_NODE,     // var, model or shadow
	FHK_ETAG_MAP,      // imap or kmap
	FHK_ETAG_INST,     // instance
	FHK_ETAG_GROUP,    // group
	FHK_ETAG_EDGE,     // edge index
	FHK_ETAG_HANDLE    // mgraph handle
};

/* common typedefs */
typedef struct fhk_arena fhk_arena;
typedef struct fhk_solver fhk_solver;
typedef struct fhk_graph fhk_graph;

// this is wrapped in a struct to make it play nice with luajit's ffi.
typedef struct { struct fhk_mut_graph *M; } fhk_mut_ref;

/* memory */
fhk_arena *fhk_create_arena(size_t hint);
void fhk_init_arena(fhk_arena *arena, size_t hint);
void fhk_destroy_arena(fhk_arena *arena);
void *fhk_alloc(fhk_arena *arena, size_t size, size_t align) __attribute__((malloc));

/* solver */
fhk_solver *fhk_create_solver(fhk_graph *G, fhk_arena *arena);
fhk_status fhk_continue(fhk_solver *S);
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
int fhk_mut_query(fhk_mut_ref *M, fhk_mhandle handle);
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
