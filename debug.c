#include "debug.h"
#include "def.h"
#include "mut.h"
#include "solve.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*              /!\  WARNING  /!\
 * everything in this file is suitable for debugging only.
 * these functions reuse internal buffers, and don't do any bound checking.
 * only use the return values as debug prints.
 * definitely do not store them.
 */

/* ---- symbol table management ---------------------------------------- */

#define dsym_ptr(T,s) (const char *)((intptr_t)(T) + (s))
#define ptr_dsym(T,p) ((intptr_t)(p) - (intptr_t)(T))

#if FHK_DSYM

static struct fhkX_dsym_tab *dsym_newtab(int minsize){
	int size = 1024;
	while(size < minsize)
		size *= 2;

	struct fhkX_dsym_tab *dstab = malloc(sizeof(*dstab) + size);
	dstab->cap = size;
	dstab->used = 0;
	return dstab;
}

static void *dsym_new(fhkX_dsym_ref *ref, int size){
	if(!*ref){
		*ref = dsym_newtab(size);
		(*ref)->used = size;
		return (*ref)->mem;
	}

	struct fhkX_dsym_tab *tab = *ref;
	if(tab->used + size > tab->cap){
		do {
			tab->cap *= 2;
		} while(tab->used + size > tab->cap);
		*ref = tab = realloc(tab, sizeof(*tab) + tab->cap);
	}

	void *mem = tab->mem + tab->used;
	tab->used += size;
	return mem;
}

fhkX_dsym fhk_debug_sym_add(fhkX_dsym_ref *ref, const char *sym){
	int size = strlen(sym) + 1;
	void *p = dsym_new(ref, size);
	memcpy(p, sym, size);
	return ptr_dsym(*ref, p);
}

#endif

/* ---- debug strings ---------------------------------------- */

const char *fhk_debug_sym(struct fhk_graph *G, xidx idx){
	static char rbuf[4][32];
	static int pos = 0;

#if FHK_DSYM
	if(idx_isM(idx) && G->models[idx].dsym) return dsym_ptr(G->dsym, G->models[idx].dsym);
	// this also handles guards.
	if(idx_isX(idx) && G->vars[idx].dsym)   return dsym_ptr(G->dsym, G->vars[idx].dsym);
#endif

	char *buf = rbuf[pos];
	pos = (pos + 1) % 4;

	const char *fmt = (idx < -G->nm) ? "(OOB model: %zd)"
		            : (idx < 0)      ? "model[%zd]"
					: (idx < G->nv)  ? "var[%zd]"
					: (idx < G->nx)  ? "guard[%zd]"
					:                  "(OOB xnode: %zd)";

	sprintf(buf, fmt, idx);
	return buf;
}

const char *fhk_mut_debug_sym(struct fhk_mut_graph *M, fhk_mhandle handle){
	static char rbuf[4][128];
	static int pos = 0;

	static const char *tagstr[] = {
#define TAGSTR(name,_) #name,
		MUT_OBJDEF(TAGSTR)
#undef TAGSTR
	};

	if(mhandle_isident(handle)) return "(ident)";
	if(mhandle_istarget(handle)) return "(target group)";

	char *buf = rbuf[pos];
	pos = (pos + 1) % 4;

	if(mhandle_isref(handle)){
		int tag = mref_tag(M, handle);
		buf[0] = mtag_ispruned(tag) ? 'X' : '-';
		buf[1] = mtag_ispinned(tag) ? 'P' : '-';
		buf[2] = mtag_isA(tag)      ? 'A' : '-';
		buf[3] = mtag_isB(tag)      ? 'B' : '-';
		buf[4] = ':';

#if FHK_DSYM
		fhkX_dsym dsym = 0;
		switch(mtagT(tag)){
			case MTAG(var): dsym = ((struct fhk_mut_var *) mrefp(M, handle))->dsym; break;
			case MTAG(model): dsym = ((struct fhk_mut_model *) mrefp(M, handle))->dsym; break;
			case MTAG(guard): dsym = ((struct fhk_mut_guard *) mrefp(M, handle))->dsym; break;
		}
		if(dsym){
			strcpy(buf+5, dsym_ptr(M->dsym, dsym));
			return buf;
		}
#endif

		sprintf(buf+5, "%s[0x%x]", tagstr[mtagT(tag)], handle);
		return buf;
	}else{
		const char *fmt = mhandle_ismapu(handle)  ? "umap[%d]"
			            : mhandle_isgroup(handle) ? "group[%d]"
						:                           "(invalid map 0x%x)";
		sprintf(buf+5, fmt, mhandleV(handle));
		return buf;
	}
}

const char *fhk_debug_value(struct fhk_solver *S, xidx idx, xinst inst){
	static char buf[128];

	typedef union { int32_t i32; float f32; } v32;
	typedef union { int64_t i64; double f64; } v64;

	if(idx_isX(idx) && idx < S->G->nv){
		struct fhk_var *x = &S->G->vars[idx];
		if(var_isG(x) && (!S->stateG[idx] || (bitmap_is1(S->stateG[idx], inst))))
			return "(no value given)";
		else if(var_isC(x) && (!S->stateV[idx] || !sp_checkV(S->stateV[idx][inst].state)))
			return "(no value computed)";

		void *vp = valueV(S->value, idx) + inst*x->size;

		switch(x->size){
			case 4: sprintf(buf, "u32: 0x%x f32: %f", ((v32*)vp)->i32, ((v32*)vp)->f32); break;
			case 8: sprintf(buf, "u64: 0x%lx f64: %f", ((v64*)vp)->i64, ((v64*)vp)->f64); break;
			default:
				strcpy(buf, "hex: 0x");
				for(size_t i=0;i<x->size;i++)
					sprintf(buf+strlen("hex: 0x")+2*i, "%x", ((uint8_t *)vp)[i]);
				buf[strlen("hex: 0x")+2*x->size] = 0;
		}
	}else if(idx_isX(idx)){
		// TODO
		return "(guard)";
	}else{
		// TODO
		return "(model)";
	}

	return buf;
}

/* ---- debug query ---------------------------------------- */

int fhk_is_dsym(){
	return !!FHK_DSYM;
}
