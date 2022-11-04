/*
 * solver coroutine.
 *
 * WARNING: the functions in this file must be called by fhk_continue, you can't call
 * them directly from C.
 */

#include "conf.h"
#include "debug.h"
#include "def.h"
#include "solve.h"
#include "sub.h"
#include "swap.h"
#include "trace.h"

#include <assert.h>
#include <float.h>
#include <math.h>
#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* the S register must: (1) be C callee-saved, and (2) match the assembly coroutine. */
register fhk_Sref S asm(ASMREG_S);

#if FHK_x64 && FHK_WINDOWS
/*
 * xmm6-xmm15 are callee-saved in the ms abi.
 * this means that normally the coroutine swap would have to save/restore them.
 * we can do fine with just xmm0-xmm5, so we will disable xmm6-xmm15 entirely on windows
 * to avoid the extra saves & restores.
 *
 * note that this only has to be done here.
 * all other functions are called and return normally, so they can use all registers.
 */
#define DISABLE(xmm) register double _##xmm asm(#xmm)
DISABLE(xmm6);  DISABLE(xmm7);  DISABLE(xmm8);  DISABLE(xmm9);  DISABLE(xmm10);
DISABLE(xmm11); DISABLE(xmm12); DISABLE(xmm13); DISABLE(xmm14); DISABLE(xmm15);
#undef DISABLE
#endif

// we will be calling recursively into the solver a lot, so declare the main functions here.
static int solver_chain(xidx, xinst, void *);
static void eval_modcall(xidx, xinst, void *);

// relative W for debugging
#define relW(W) ((intptr_t)W - (intptr_t)mem_W(srefS(S)->mem))

/* ---- control flow ---------------------------------------- */

static void yield_jmp(int jmp) {
	trace(JMP, jmp, fhk_debug_sym(srefS(S)->G, srefS(S)->idx), srefS(S)->inst);
	fhk_yield(jmp);
}

__attribute__((noreturn)) AINLINE
static void yield_err(fhk_status ecode) {
	trace(JERR);
	fhk_yield_err(ecode);
}

ERRFUNC static void yield_err_nyi() {
	yield_err(ecode(NYI));
}

ERRFUNC static void yield_err_cycle() {
	yield_err(ecode(CYCLE));
}

ERRFUNC static void yield_err_chain(xidx idx, xinst inst) {
	yield_err(ecode(CHAIN) | etagA(OBJ, idx) | etagB(INST, inst));
}

ERRFUNC static void yield_err_unset(xidx idx, xinst inst) {
	yield_err(ecode(UNSET) | etagA(OBJ, idx) | etagB(INST, inst));
}

/* ---- evaluation ---------------------------------------- */

/* evaluate given variable. caller must ensure it has no value yet. */
static void eval_given(xidx idx, xinst inst) {
	srefS(S)->idx = idx;
	srefS(S)->inst = inst;
	fhk_Gref G = srefS(S)->G;
	yield_jmp(idx - grefG(G)->j[jidx(idx)]);
	fhk_bmword *bm = srefX(S, ~idx);
	if(UNLIKELY((bm[bitmap_idx(inst)] >> bitmap_shift(inst)) & 1))
		yield_err_unset(idx, inst);
}

/*
 * evaluate computed variable. caller must ensure one or none (but not both) of C/V is set.
 * X-state must be allocated.
 * return 0 on success, 1 on error.
 */
static int eval_computed(xidx var, xinst inst, void *W) {
	fhk_sp *sp = (fhk_sp *)srefX(S, ~var) + inst;
	// C is not set AND cost is not known to be infinite?
	if(LIKELY(!sp_done(sp->u64))) {
		int r;
		if(UNLIKELY(r = solver_chain(var, inst, W))) return r;
	} else if(UNLIKELY(!(sp->u8[SP8_FLAGS] & SPC8))) {
		assert(sp->cost == INFINITY);
		return 1;
	}
	fhk_Gref G = srefS(S)->G;
	xidx midx;
	xinst minst;
	if(grefmeta(G, ~var).tag & TAG_DERIVE) {
		// can't speculate derives.
		assert(!(sp->u8[SP8_FLAGS] & SPV8));
		midx = var;
		minst = inst;
	} else {
		uint32_t state = sp->state;
		// solver picked speculated model?
		if(UNLIKELY(state & SP_FLAGS32(SPV8))) return 0;
		fhk_var *x = grefobj(G, var);
		midx = vheap(x, ~(uint64_t)sp_ei(state))->idx;
		minst = sp_inst(state);
	}
	eval_modcall(midx, minst, W);
	return 0;
}

/*
 * evaluate a map.
 * caller must ensure:
 * - it has no value yet,
 * - if it's computed it has X.
 */
static void eval_map(xidx map, xinst inst, void *W) {
	uint8_t tag = grefmeta(srefS(S)->G, ~map).tag;
	if(LIKELY(tag & TAG_GIVEN)) {
		eval_given(map, inst);
	} else {
		assert(tag & TAGM_ISCOMP);
		if(UNLIKELY(eval_computed(map, inst, W)))
			yield_err_chain(map, inst);
	}
}

/*
 * evaluate either imap inst or kmap 0.
 * caller must ensure assumptions of eval_map.
 */
static void eval_anymap(xidx map, xinst inst, void *W) {
	eval_map(map, map_isI(map) ? inst : 0, W);
}

/*
 * evaluate a predicate into F.
 * F is the bitmap base, vp is the value pointer, i is the offset from bitmap base (0 <= i <= 63).
 *
 * Q: why does this function look so ugly?
 * A: gcc was struggling when i wanted to use either a float or double depending on the opcode.
 */
static void eval_predicate(fhk_predicate *pre, fhk_bmword *F, void *vp, size_t stride, int64_t i,
		int64_t n) {

#if FHK_x64
	static const void *prep[] = {
#define PREPLABEL(operator, operand) &&prep_##operator,
		FHK_PREDEF(PREPLABEL)
#undef PREPLABEL
	};
	static const void *op[] = {
#define OPLABEL(operator, operand) &&operator,
		FHK_PREDEF(OPLABEL)
#undef OPLABEL
	};

	register float fpr;
	register uint64_t gpr;
	register uint64_t res = 0;
	void *const *o = op[pre->operator];
	goto *prep[pre->operator];

#define ASMPREP(src) asm(src : "=r"(gpr), "=x"(fpr) : "r"(pre))

prep_f32le:
prep_f32ge:
	ASMPREP("vmovss -4(%2), %1");
	goto *o;

prep_f64le:
prep_f64ge:
	ASMPREP("vmovsd -8(%2), %1");
	goto *o;

prep_isn:
	ASMPREP("mov -8(%2), %0");
	goto isn;

#undef ASMPRERP

#define ASMOP(src) asm(src : "+r"(res) : "r"(vp), "r"(gpr), "x"(fpr))

f32le:
	ASMOP(
			"vcomiss (%1), %3\n\t"
			"setb %b0"
	);
	goto next;

f32ge:
	ASMOP(
			"vcomiss (%1), %3\n\t"
			"seta %b0"
	);
	goto next;

f64le:
	ASMOP(
			"vcomisd (%1), %3\n\t"
			"setb %b0"
	);
	goto next;

f64ge:
	ASMOP(
			"vcomisd (%1), %3\n\t"
			"seta %b0"
	);
	goto next;

isn:
	// don't need inline asm here, gcc handles this one fine.
	res = (gpr >> *(uint8_t *)vp) & 1;
	goto next;

#undef ASMOP

next:
	*F |= res << (i&63);
	if(!--n) return;
	i++;
	if(UNLIKELY(!(i&63))) F++;
	vp += stride;
	res = 0;
	goto *o;

#else
#error "TODO: eval predicate for this arch"
#endif
}

static void newbufX(xidx idx, void *W);
static void checkbufX(xidx idx, void *W);
static void checkanyX(xidx idx, void *W);

/* evaluate a guard. caller must ensure it has no value yet. */
static void eval_guard(xidx idx, xinst inst, void *W) {
	fhk_Gref G = srefS(S)->G;
	uint8_t tag = grefmeta(G, ~idx).tag;
	if(LIKELY(!(tag & (TAG_DERIVE|TAG_COMPUTED|TAG_GIVEN)))) {
		fhk_pregrd *g = grefobj(G, idx);
		xidx vidx = g->idx;
		uint8_t vtag = grefmeta(G, ~vidx).tag;
		xinst end; // one past the last index
		fhk_bmword *bm = srefV(S, idx);
		if(vtag & TAG_GIVEN) {
			fhk_bmword *vm = srefX(S, ~vidx);
			// X doesn't necessarily exist, so we have to check.
			// we don't need to allocate it though, setvalue will do it for us.
			// the group map is already allocated by the solver.
			if(UNLIKELY(!vm || (vm[bitmap_idx(inst)] & (1ULL << bitmap_shift(inst))))) {
				eval_given(vidx, inst);
				vm = srefX(S, ~vidx);
			}
			xidx group = grefmeta(G, ~idx).group;
			xinst last = subsetIE_znum(*(fhk_subset *) srefV(S, group));
			xinst base = inst & ~63;
			int64_t i = bitmap_idx(inst);
			fhk_bmword V = (vm[i] | ~bm[~i]) & zeros(inst&63);
			if(V) {
				// overflow is zero, so any one bit found is guaranteed to be in bounds.
				int64_t one = bitmapW_ffs(V);
				bm[~i] &= zeros(one) | ones(inst&63);
				end = base + one;
			} else {
				bm[~i] &= ones(inst&63);
				for(;;) {
					base += 64;
					if(base > last) {
						end = last+1;
						break;
					}
					i++;
					V = vm[i] | ~bm[~i];
					if(V) {
						int64_t one = bitmapW_ffs(V);
						bm[~i] &= zeros(one);
						end = base + one;
						break;
					}
					bm[~i] = 0;
				}
			}
		} else {
			fhk_sp *sp = srefX(S, ~vidx);
			if(UNLIKELY(!sp)) {
				newbufX(vidx, W);
				sp = srefX(S, ~vidx);
			}
			if(UNLIKELY((sp[inst].u8[SP8_FLAGS] & (SPC8|SPV8)) != (SPC8|SPV8))) {
				if(UNLIKELY(eval_computed(vidx, inst, W))) {
					bm[bitmap_idx(inst)] |= 1ULL << bitmap_shift(inst);
					bm[~bitmap_idx(inst)] &= ~(1ULL << bitmap_shift(inst));
					return;
				}
			}
			xidx group = grefmeta(G, ~idx).group;
			xinst last = subsetIE_znum(*(fhk_subset *) srefV(S, group));
			end = inst;
			fhk_bmword *mm = bm + ~bitmap_idx(inst);
			for(;;) {
				*mm &= ~(1ULL << (end&63));
				end++;
				if(end > last) break;
				if((sp[end].u8[SP8_FLAGS] & (SPC8|SPV8)) != (SPC8|SPV8)) break;
				if(UNLIKELY(!(end&63))) mm--;
			}
		}
		size_t size = grefmeta(G, ~vidx).size;
		eval_predicate((fhk_predicate *) g, bm + bitmap_idx(inst), srefV(S, vidx)+size*inst,
				size, inst, end-inst);
	} else {
		// NYI: non-predicated guards (computed/given)
		yield_err_nyi();
	}
}

/* ---- maps and subsets ---------------------------------------- */

/* subset load unbiased */
AINLINE static fhk_subset map_subset_unchecked(xidx map, xinst inst) {
#if FHK_x64 && 0
	// TODO: is this better?
	//   mov $tmp1, [S+$map*8]
	//   lea $tmp2, [$inst*8]
	//   xor $tmp3, $tmp3
	//   test $mapb, $mapb
	//   cmovs $tmp3, $tmp2
	//   mov $result, [$tmp1+$tmp3]
	fhk_subset *vp = srefV(S, map);
	fhk_subset *vpi = vp + inst;
	asm (
			"test %b1, %b1\n\t"
			"cmovs %2, %0"
			: "+r" (vp)
			: "r" (map), "r" (vpi)
			: "cc"
	);
	return *vp;
#else
	return ((fhk_subset *) srefV(S, map))[map_isI(map) ? inst : 0];
#endif
}

/* subset load biased for i-maps (this should compile to a branch) */
AINLINE static fhk_subset map_subset_unchecked_biasI(xidx map, xinst inst) {
	// TODO: asm version to actually make it branch.
	return ((fhk_subset *) srefV(S, map))[LIKELY(map_isI(map)) ? inst : 0];
}

/*
 * checked shape (group size) load of an object.
 * this function makes no assumptions about about the existence of V/X for the space map.
 */
static xinst shapeof_checked(xidx idx, void *W) {
	xidx group = grefmeta(srefS(S)->G, ~idx).group;
	fhk_subset *vp = srefV(S, group);
	if(LIKELY(vp)) {
		fhk_subset ss = *vp;
		if(LIKELY(!subset_isU(ss)))
			return subsetIE_size(ss);
	}
	if(LIKELY(grefmeta(srefS(S)->G, ~group).tag & TAG_GIVEN)) {
		eval_given(group, 0);
	} else {
		// V doesn't imply X for computed variables.
		checkbufX(group, W);
		if(UNLIKELY(eval_computed(group, 0, W)))
			yield_err_chain(group, 0);
	}
	return subsetIE_size(*(fhk_subset *) srefV(S, group));
}

/* ---- state management ---------------------------------------- */
/*
 * NOTE: all functions below must preserve the following invariants:
 *   computed var X  => candidate model X
 *   model/derive HX => guard edge map           V+X
 *                      guard                    V
 *                      computed param edge map  V+X
 *                      computed param           X
 *   model/derive HV => given param edge map     V+X
 *                      given param              X
 *                      return edge map          V+X
 *                      return                   V
 */

AINLINE static void checkbufV(xidx idx, void *W) {
	if(LIKELY(srefV(S, idx))) return;
	fhk_mem_newbufV(S, idx, shapeof_checked(idx, W));
	// TODO (?): here (or maybe even earlier?) given subsets could be just pointed to a
	// global buffer full of SUBSET_UNDEFs, and then redirected on the first write.
	// this would allow copying a given subset buffer from the outside world.
}

AINLINE static void checkbitmapV(xidx idx, void *W) {
	if(LIKELY(srefV(S, idx))) return;
	fhk_mem_newbitmapV(S, idx, shapeof_checked(idx, W));
}

/* allocate X buffer. caller must ensure it doesn't exist yet. */
static void newbufX(xidx idx, void *W) {
	assert(!srefX(S, ~idx));
	// non-presolved models should be allocated by the following loop.
	// `idx` should never be a non-presolved model.
	assert((grefmeta(srefS(S)->G, ~idx).tag & (TAG_MODEL|TAG_PRESOLVED)) != TAG_MODEL);
	fhk_mem_newbufX(S, idx, shapeof_checked(idx, W));
	fhk_Gref G = srefS(S)->G;
	if(grefmeta(G, ~idx).tag & TAG_COMPUTED) {
		fhk_var *x = grefobj(G, idx);
		int64_t nh = x->nh;
		do {
			xidx map = vheap(x, -nh)->map;
			checkbufV(map, W);
			// map may be computed so we have to do the full check.
			checkanyX(map, W);
			xidx cidx = vheap(x, -nh)->idx;
			if(LIKELY(!srefX(S, ~cidx)))
				fhk_mem_newbufX(S, cidx, shapeof_checked(cidx, W));
		} while(--nh > 0);
	}
}

/* allocate X buffer for a computed variable, derived variable or model if it doesn't exist yet. */
AINLINE static void checkbufX(xidx idx, void *W) {
	assert(grefmeta(srefS(S)->G, ~idx).tag & (TAG_DERIVE|TAG_COMPUTED|TAG_MODEL));
	if(LIKELY(srefX(S, ~idx))) return;
	newbufX(idx, W);
}

/* allocate X buffer for a GIVEN variable if it doesn't exist yet. */
AINLINE static void checkbitmapX(xidx idx, void *W) {
	assert(grefmeta(srefS(S)->G, ~idx).tag & TAG_GIVEN);
	if(LIKELY(srefX(S, ~idx))) return;
	fhk_mem_newbitmapX(S, idx, shapeof_checked(idx, W));
}

AINLINE static void checkanyX(xidx idx, void *W) {
	if(LIKELY(srefX(S, ~idx))) return;
	if(grefmeta(srefS(S)->G, ~idx).tag & TAG_GIVEN)
		fhk_mem_newbitmapX(S, idx, shapeof_checked(idx, W));
	else
		newbufX(idx, W);
}

/*
 * expand model/derive search state:
 *   -> edge maps (c,p,r)      VX
 *   -> checks                 VX
 *   -> computed params        -X     + candidates -X
 *   -> pre-solved params      --
 *   -> given params           --
 *   -> returns                --
 */
static void expandbufX(xidx idx, void *W) {
	assert(grefmeta(srefS(S)->G, ~idx).tag & TAGM_ISMOD);
	fhk_sp *sp = srefX(S, ~idx);
	// HV may be set here if this model first appeared as a presolved edge.
	assert(!(((uint8_t *)sp)[-1] & HX));
	((uint8_t *) sp)[-1] |= HX;
	fhk_Gref G = srefS(S)->G;
	fhk_model *m = grefobj(G, idx);
	int64_t ei = -(int64_t)m->e_check;
	if(ei) {
		fhk_edgeC *e = m->ec + ei;
		for(; ei<0; ei++, e++) {
			checkbufV(e->map, W);
			checkanyX(e->map, W);
			checkbitmapV(e->idx, W);
			// TODO: if/when given/computed checks are implemented this needs to check for X.
			// pred. guard checks don't have X.
			// checkbufX(e->idx, W);
		}
	} else {
		xidx group = grefmeta(G, ~idx).group;
		xinst shape = subsetIE_znum(*(fhk_subset *) srefV(S, group));
		for(xinst i=0; i<=shape; i++) sp[i].u8[SP8_FLAGS] = SPK8;
	}
	int64_t ecp = m->e_cparam;
	fhk_edgeX *e = m->ex;
	for(int64_t ei=0; ei<ecp; ei++, e++) {
		checkbufV(e->map, W);
		checkanyX(e->map, W);
		checkbufX(e->idx, W);
	}
}

/*
 * expand model/derive for evaluation:
 * (expand_mod_X is not assumed to be called, so that pre-solved edges will also work)
 *   -> edge maps (-,p,r)      VX
 *   -> computed params        --
 *   -> pre-solved params      --
 *   -> given params           -X
 *   -> returns                VX
 */
static void expandbufV(xidx idx, fhk_frameC *F, void *W) {
	fhk_sp *sp = srefX(S, ~idx);
	// HX may or may not be set, depending on whether this model was presolved or no.
	assert(!(((uint8_t *)sp)[-1] & HV));
	((uint8_t *) sp)[-1] |= HV;
	fhk_Gref G = srefS(S)->G;
	fhk_model *m = grefobj(G, idx);
	int64_t end;
	int64_t ep = m->e_param;
	if(grefmeta(G, ~idx).tag & TAG_DERIVE) {
		end = ep;
		checkbufV(idx, W);
		// X automatically exists, because this is a derive.
	} else {
		end = m->e_return;
		for(int64_t ei=ep; ei<end; ei++) {
			xidx idx = m->ex[ei].idx;
			checkbufV(idx, W);
			checkbufX(idx, W);
		}
	}
	for(int64_t ei=0; ei<end; ei++) {
		xidx map = m->ex[ei].map;
		checkbufV(map, W);
		checkanyX(map, W);
	}
	for(int64_t ei=m->e_xcparam; ei<ep; ei++)
		checkbitmapX(m->ex[ei].idx, W);
	// fixup pointer if needed: if we recursed here and V wasn't yet allocated,
	// we stored an uninitialized pointer, so fix that now.
	if(UNLIKELY(F->base == WBASE)) return;
	fhk_model *fm = grefobj(G, F->idx);
	fhk_edgeX *fe = fm->ex + F->ei;
	fhk_subset ss = map_subset_unchecked(fe->map, F->m_inst);
	if(LIKELY(subset_isI(ss))) {
		xidx vidx = fe->idx;
		fhk_cedge *ce = F->ce + edgeP_order(fe->info);
		size_t size = grefmeta(G, ~vidx).size;
		ce->p = srefV(S, vidx) + size*subsetI_first(ss);
	}
}

/* ---- main functions ---------------------------------------- */

#define reg(name) _reg_##name
#define root(name) _root_##name

NO_ASAN
static int solver_chain(xidx root(X), xinst root(I), void *root(W)) {
	int64_t reg(1); int64_t reg(2); int64_t reg(3); int64_t reg(4);
	void *reg(P1); void *reg(P2);
	float reg(A); float reg(B); float reg(C); float reg(D);
	fhk_frameW *W;

/* enter base. */
	{
		xidx idx = root(X);
		xinst inst = root(I);
		W = (fhk_frameW *)((int64_t *)root(W)+1) - 1;
		fhk_mem_commit_head(srefS(S)->mem, (intptr_t) (W+1));
		W->base = WBASE;
		fhk_Gref G = srefS(S)->G;
		fhk_sp *sp = srefX(S, ~idx);
		if(UNLIKELY((int32_t)sp[inst].u32[SP32_COST] < 0))
			yield_err_cycle();
		sp[inst].u32[SP32_COST] = F32INFN;
		uint8_t tag = grefmeta(G, ~idx).tag;
		assert(tag & TAGM_ISCOMP);
		reg(1) = idx;
		reg(2) = inst;
		reg(B) = FLT_MAX;
		if(tag & TAG_DERIVE) {
			reg(P1) = sp;
			goto enter_derive;
		} else {
			reg(P1) = sp + inst;
			goto enter_computed;
		}
	}

/*
 * enter computed variable.
 *   1  : var idx
 *   2  : var inst
 *   P1 : sp *  ( (fhk_sp *)srefX(S, ~idx) + inst )
 *   B  : beta
 */
enter_computed:
	{
		xidx var = reg(1);
		xinst inst = reg(2);
		fhk_Gref G = srefS(S)->G;
		fhk_var *x = grefobj(G, var);
		int64_t nh = x->nh;
		fhk_edgeH *heapx = x->heap;
		reg(D) = heapx[-1].c; // heapx[-1].c is initial delta, not a real cost.
		heapx -= nh;
		fhk_frameW *W_ = W;
		fhk_edgeH *heapw = (fhk_edgeH *) (W+1);
		W = (fhk_frameW *) (heapw+nh);
		fhk_mem_commit_head(srefS(S)->mem, (intptr_t) (W+1));
		int h = nh;
		for(;;) {
			memcpy(heapw, heapx, SOLVER_HEAP_COPY_UNROLL*sizeof(*heapw));
			h -= SOLVER_HEAP_COPY_UNROLL;
			if(h <= 0) break;
			heapx += SOLVER_HEAP_COPY_UNROLL;
			heapw += SOLVER_HEAP_COPY_UNROLL;
		}
#if FHK_TRACEON(solver)
		W->v_idx = var;
#endif
		W->nh = nh;
		W->v_sp = reg(P1);
		W->v_inst = inst;
		W->beta = reg(B);
		W->link = (intptr_t)W - (intptr_t)W_;
		W->tol = 0x75; // initial exponent: 01110101 = 2^-10
		trace(ENTERV, (intptr_t)W-(intptr_t)mem_W(srefS(S)->mem), fhk_debug_sym(G, var), (int)inst, W->beta);
		goto enter_cand;
	}

/*
 * enter candidate.
 *   2  : var instance
 *   B  : beta
 *   D  : delta
 */
enter_cand:
	{
		xidx model = wtop(W)->idx;
		xidx map = wtop(W)->map;
		xidx inst = reg(2);
		reg(1) = model;
		fhk_subset ss = map_subset_unchecked_biasI(map, inst);
		// fast path: we have a unique instance for the candidate.
		if(LIKELY(subset_is1(ss))) {
			reg(2) = ss;
			goto enter_checkcand;
		}
		// is the subset known?
		if(UNLIKELY(subset_isU(ss))) {
			eval_anymap(map, inst, W+1);
			goto enter_cand; // retry with the actual value
		}
		// no candidates in the subset?
		if(UNLIKELY(subset_isE(ss))) goto candidate_reject;
		// slow path: it's either an interval or complex.
		// we must now find the instance that becomes our candidate,
		// and patch delta to be the next best lowbound.
		fhk_sp *sp = srefX(S, ~model);
		fhk_pkref pk = 0;
		xinst i, zn;
		if(LIKELY(subset_isI(ss))) {
			i = subsetI_first(ss);
			zn = subsetIE_znum(ss);
		} else {
			pk = subsetC_pk(ss);
			i = pkref_first(pk);
			zn = pkref_znum(pk);
		}
		xinst minst = 0;
		int32_t delta = fu32(reg(D));
		int32_t cost = F32INF;
		for(;;) {
			// here we compare the fp costs as signed integers.
			// why does this work? positive floats compare in the same order
			// as integers, while negative floats compare in the reverse order.
			// all our possible values are positive, with the exception of the cycle marker.
			// the integer comparison will therefore select the lowest non-negative cost
			// OR the cycle marker if any instance has it set.
			// entering the cycle marker will eventually raise an error due to one of its
			// parameters (or maps or checks), which is what we want.
			int32_t c = sp[i].u32[SP32_COST];
			minst = c <= cost ? i : minst;
			delta = min(delta, max(cost, c));
			cost = min(cost, c);
			if(--zn < 0) {
				if(LIKELY(!pk)) break;
				pk = pkref_next(pk);
				i = pkref_first(pk);
				zn = pkref_znum(pk);
				pk = pkref_more(pk) ? pk : 0;
			} else {
				i++;
			}
		}
		if(UNLIKELY(cost > delta)) {
			reg(D) = uf32(cost);
			goto candidate;
		}
		reg(2) = minst;
		wtop(W)->c = uf32(delta);
		reg(D) = uf32(delta);
		goto enter_checkcand;
candidate_reject:
		{
			reg(D) = INFINITY;
			goto candidate;
		}
	}

/*
 * verify candidate and enter.
 *   1  : model idx
 *   2  : model instance
 *   B  : beta
 *   D  : delta
 */
enter_checkcand:
	{
		xidx model = reg(1);
		xinst inst = reg(2);
		fhk_sp *sp = (fhk_sp *)srefX(S, ~model);
		reg(P1) = sp;
		if(UNLIKELY(sp[inst].u8[SP8_FLAGS] & SPC8)) {
			fhk_sp *xsp = W->v_sp;
			if(UNLIKELY(sp[inst].u8[SP8_FLAGS] & SPV8)) {
				// the model has already been evaluated.
				// there's 2 possible cases here:
				//   (1) the variable has this chain as its speculated chain.
				//   (2) the variable has some other chain as its speculated chain.
				// in case (2) the speculated chain must have the same cost, since it was not
				// overwitten when this model was evaluated.
				// in either case, the variable already has both a chain and a value,
				// so we can just toggle the C flag.
				assert(xsp->u8[SP8_FLAGS] & SPV8);
				xsp->u8[SP8_FLAGS] |= SPC8;
			} else {
				// otherwise, the model has not been evaluated yet, so we don't care if
				// the variable has a speculated value. we will be overwriting it anyway.
				xsp->state = SP_FLAGS32(SPC8) | (inst << 8) | wtop(W)->ei;
			}
			trace(CHAINC, relW(W), fhk_debug_sym(srefS(S)->G, W->v_idx), W->v_inst,
					fhk_debug_sym(srefS(S)->G, model), (int)inst, sp->cost);
			reg(D) = sp->cost;
			goto exit_chosen;
		}
		trace(ENTERC, relW(W), fhk_debug_sym(srefS(S)->G, model), (int)inst, reg(B), reg(D));
		goto enter_mod;
	}

/*
 * enter derive.
 *   1  : derive idx
 *   2  : derive instance
 *   P1 : sp *   ( model base  srefX(S, ~model) )
 *   B  : beta
 */
enter_derive:
	{
		fhk_sp *sp = reg(P1);
		xinst inst = reg(2);
		W = (void *)W + sizeof(fhk_edgeH) + sizeof(*W);
		fhk_mem_commit_head(srefS(S)->mem, (intptr_t) (W+1));
		wtop(W)->idx = reg(1);
		wtop(W)->c = INFINITY;
#if FHK_TRACEON(solver)
		W->v_idx = wtop(W)->idx;
#endif
		W->v_sp = sp + inst;
		W->link = sizeof(fhk_edgeH) + sizeof(*W);
		W->beta = reg(B);
		reg(D) = INFINITY;
		trace(ENTERD, relW(W), fhk_debug_sym(srefS(S)->G, reg(1)), (int)reg(2), reg(B));
		goto enter_mod;
	}

/*
 * enter model or derive.
 *   1  : model idx
 *   2  : model instance
 *   P1 : sp *    (model base  srefX(S, ~model) )
 *   B  : beta
 *   D  : delta
 */
enter_mod:
	{
		xidx model = reg(1);
		xidx inst = reg(2);
		W->m_inst = inst;
		fhk_sp *sp = reg(P1);
		fhk_Gref G = srefS(S)->G;
		reg(P1) = grefobj(G, model);
mod_retry:
		// SPK implies HX
		if(sp[inst].u8[SP8_FLAGS] & SPK8) goto checks_ok;
		if(LIKELY(((uint8_t *)sp)[-1] & HX)) goto checks;
		expandbufX(model, W+1);
		goto mod_retry;
	}

/*
 * walk check edges.
 *   2  : model instance
 *   P1 : model *    ( grefobj(G, reg(X)) )
 *   B  : beta (not inverse)
 *   D  : delta (not inverse)
 */
checks:
	{
		xinst inst = reg(2);
		fhk_model *m = reg(P1);
		float lim = min(reg(B), reg(D));
		int64_t ci = -(int64_t)m->e_check;
		float penalty = 0;
		for(;;) {
			fhk_edgeC *ce = m->ec + ci;
			fhk_bmword *bm = srefV(S, ce->idx);
			fhk_subset ss;
check_retry:
			ss = map_subset_unchecked(ce->map, inst);
			fhk_pkref pk = 0;
			fhk_bmword mask;
			xinst i, zn;
			if(LIKELY(subset_isI(ss))) {
				i = subsetI_first(ss);
				zn = subsetIE_znum(ss);
			} else if(UNLIKELY(subset_isU(ss))) {
				eval_anymap(ce->map, inst, W+1);
				goto check_retry;
			} else if(UNLIKELY(subset_isE(ss))) {
				goto check_next;
			} else {
				pk = subsetC_pk(ss);
				i = pkref_first(pk);
				zn = pkref_znum(pk);
			}
check_interval:
			mask = zeros(i&63);
			zn += i&63;
			i &= ~63;
			int64_t bmidx = bitmap_idx(i);
			fhk_bmword F = bm[bmidx] & mask;
			fhk_bmword M = bm[~bmidx] & mask;
			for(;;) {
				if(LIKELY(F)) {
					int fail = bitmapW_ffs(F);
					if(LIKELY(fail <= zn)) goto check_penalty;
				}
				if(UNLIKELY(M)) {
					int missing = bitmapW_ffs(M);
					if(LIKELY(missing <= zn)) {
						eval_guard(ce->idx, i+missing, W+1);
						F |= M & bm[bmidx];
						M &= bm[~bmidx];
						continue;
					}
				}
				zn -= 64;
				if(zn >= 0) {
					i += 64;
					bmidx++;
					F = bm[bmidx];
					M = bm[~bmidx];
					continue;
				}
				if(UNLIKELY(pk)) {
					pk = pkref_next(pk);
					i = pkref_first(pk);
					zn = pkref_znum(pk);
					pk = pkref_more(pk) ? pk : 0;
					goto check_interval;
				}
				break;
			}
check_next:
			if(++ci >= 0) break;
			continue;
check_penalty:
			trace(PENALTY, relW(W), ~(int)ci, fhk_debug_sym(srefS(S)->G, wtop(W)->idx),
					W->m_inst, fhk_debug_sym(srefS(S)->G, ce->idx),
					fhk_debug_sym(srefS(S)->G, ce->map),
					ce->penalty, penalty+ce->penalty, lim);
			penalty += ce->penalty;
			if(UNLIKELY(penalty <= lim)) goto check_next;
			reg(D) = penalty;
			goto bound;
		}
		if(penalty > 0) {
			reg(B) = lim;
			reg(C) = costf_inv(m, penalty);
			goto enter_params;
		} else {
			fhk_sp *sp = (fhk_sp *)srefX(S, ~(int64_t)wtop(W)->idx) + W->m_inst;
			sp->u8[SP8_FLAGS] = SPK8;
			goto checks_ok;
		}
	}

/*
 * apply checks passed bonus and jump to edges.
 *   2  : model instance
 *   P1 : model *
 *   B  : beta (not inverse)
 *   D  : delta (not inverse)
 */
checks_ok:
	{
		fhk_model *m = reg(P1);
		reg(D) = max(reg(D), m->bonus);
		reg(B) = min(reg(B), reg(D));
		reg(C) = 0;
		wtop(W)->c = reg(D);
		goto enter_params;
	}

/*
 * start iterating parameter edges.
 *   2  : model instance
 *   P1 : model *
 *   B  : min(beta, delta) (NOT INVERSE)
 *   C  : cost INVERSE
 */
enter_params:
	{
		fhk_model *m = reg(P1);
		float bi = costf_inv(m, reg(B));
		W->bi = bi;
		W->p_pk = 0;
		reg(1) = m->e_cparam;
		reg(B) = bi;
		goto param;
	}

/*
 * setup next computed parameter edge.
 *   1  : edge index
 *   2  : model instance
 *   P1 : model *
 *   B  : beta' inverse
 *   C  : cost inverse
 */
param:
	{
		int64_t ei = reg(1);
		if(--ei < 0) goto solved;
		reg(1) = ei;
		W->p_ei = ei;
		W->ci = reg(C);
		fhk_model *m = reg(P1);
		xidx inst = reg(2);
		fhk_edgeX *e = m->ex + ei;
		reg(P2) = e;
		reg(A) = 0;
		fhk_subset ss;
param_retry:
		ss = map_subset_unchecked(e->map, inst);
		if(LIKELY(subset_isI(ss))) {
			reg(3) = subsetI_first(ss);
			reg(4) = subsetIE_znum(ss);
			assert(!W->p_pk); // should be zeroed on enter and after iteration
			goto param_edge;
		}
		if(UNLIKELY(subset_isU(ss))) {
			eval_anymap(e->map, inst, W+1);
			goto param_retry;
		}
		if(UNLIKELY(subset_isE(ss))) goto param;
		fhk_pkref pk = subsetC_pk(ss);
		reg(3) = pkref_first(pk);
		reg(4) = pkref_znum(pk);
		W->p_pk = pk;
		goto param_edge;
	}

/*
 * walk computed parameter edge.
 *   1  : edge index
 *   2  : model instance
 *   3  : start
 *   4  : znum
 *   P1 : model *
 *   P2 : edgeX *
 *   A  : edge cost
 *   B  : beta inverse
 *   C  : cost inverse
 */
param_edge:
	{
		fhk_model *m = reg(P1);
		fhk_edgeX *e = reg(P2);
		fhk_sp *sp = srefX(S, ~(int64_t)e->idx);
		xinst inst = reg(3);
		xinst znum = reg(4);
		float ce = reg(A);
		float bi = reg(B);
		float ci = reg(C);
		for(;;) {
			float cost = sp[inst].cost;
			ce = max(ce, cost);
			// this check also skips cycles: cost = -inf in that case.
			float xcost = ci + cost;
			if(UNLIKELY(xcost > bi)) {
				reg(D) = costf(m, xcost);
				goto bound;
			}
			if(UNLIKELY(!(sp[inst].u8[SP8_FLAGS] & SPC8))) {
				if(UNLIKELY(cost < 0)) yield_err_cycle();
				// set cycle detection mark.
				// this will be automatically cleared when the var/derive is exited
				// and the cost is updated.
				sp[inst].u32[SP32_COST] = F32INFN;
				// pack up our stuff, it's recursion time.
				W->p_ce = ce;
				W->p_inst = inst;
				W->p_znum = znum;
				reg(1) = e->idx;
				reg(2) = inst;
				reg(B) = bi - ci;
				if(edgeP_isderive(e->info)) {
					reg(P1) = sp;
					goto enter_derive;
				} else {
					reg(P1) = sp + inst;
					goto enter_computed;
				}
			}
			if(--znum < 0) {
				fhk_pkref pk = W->p_pk;
				if(LIKELY(!pk)) break;
				pk = pkref_next(pk);
				inst = pkref_first(pk);
				znum = pkref_znum(pk);
				W->p_pk = pkref_more(pk) ? pk : 0;
				continue;
			}
			inst++;
		}
		trace(PARAM, relW(W), (int)reg(1), fhk_debug_sym(srefS(S)->G, wtop(W)->idx),
				(int)reg(2), fhk_debug_sym(srefS(S)->G, m->ex[reg(1)].idx),
				fhk_debug_sym(srefS(S)->G, m->ex[reg(1)].map),
				ce, ci+ce, reg(B));
		reg(C) = ci + ce;
		goto param;
	}

/*
 * model chain solved
 *   2  : model instance
 *   B  : beta' inverse
 *   C  : cost inverse
 *   P1 : model *
 */
solved:
	{
		xinst inst = reg(2);
		float ci = reg(C);
		fhk_model *m = reg(P1);
		fhk_sp *spm = (fhk_sp *)srefX(S, ~(int64_t)wtop(W)->idx) + inst;
		// we can set SPC now even if we may end up with an infinite cost, that's fine.
		spm->state = SP_FLAGS32(SPC8);
		float cost = costf(m, ci);
		spm->cost = cost;
		trace(CHAINM, relW(W), fhk_debug_sym(srefS(S)->G, wtop(W)->idx), (int)inst, cost, ci);
		if(LIKELY(!m->n_rcheck)) {
			fhk_sp *spv = W->v_sp;
			spv->state = SP_FLAGS32(SPC8) | (inst << 8) | wtop(W)->ei;
			spv->cost = cost;
		} else {
			// this handles rchecks and increases spm->cost if needed.
			eval_modcall(wtop(W)->idx, inst, W+1);
			cost = spm->cost;
			fhk_sp *spv = W->v_sp;
			float delta = wtop(W)->c;
			// we have a better candidate?
			if(cost > delta) {
				// better candidate under beta, go back.
				if(delta <= W->beta) goto candidate;
				// chain not solved, but we know we don't have a solution under beta.
				reg(D) = cost;
				spv->cost = cost;
				goto exit_bound;
			}
			// this is still the best candidate. we solved the variable.
			// the modcall already wrote the chain for us, we just need to set the C flag.
			assert(spv->state == (SP_FLAGS32(SPV8) | (inst << 8) | wtop(W)->ei));
			spv->u8[SP8_FLAGS] |= SPC8;
			spv->cost = cost;
			// did we go over bound?
			if(cost > W->beta) {
				reg(D) = cost;
				goto exit_bound;
			}
		}
		if(spm != W->v_sp)
			trace(CHAINV, relW(W), fhk_debug_sym(srefS(S)->G, W->v_idx), W->v_inst,
					fhk_debug_sym(srefS(S)->G, wtop(W)->idx), (int)inst, cost, ci);
		reg(D) = cost;
		goto exit_chosen;
	}

/*
 * chain chosen -> exit variable/derive.
 *   D : chain cost
 */
exit_chosen:
	{
		// return to the edge
		W = (void*)W - W->link;
		if(UNLIKELY(W->base == WBASE)) return 0;
		reg(1) = W->p_ei;
		reg(2) = W->m_inst;
		fhk_Gref G = srefS(S)->G;
		fhk_model *m = grefobj(G, wtop(W)->idx);
		reg(P1) = m;
		reg(B) = W->bi;
		float ci = W->ci;
		float ce = max(W->p_ce, reg(D));
		xinst znum = W->p_znum;
		xinst inst;
		if(--znum < 0) {
			fhk_pkref pk = W->p_pk;
			if(LIKELY(!pk)) {
				trace(TAILP, relW(W), W->p_ei,
						fhk_debug_sym(srefS(S)->G, wtop(W)->idx), W->m_inst,
						fhk_debug_sym(srefS(S)->G, m->ex[W->p_ei].idx),
						fhk_debug_sym(srefS(S)->G, m->ex[W->p_ei].map),
						ce, ci+ce, W->bi);
				reg(C) = ci + ce;
				goto param;
			}
			inst = pkref_first(pk);
			znum = pkref_znum(pk);
			W->p_pk = pkref_more(pk) ? pk : 0;
		} else {
			inst = W->p_inst + 1;
		}
		reg(3) = inst;
		reg(4) = znum;
		reg(P2) = m->ex + reg(1);
		reg(A) = ce;
		reg(C) = ci;
		goto param_edge;
	}

/*
 * hit cost bound.
 *   2  : model instance
 *   D  : cost after bound hit (actual cost, not inverse!)
 *        jumper must ensure NOT cost <= delta <= beta (EXCEPT if jumping from parameter edge)
 */
bound:
	{
		xinst inst = reg(2);
		fhk_sp *sp = (fhk_sp *)srefX(S, ~(int64_t)wtop(W)->idx) + inst;
		sp->cost = reg(D);
		// more candidates left?
		float delta = wtop(W)->c;
		trace(BOUND, relW(W), fhk_debug_sym(srefS(S)->G, wtop(W)->idx), (int)inst, reg(D), W->beta, delta);
		if(delta <= W->beta) {
			if(LIKELY(reg(D) > delta)) goto candidate;
			// stalling due to rounding error (we have ci > bi but cost <= delta <= beta).
			// we'll keep increasing delta until either the model passes or fails with
			// cost > original delta.
			reg(1) = W->p_ei;
			reg(3) = W->p_inst;
			reg(4) = W->p_znum;
			fhk_model *m = grefobj(srefS(S)->G, wtop(W)->idx);
			reg(P1) = m;
			reg(P2) = m->ex + reg(1);
			reg(A) = W->p_ce;
			reg(B) = W->bi + uf32((uint32_t)W->tol << 22);
			reg(C) = W->ci;
			trace(TOLER, relW(W), fhk_debug_sym(srefS(S)->G, wtop(W)->idx), (int)inst, W->tol, reg(B));
			W->tol++;
			goto param_edge;
		}
		reg(D) = min(reg(D), delta);
		sp = W->v_sp;
		sp->cost = reg(D);
		goto exit_bound;
	}

/*
 * hit cost bound with min(cost, delta) > beta  -->  exit variable/derive.
 *   D  : W->v_sp->cost
 */
exit_bound:
	{
		assert(reg(D) == W->v_sp->cost);
		trace(BOUNDV, relW(W), fhk_debug_sym(srefS(S)->G, W->v_idx), W->v_inst, reg(D));
		W = (void*)W - W->link;
		if(UNLIKELY(W->base == WBASE)) return 1;
		fhk_Gref G = srefS(S)->G;
		fhk_model *m = grefobj(G, wtop(W)->idx);
		reg(2) = W->m_inst;
		reg(D) = costf(m, W->ci + reg(D));
		goto bound;
	}

/*
 * try next candidate. must have reg(D) > delta to guarantee forward progress.
 *   D  : cost
 */
candidate:
	{
		int nh = W->nh;
		assert(nh > 0);
		assert(reg(D) > wtop(W)->c);
		reg(2) = W->v_inst;
		reg(B) = W->beta;
		// reg(D) stays as cost if nh=1: we'll pick delta from the subset.
		if(UNLIKELY(nh == 1)) goto enter_cand;
		float cost = reg(D);
		fhk_edgeH *heap = wheap(W);
		if(nh == 2) {
			if(UNLIKELY(cost <= heap[-2].c)) goto enter_cand;
			uint32_t a = heap[-1].u32[EH_EDGE];
			uint32_t b = heap[-2].u32[EH_EDGE];
			heap[-1].c = cost;
			heap[-1].u32[EH_EDGE] = b;
			heap[-2].c = cost;
			heap[-2].u32[EH_EDGE] = a;
			// reg(D) stays as cost
		} else {
			int64_t end = -nh;
			uint64_t v = ((uint64_t)heap[-1].u32[EH_EDGE] << 32) | fu32(cost);
			uint64_t lv = heap[-2].u64;
			uint64_t rv = heap[-3].u64;
			// note: comparisons are i32 here so that we will always pick a candidate
			// if it has a cycle mark.
			uint64_t iv = (int32_t)lv < (int32_t)rv ? lv : rv;
			if(UNLIKELY((int32_t)v <= (int32_t)iv)) goto enter_cand;
			heap[-1].u64 = iv;
			int64_t i = (int32_t)lv < (int32_t)rv ? -2 : -3;
			for(;;) {
				int64_t j = i << 1;
				lv = heap[j].u64;
				rv = heap[j-1].u64;
				if(j <= end) {
					if(j == end && (int32_t)lv < (int32_t)v) {
						heap[i].u64 = lv;
						i = j;
					}
					break;
				}
				iv = (int32_t)lv < (int32_t)rv ? lv : rv;
				if((int32_t)v <= (int32_t)iv) break;
				heap[i].u64 = iv;
				i = j - ((int32_t)rv <= (int32_t)lv);
			}
			assert(i < 0 && i >= end);
			heap[i].u64 = v;
			float lc = heap[-2].c;
			float rc = heap[-3].c;
			reg(D) = min(lc, rc);
			heap[-1].c = reg(D);
		}
		goto enter_cand;
	}

}

AINLINE static void inline_eval_given_interval(xidx idx, xinst first, xinst zn, fhk_bmword *bmbase) {
	assert(bmbase == srefX(S, ~idx));
	fhk_bmword *bm = bmbase + bitmap_idx(first);
	fhk_bmword M = *bm & zeros(first&63);
	zn += first&63;
	first &= ~63;
	for(;;) {
		while(M) {
			int missing = bitmapW_ffs(M);
			if(missing > (int)zn) break;
			eval_given(idx, first+missing);
			M &= *bm;
		}
		zn -= 64;
		if(zn < 0) break;
		first += 64;
		M = *++bm;
	}
}

static void eval_given_interval(xidx idx, xinst first, xinst zn, fhk_bmword *bmbase) {
	inline_eval_given_interval(idx, first, zn, bmbase);
}

static void eval_checkident(xidx idx) {
	int32_t znum = subsetIE_znum(*(fhk_subset *) srefV(S, idx));
	if(UNLIKELY(znum > srefS(S)->ident))
		fhk_mem_grow_ident(S, znum);
}

static void eval_modcall(xidx root(M), xinst root(I), void *root(W)) {
	int64_t reg(1); int64_t reg(2); int64_t reg(3); int64_t reg(4);
	void *reg(P1); void *reg(P2); void *reg(P3);

#if FHK_x64 && 0
	// gcc has some trouble with register allocation here, so help it out.
	// normally the register hint would be ignored, but coupled with the asm
	// statement gcc has to put it in the register we want.
	// this actually seems to improve register allocation.
	register fhk_Gref G asm("r13") = srefS(S)->G;
	register fhk_frameC *F asm("r14");
#define LABEL(label) label: asm volatile ( "" : "=&r" (G), "=&r" (F));
#else
	fhk_Gref G = srefS(S)->G;
	fhk_frameC *F;
#define LABEL(label) label:
#endif

	void *W;

/* enter root modcall. */
	{
		F = (fhk_frameC *)((int64_t *)root(W)+1) - 1;
		W = F+1;
		fhk_mem_commit_head(srefS(S)->mem, (intptr_t) W);
		F->base = WBASE;
		reg(1) = root(M);
		reg(2) = root(I);
		goto enter;
	}

/*
 * enter modcall.
 *   1  : idx
 *   2  : inst
 */
LABEL(enter)
	{
		xidx idx = reg(1);
		// we are not guaranteed to have an sp yet (for pre-solved models).
		checkbufX(idx, W);
		// this must be called with old F to fixup uninitialized parameter pointer
		if(UNLIKELY(!(((uint8_t *)srefX(S, ~idx))[-1] & HV)))
			expandbufV(idx, F, W);
		fhk_model *m = grefobj(G, idx);
		// always allocate 1 extra edge for derives.
		// in case of non-derive we may temporarily waste 16 bytes of scratch space.
		// no big deal.
		void *WW = W + sizeof(fhk_frameC) + (ptrdiff_t)(m->e_return+1)*sizeof(fhk_cedge);
		fhk_mem_commit_head(srefS(S)->mem, (intptr_t) WW);
		((fhk_frameC *)W)->link = (intptr_t)W - (intptr_t)F;
		F = W;
		W = WW;
		F->m_inst = reg(2);
		F->idx = idx;
		F->c_pk = 0;
		reg(1) = m->e_xcparam;
		reg(P1) = m;
		trace(EVALM, relW(W), fhk_debug_sym(G, idx), (int)reg(2));
		goto paramxc;
	}

/*
 * collect non-given parameter.
 *   1  : edge index
 *   2  : model instance
 *   P1 : model *
 */
LABEL(paramxc)
	{
		int64_t ei = reg(1);
		if(--ei < 0) goto paramg;
		reg(1) = ei;
		F->ei = ei;
		xinst inst = reg(2);
		fhk_model *m = reg(P1);
		fhk_edgeX *e = m->ex + ei;
		fhk_cedge *ce = F->ce + edgeP_order((ptrdiff_t)e->info);
		fhk_subset ss = map_subset_unchecked(e->map, inst);
		assert(!subset_isU(ss)); // solver has visited it.
		xidx idx = e->idx;
		size_t size = grefmeta(G, ~idx).size;
		reg(P2) = e;
		reg(P3) = srefX(S, ~idx);
		if(LIKELY(subset_isI(ss))) {
			reg(3) = subsetI_first(ss);
			reg(4) = subsetIE_znum(ss);
			// note: the V-pointer is not necessarily allocated yet, and may be null.
			// that's fine: it means we will recurse and expandbufV will fixup the pointer for us.
			ce->p = srefV(S, idx) + size*reg(3);
			ce->n = reg(4) + 1;
			assert(!F->c_pk);
			goto paramxc_edge;
		}
		if(UNLIKELY(subset_isE(ss))) {
			ce->p = NULL;
			ce->n = 0;
			goto paramxc;
		}
		fhk_pkref pk = subsetC_pk(ss);
		reg(3) = pkref_first(pk);
		reg(4) = pkref_znum(pk);
		ce->p = W;
		ce->n = 0;
		F->c_n = &ce->n;
		F->c_size = size;
		F->c_pk = pk;
		goto paramxc_edge;
	}

/*
 * walk non-given parameter edge.
 *   1  : edge index
 *   2  : model instance
 *   3  : start
 *   4  : znum
 *   P1 : model *
 *   P2 : edgeX *
 *   P3 : sp *   base
 */
LABEL(paramxc_edge)
	{
		fhk_edgeX *e = reg(P2);
		fhk_sp *sp = reg(P3);
		xinst inst = reg(3);
		xinst znum = reg(4);
		for(;;) {
			if(UNLIKELY(!(sp[inst].u8[SP8_FLAGS] & SPV8))) {
				F->p_inst = inst;
				F->p_znum = znum;
				xidx idx = e->idx;
				if(edgeP_isderive(e->info)) {
					reg(1) = idx;
					reg(2) = inst;
				} else {
					fhk_var *x = grefobj(G, idx);
					uint32_t state = sp[inst].state;
					assert(state & SP_FLAGS32(SPC8));
					reg(1) = vheap(x, ~(uint64_t)sp_ei(state))->idx;
					reg(2) = sp_inst(state);
				}
				goto enter;
			}
			if(--znum < 0) {
				fhk_pkref pk = F->c_pk;
				if(LIKELY(!pk)) break;
				void *vp = srefV(S, e->idx);
				size_t n = 1 + pkref_znum(pk);
				size_t size = F->c_size*n;
				fhk_mem_commit_head(srefS(S)->mem, (intptr_t)W + size);
				memcpy(W, vp + F->c_size*pkref_first(pk), size);
				W += size;
				*F->c_n += n;
				if(!pkref_more(pk)) {
					// always keep W aligned here so that we don't have to mind alignment
					// if we pass it to solver.
					W = ALIGN(W, 8);
					F->c_pk = 0;
					break;
				}
				pk = pkref_next(pk);
				inst = pkref_first(pk);
				znum = pkref_znum(pk);
				F->c_pk = pk;
			} else {
				inst++;
			}
		}
		goto paramxc;
	}

/*
 * collect given parameters.
 *   2  : model instance
 *   P1 : model *
 */
LABEL(paramg)
	{
		xinst inst = reg(2);
		fhk_model *m = reg(P1);
		if(m->e_xcparam == m->e_param) goto returns;
		fhk_edgeX *e = m->ex + m->e_xcparam;
		fhk_edgeX *ep = m->ex + m->e_param;
		for(;;) {
			fhk_cedge *ce = F->ce + edgeP_order((ptrdiff_t)e->info);
			xidx idx = e->idx;
			size_t size = grefmeta(G, ~idx).size;
			fhk_bmword *bm = srefX(S, ~idx);
			fhk_subset ss;
paramg_retry:
			ss = map_subset_unchecked(e->map, inst);
			if(LIKELY(subset_isI(ss))) {
				xinst first = subsetI_first(ss);
				xinst zn = subsetIE_znum(ss);
				ce->n = zn + 1;
				inline_eval_given_interval(idx, first, zn, bm);
				// we must defer setting p here, since V may not be allocated before
				// we first call eval_given.
				ce->p = srefV(S, idx) + first*size;
			} else if(UNLIKELY(subset_isU(ss))) {
				eval_anymap(e->map, inst, W);
				goto paramg_retry;
			} else if(UNLIKELY(subset_isE(ss))) {
				ce->p = NULL;
				ce->n = 0;
			} else {
				// we could align more carefully here, but no point in trying to
				// save a few bytes of temporary storage.
				// it's going to be nuked after the modcall anyway.
				W = ALIGN(W, 8);
				ce->p = W;
				xinst n = 0;
				fhk_pkref pk = subsetC_pk(ss);
				for(;;) {
					xinst first = pkref_first(pk);
					xinst zn = pkref_znum(pk);
					eval_given_interval(idx, first, zn, bm);
					size_t sz = size*(1+zn);
					n += 1+zn;
					fhk_mem_commit_head(srefS(S)->mem, (intptr_t)W + sz);
					// reload vp here because we can't load it before eval_given.
					memcpy(W, srefV(S, idx) + first*size, sz);
					W += sz;
					if(!pkref_more(pk)) break;
					pk = pkref_next(pk);
				}
				ce->n = n;
			}
			e++;
			if((intptr_t)e >= (intptr_t)ep) break;
			continue;
		}
		goto returns;
	}

/*
 * setup return edges and yield modcall.
 *   2  : model instance
 *   P1 : model *
 */
LABEL(returns)
	{
		xinst inst = reg(2);
		srefS(S)->inst = inst;
		fhk_model *m = reg(P1);
		xidx idx = F->idx;
		srefS(S)->idx = idx;
		fhk_cedge *ce = F->ce + m->e_param;
		fhk_sp *sp = srefX(S, ~idx);
		assert((sp[inst].u8[SP8_FLAGS] & (SPC8|SPV8)) == SPC8);
		// models don't store chain info, so we may overwrite the flag byte.
		// this destroys the K flag if it's set, but that's fine,
		// the solver will never enter this model again.
		sp[inst].u8[SP8_FLAGS] = SPC8 | SPV8;
		srefS(S)->edges = F->ce;
		int jmp = idx - grefG(G)->j[jidx(idx)];
		uint8_t tag = grefmeta(G, ~idx).tag;
		if(tag & TAG_DERIVE) {
			void *vp = srefV(S, idx);
			size_t size = grefmeta(G, ~idx).size;
			ce->p = vp + inst*size;
			ce->n = 1;
			yield_jmp(jmp);
			if(UNLIKELY(tag & TAG_GROUP))
				eval_checkident(F->idx);
		} else {
			uint8_t wback = 0;
			fhk_edgeX *e = m->ex + m->e_param;
			fhk_edgeX *er = m->ex + m->e_return;
			for(;;) {
				xidx vidx = e->idx;
				size_t size = grefmeta(G, ~vidx).size;
				fhk_subset ss;
returns_retry:
				ss = map_subset_unchecked_biasI(e->map, inst);
				if(LIKELY(subset_isI(ss))) {
					fhk_sp *vsp = srefX(S, ~vidx);
					xinst i = subsetI_first(ss);
					xinst zn = subsetIE_znum(ss);
					ce->n = zn + 1;
					for(;;) {
						if(vsp[i].u8[SP8_FLAGS] & SPV8) {
							// we could still also direct write in some cases here,
							// but it's rare enough that it's not worth checking.
							// it just costs an extra memcpy after the call, when we
							// do the more granular check.
							size_t num = 1 + subsetIE_znum(ss);
							W = ALIGN(W, 8);
							ce->p = W;
							W += num*size;
							wback = 1;
							break;
						}
						if(--zn < 0) {
							i = subsetI_first(ss);
							zn = subsetIE_znum(ss);
							void *vp = srefV(S, vidx);
							ce->p = vp + size*i;
							uint32_t chain = (inst << 8) | e->info;
							uint32_t chainc = SP_FLAGS32(SPC8) | chain;
							uint32_t chainv = SP_FLAGS32(SPV8) | chain;
							for(;;) {
								uint32_t state = vsp[i].state;
								uint32_t commit = (state & SP_FLAGS32(SPC8)) | chainv;
								// commit our value iff either
								//   (1) state has no C flag                    state ^ chainc < 0
								//   (2) state has C and exactly our chain      state ^ chainc = 0
								vsp[i].state = (int32_t)(state ^ chainc) <= 0 ? commit : state;
								if(--zn < 0) break;
								i++;
							}
							break;
						}
						i++;
					}
				} else if(UNLIKELY(subset_isU(ss))) {
					eval_anymap(e->map, inst, W);
					goto returns_retry;
				} else if(UNLIKELY(subset_isE(ss))) {
					ce->p = (void *) ~(intptr_t)0;
					ce->n = 0;
				} else {
					// complex set. we always need to allocate a buffer here.
					wback = 1;
					W = ALIGN(W, 8);
					ce->p = W;
					size_t num = 0;
					fhk_pkref pk = subsetC_pk(ss);
					for(;;) {
						num += 1 + pkref_znum(pk);
						if(!pkref_more(pk)) break;
						pk = pkref_next(pk);
					}
					ce->n = num;
					W += num*size;
				}
				e++;
				ce++;
				if((intptr_t)e >= (intptr_t)er) break;
			}
			if(UNLIKELY(m->n_rcheck)) {
				// TODO: eval return checks, increase cost
				yield_err_nyi();
			}
			fhk_mem_commit_head(srefS(S)->mem, (intptr_t) W);
			yield_jmp(jmp);
			if(UNLIKELY(wback)) {
				e = m->ex + m->e_param;
				ce = F->ce + m->e_param;
				er = m->ex + m->e_return;
				float cost = sp[inst].cost;
				for(;;) {
					// anything < W is on the work stack and > W is a direct reference.
					void *p = ce->p;
					if(LIKELY((intptr_t)p < (intptr_t)W)) {
						xidx vidx = e->idx;
						void *vp = srefV(S, vidx);
						fhk_sp *vsp = srefX(S, ~vidx);
						fhk_var *x = grefobj(G, vidx);
						size_t size = grefmeta(G, ~vidx).size;
						uint32_t chain = SP_FLAGS32(SPV8) | (inst << 8) | e->info;
						// ss can't be U or E here since we excluded those cases
						// when building the call.
						fhk_subset ss = map_subset_unchecked_biasI(e->map, inst);
						xinst i, zn;
						fhk_pkref pk = 0;
						if(LIKELY(subset_isI(ss))) {
							i = subsetI_first(ss);
							zn = subsetIE_znum(ss);
						} else {
							pk = subsetC_pk(ss);
							i = pkref_first(pk);
							zn = pkref_znum(pk);
						}
						xinst start = i;
						for(;;) {
							// commit when:
							//   CV    never
							//   C-    always
							//   -V    cost < speculated cost
							//   --    always
							uint32_t state = vsp[i].state;
							if(LIKELY(!(state & SP_FLAGS32(SPV8)))) goto wback_commit;
							xidx cidx = vheap(x, ~(uint64_t)sp_ei(state))->idx;
							fhk_sp *csp = srefX(S, ~cidx);
							if(cost < csp[sp_inst(state)].cost) goto wback_commit;
							if(start < i) {
								memcpy(vp + start*size, p, (i-start)*size);
								p += (i-start)*size;
							}
							i++;
							start = i;
							p += size;
							goto wback_next;
wback_commit:
							vsp[i].state = (state & SP_FLAGS32(SPC8)) | chain;
							i++;
wback_next:
							if(--zn < 0) {
								if(start < i)
									memcpy(vp + start*size, p, (i-start)*size);
								if(UNLIKELY(pk)) {
									p += (i-start)*size;
									pk = pkref_next(pk);
									i = pkref_first(pk);
									zn = pkref_znum(pk);
									start = i;
									pk = pkref_more(pk) ? pk : 0;
									continue;
								}
								break;
							}
						}
					}
					e++;
					ce++;
					if((intptr_t)e >= (intptr_t)er) break;
				}
			}
			if(UNLIKELY(tag & TAG_GROUP)) {
				e = m->ex + m->e_param;
				er = m->ex + m->e_return;
				do {
					if(LIKELY(grefmeta(G, ~(xidx)e->idx).tag & TAG_GROUP))
						eval_checkident(e->idx);
					e++;
				} while((intptr_t)e < (intptr_t)er);
			}
		}
	}

/* we are done, return. */
	{
		W = F;
		F = (void*)F - F->link;
		if(UNLIKELY(F->base == WBASE)) return;
		int64_t ei = F->ei;
		reg(1) = ei;
		reg(2) = F->m_inst;
		fhk_model *m = grefobj(G, F->idx);
		reg(P1) = m;
		// if this was the last instance in the edge and we don't have
		// a complex subset to deal with, we can just jump straight to the
		// next edge and avoid restoring state.
		// this is eg. all unit subset edges.
		if(!F->p_znum && !F->c_pk) goto paramxc;
		// otherwise we have to go back.
		// it we have a complex subset we need to collect the param values,
		// so we just repeat the edge.
		// the sp check is not expensive anyway.
		reg(3) = F->p_inst;
		reg(4) = F->p_znum;
		fhk_edgeX *e = m->ex + ei;
		reg(P2) = e;
		fhk_sp *sp = srefX(S, ~(int64_t)e->idx);
		reg(P3) = sp;
		goto paramxc_edge;
	}

#undef LABEL

}

#undef reg
#undef root

/* ---- main loop ---------------------------------------- */

static fhk_bucket *root_find_bucket() {
	fhk_bucket **prev = &srefS(S)->bucket;
	while(*prev) {
		fhk_bucket *bucket = *prev;
		if(bucket->num > 0) {
			*prev = bucket->next;
			return bucket;
		}
		prev = &bucket->next;
	}
	return NULL;
}

static void root_bucket_recycle(fhk_bucket *bucket) {
	bucket->num = 0;
	bucket->next = srefS(S)->bucket;
	srefS(S)->bucket = bucket;
}

// this is a very naive quicksort, could be a lot faster.
// it doesn't matter, this is not the performance sensitive part.
static void root_list_sort(fhk_root *roots, int64_t start, int64_t end) {
#define swap(a, b) do { typeof(a) _a = (a); (a) = (b); (b) = _a; } while(0)
	if(end-start < 32){
		for(int64_t i=start+1;i<end;i++){
			fhk_root x = roots[i];
			int64_t j = i;
			for(;j>0;j--){
				if(roots[j-1] <= x) break;
				roots[j] = roots[j-1];
			}
			roots[j] = x;
		}
		return;
	}
	fhk_root a = roots[start];
	fhk_root b = roots[(start+end)/2];
	fhk_root c = roots[end];
	fhk_root pivot = a < b ? (b < c ? b : a < c ? c : a) : (a < c ? a : b < c ? c : b);
	int i = start-1, j = end+1;
	for(;;) {
		for(;;) if(roots[++i] > pivot) break;
		for(;;) if(roots[--j] < pivot) break;
		if(j <= i) break;
		swap(roots[i], roots[j]);
	}
	// tailcall the bigger interval
	if(end-i < j-start) {
		swap(start, i);
		swap(end, j);
	}
	root_list_sort(roots, start, j);
	root_list_sort(roots, i, end);
#undef swap
}

// TODO: tätä sorttia ei oikeastaan tarvita tässä, koska kaikki queryt tunnetaan
// etukäteen. sortin voi tehdä queryä muodostettaessa.
static void root_bucket_sort(fhk_bucket *bucket) {
	assert(bucket->num > 0);
	root_list_sort(bucket->roots, 0, bucket->num - 1);
}

static void root_computed(xidx idx, fhk_subset ss) {
	fhk_sp *sp = srefX(S, ~idx);
	fhk_pkref pk = 0;
	xinst inst, znum;
	// solve.
	if(LIKELY(subset_isI(ss))) {
		inst = subsetI_first(ss);
		znum = subsetIE_znum(ss);
	} else {
		pk = subsetC_pk(ss);
		inst = pkref_first(pk);
		znum = pkref_znum(pk);
	}
	for(;;) {
		if(LIKELY(!sp_done(sp[inst].u64))) {
			if(UNLIKELY(solver_chain(idx, inst, mem_W(srefS(S)->mem))))
				goto nochain;
		} else if(UNLIKELY(!(sp[inst].u8[SP8_FLAGS] & SPC8))) {
nochain:
			yield_err_chain(idx, inst);
		}
		inst++;
		if(!znum--) {
			if(LIKELY(!pk)) break;
			pk = pkref_next(pk);
			inst = pkref_first(pk);
			znum = pkref_znum(pk);
			pk = pkref_more(pk) ? pk : 0;
		}
	}
	// eval.
	if(LIKELY(subset_isI(ss))) {
		inst = subsetI_first(ss);
		znum = subsetIE_znum(ss);
	} else {
		pk = subsetC_pk(ss);
		inst = pkref_first(pk);
		znum = pkref_znum(pk);
	}
	int derive = grefmeta(srefS(S)->G, ~idx).tag & TAG_DERIVE;
	for(;;) {
		if(LIKELY(derive)) {
			for(;;) {
				if(LIKELY(!(sp[inst].u8[SP8_FLAGS] & SPV8)))
					eval_modcall(idx, inst, mem_W(srefS(S)->mem));
				if(--znum < 0) break;
				inst++;
			}
		} else {
			fhk_Gref G = srefS(S)->G;
			for(;;) {
				if(LIKELY(!(sp[inst].u8[SP8_FLAGS] & SPV8))) {
					uint32_t state = sp[inst].state;
					fhk_var *x = grefobj(G, idx);
					xidx midx = vheap(x, ~(uint64_t)sp_ei(state))->idx;
					eval_modcall(midx, sp_inst(state), mem_W(srefS(S)->mem));
				}
				if(--znum < 0) break;
				inst++;
			}
		}
		if(LIKELY(!pk)) return;
		pk = pkref_next(pk);
		inst = pkref_first(pk);
		znum = pkref_znum(pk);
		pk = pkref_more(pk) ? pk : 0;
	}
}

static void root_given(xidx idx, fhk_subset ss) {
	fhk_bmword *bm = srefX(S, ~idx);
	if(LIKELY(subset_isI(ss))) {
		eval_given_interval(idx, subsetI_first(ss), subsetIE_znum(ss), bm);
	} else {
		fhk_pkref pk = subsetC_pk(ss);
		for(;;) {
			eval_given_interval(idx, pkref_first(pk), pkref_znum(pk), bm);
			if(!pkref_more(pk)) break;
			pk = pkref_next(pk);
		}
	}
}

static void root_bucket_solve(fhk_bucket *bucket) {
	int64_t num = bucket->num;
	fhk_root *r = bucket->roots;
	do {
		fhk_root root = *r++;
		xidx idx = root_idx(root);
		if(UNLIKELY(!srefX(S, ~idx))) {
			if(root & ROOT_COMPUTED)
				newbufX(idx, mem_W(srefS(S)->mem));
			else
				fhk_mem_newbitmapX(S, idx, shapeof_checked(idx, mem_W(srefS(S)->mem)));
		}
		int64_t pos = root_pos(root);
		fhk_selection sel = bucket->sel[pos];
		fhk_subset ss;
		if(root & ROOT_MAP) {
			ss = ((fhk_subset *) srefV(S, (xidx)select_idx(sel)))[(xinst)select_inst(sel)];
			if(UNLIKELY(subset_isE(ss))) continue;
		} else {
			ss = sel;
		}
		assert(!subset_isUE(ss));
		if(root & ROOT_COMPUTED)
			root_computed(idx, ss);
		else
			root_given(idx, ss);
	} while(--num);
}

/*
 * solver entry point.
 * the asm swap function ensures S is set.
 * this function must return when there's no more work to do, and
 * the asm swap function will yield FHK_OK to caller.
 */
NOAPI void fhk_solver_main() {
	for(;;){
		fhk_bucket *bucket = root_find_bucket();
		if(!bucket) {
			trace(JOK);
			return;
		}
		root_bucket_sort(bucket);
		root_bucket_solve(bucket);
		root_bucket_recycle(bucket);
	}
}

/*
 * given k-map rescan.
 * if any kmapg is larger than the current interned ident map,
 * we have to grow the intern.
 */
NOAPI void fhk_solver_kmapg_rescan() {
	fhk_Gref G = srefS(S)->G;
	int32_t ident = srefS(S)->ident;
	int32_t maxkg = 0;
	int32_t i = grefG(G)->kmapg;
	fhk_meta *mp = &grefmeta(G, ~i);
	fhk_subset **vp = (fhk_subset **) &srefV(S, i);
	for(;;) {
		if((mp->tag & TAG_GROUP) && *vp) {
			// if it's empty or undefined, subsetIE_size(ss) = -1.
			maxkg = max(maxkg, subsetIE_size(**vp));
		}
		if(i++ == OBJ_MAXKMAPG) break;
		mp--;
		vp++;
	}
	if(UNLIKELY(maxkg > ident))
		fhk_mem_grow_ident(S, maxkg);
}
