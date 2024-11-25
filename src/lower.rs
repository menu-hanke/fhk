//! Graph -> IR.

use core::cmp::{max, min};
use core::iter::{repeat_n, zip};
use core::mem::swap;

use alloc::vec::Vec;
use enumset::{EnumSet, EnumSetType};

use crate::bitmap::BitMatrix;
use crate::bump::{self, Bump, BumpPtr, BumpRef};
use crate::compile::{self, Ccx, Phase};
use crate::dataflow::{Dataflow, DataflowSystem};
use crate::dump::dump_ir;
use crate::hash::HashMap;
use crate::index::{IndexOption, InvalidValue};
use crate::intrinsics::Intrinsic;
use crate::ir::{self, Bundle, Func, FuncId, FuncKind, Ins, InsId, Opcode, Phi, PhiId, Query, SignatureBuilder, Type, IR};
use crate::lang::Lang;
use crate::mem::{Offset, ResetId, ResetSet, SizeClass};
use crate::obj::{cast_args, cast_args_raw, obj_index_of, FieldType, Obj, ObjRef, ObjectRef, Objects, Operator, CALLN, CALLX, DIM, EXPR, GET, KFP64, KINT, KINT64, KSTR, LOAD, MOD, QUERY, RESET, TAB, TPRI, TTEN, TTUP, VAR, VGET, VSET};
use crate::trace::trace;
use crate::typestate::{Absent, Access, R, RW};
use crate::typing::Primitive;

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct Axis {
    size: ObjRef<EXPR>,
    ret: PhiId,
    rank: u8,
    _pad: u8
}

bump::vla_struct! {
    struct Tab {
        func: FuncId,
        n: u8,
        _pad: u8
    } axes: [Axis; |t| t.n as usize]
}

bump::vla_struct! {
    struct Mod {
        tab: BumpRef<Tab>,
        guard: ObjRef<EXPR>,
        base: FuncId,
        n: u8,
        mt: u8
    } value: [VSet; |m| m.n as usize]
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct VSet {
    obj: ObjRef<VSET>,
    model: BumpRef<Mod>,
    var: BumpRef<Var>,
    ret: PhiId,
    vst: u8,
    _pad: u8
}

bump::vla_struct! {
    struct Var {
        obj: ObjRef<VAR>,
        tab: BumpRef<Tab>,
        base: FuncId,
        n: u8,
        _pad: u8
    } value: [BumpRef<VSet>; |v| v.n as usize]
}

impl Tab {
    const GLOBAL: BumpRef<Tab> = zerocopy::transmute!(0);
}

impl Var {
    const SUB_VALUE: isize = 0;
    const SUB_ARM: isize = 2;
}

impl Mod {
    const SUB_VALUE: isize = 0;
    const SUB_AVAIL: isize = 2;
    const SIMPLE: u8 = 0;
    const COMPLEX: u8 = 1;
}

impl Axis {
    const SCALAR: u8 = 0;
    const VECTOR: u8 = 1;
}

impl VSet {
    // this is the only vset of the model, and it has no indices
    const SIMPLE: u8 = 0;
    // the model instance [i1, ..., iN] returns the variable instance(s) [i1, ..., iN, :, ... :]
    const PREFIX: u8 = 1;
    // the model returns some arbitrary indices
    const COMPLEX: u8 = 2;
}

pub fn decomposition_size(objs: &Objects, idx: ObjRef) -> usize {
    match objs.get(objs.totype(idx)) {
        ObjectRef::TPRI(_) => 1,
        ObjectRef::TTEN(&TTEN { dim, elem, .. }) => dim as usize + decomposition_size(objs, elem),
        ObjectRef::TTUP(TTUP { elems, .. }) => elems.iter().map(|&e| decomposition_size(objs, e)).sum(),
        _ => unreachable!()
    }
}

fn pushdeco(objs: &Objects, idx: ObjRef, deco: &mut Vec<Type>) {
    match objs.get(objs.totype(idx)) {
        ObjectRef::TPRI(&TPRI { ty, ..  }) => {
            deco.push(Primitive::from_u8(ty).to_ir());
        },
        ObjectRef::TTEN(&TTEN { dim, elem, .. }) => {
            deco.extend(repeat_n(Type::PTR, decomposition_size(objs, elem)));
            deco.extend(repeat_n(IRT_IDX, dim as _));
        },
        ObjectRef::TTUP(TTUP { elems, .. }) => {
            for &e in elems {
                pushdeco(objs, e, deco);
            }
        },
        _ => unreachable!()
    }
}

fn decomposition<'objs, 'work>(
    objs: &'objs Objects,
    idx: ObjRef,
    work: &'work mut Vec<Type>
) -> &'work [Type] {
    work.clear();
    pushdeco(objs, idx, work);
    &*work
}

fn typedim(objs: &Objects, idx: ObjRef) -> u8 {
    match objs.get(objs.totype(idx)) {
        ObjectRef::TTEN(&TTEN { dim, .. }) => dim,
        o => {
            debug_assert!(matches!(o, ObjectRef::TPRI(_)));
            1
        }
    }
}

#[derive(EnumSetType)]
enum IdxAttr {
    // expression selects exactly one element from the target table.
    // note that this does NOT mean that the selected element itself is scalar.
    // One,
    // instances of the source table will NOT select overlapping indices.
    Disjoint,
    _3, _4, _5, _6, _7, _8
    // // selects a contiguous range of flat indices.
    // Range,
    // // index is of the form source[i1,...,iN] -> target[i1,...,iN,:,...,:]
    // // implies Disjoint+Range
    // SourcePrefix,
    // // index is of the form target[i1,...,iN,iN+1,...iN+M] -> target[i1,...,iN]
    // TargetPrefix,
    // // the source and target prefix have the same flat index
    // SamePrefix,
}

#[repr(C)] // need repr(C) for transmuting references
pub struct Lower<O=RW, F=RW> {
    bump: Access<Bump<u32>, O>,
    objs: Access<HashMap<ObjRef, BumpRef<()>>, O>,
    expr: HashMap<ObjRef<EXPR>, InsId>,
    // TODO: remove the following tmp_* fields and use ccx.tmp instead:
    tmp_ins: Vec<InsId>, // public for lower_callx
    tmp_vty: Vec<Type>, // for emitvarvalue
    tmp_ty: Vec<Type>, // for expressions
    // current function:
    func: Access<Func, F>, // public for lower_callx
    tab: BumpRef<Tab>,
}

// for emit*
pub type Lcx<'a, 'b, 'c> = Ccx<Lower<R<'a>, R<'b>>, R<'c>>;

// for callx (&mut Lcx -> &mut CLcx is ok because &mut T -> &mut UnsafeCell<T> is ok).
// the point of this is to tell the compiler that lower_callx won't replace the current phase data.
pub type CLcx<'a, 'b, 'c> = Ccx<Access<Lower, R<'a>>, R<'b>, R<'c>>;

// integer type used for indexing
pub const IRT_IDX: Type = Type::I32;
// integer type used for selecting models.
// note: var.def only has 8 bits anyway, so this can't go higher
const IRT_ARM: Type = Type::I8;

// vars, models, and tabs always emit this as ins #1 (where start = #0):
const INS_FLATIDX: InsId = zerocopy::transmute!(1u16);

// expr obj.mark:
const EXPR_NONE: u8 = 0;  // no uses
const EXPR_ONE: u8 = 1;   // one use
const EXPR_MANY: u8 = 2;  // many uses

/* ---- Initialization ------------------------------------------------------ */

fn sizeclass(objs: &Objects, tab: ObjRef<TAB>) -> SizeClass {
    match objs.dim(tab) {
        0 => SizeClass::GLOBAL,
        _ => SizeClass::dynamic_class(tab)
    }
}

fn toann(objs: &Objects, x: ObjRef) -> ObjRef {
    match objs[x].op {
        Obj::VAR => objs[x.cast::<VAR>()].ann,
        op if Operator::is_expr_raw(op) => objs[x.cast::<EXPR>()].ann,
        _ => x
    }
}

fn isscalarann(objs: &Objects, ann: ObjRef) -> bool {
    objs[toann(objs, ann)].op == Obj::TPRI
}

fn createtab(ctx: &mut Ccx<Lower, R>, idx: ObjRef<TAB>, obj: &TAB) {
    let axes = &ctx.objs[obj.shape].fields;
    ctx.data.bump.push(Tab {
        func: ctx.ir.funcs.end(),
        n: axes.len() as _,
        _pad: 0,
        axes: []
    });
    let mut ret: PhiId = 1.into();
    let mut func = Func::new(FuncKind::Bundle(Bundle::new(SizeClass::GLOBAL)));
    let mut sig = func.build_signature().add_return(IRT_IDX);
    for &size in axes {
        let rank = match ctx.objs[ctx.objs[size].ann].op {
            Obj::TPRI => Axis::SCALAR,
            _ => Axis::VECTOR
        };
        ctx.data.bump.push(Axis { size, ret, rank, _pad: 0 });
        match rank {
            Axis::SCALAR => {
                sig = sig.add_return(IRT_IDX);
                ret += 1;
            },
            _ /* VECTOR */ => {
                // forward + backward lookup tables:
                sig = sig.add_return(Type::PTR).add_return(Type::PTR);
                ret += 2;
            }
        }
    }
    sig.finish_returns().finish_args();
    let fid = ctx.ir.funcs.push(func);
    trace!(LOWER "TAB {:?} func: {:?}", idx, fid);
}

fn makeinitfunc(ir: &mut IR) {
    let mut func = Func::new(FuncKind::Bundle(Bundle::new(SizeClass::GLOBAL)));
    func.build_signature().add_return(Type::FX).finish_returns().finish_args();
    ir.funcs.push(func);
}

fn maybeidxarg(
    mut sig: SignatureBuilder<'_, ir::Args>,
    scl: SizeClass
) -> SignatureBuilder<'_, ir::Args> {
    if scl != SizeClass::GLOBAL {
        sig = sig.add_arg(IRT_IDX);
    }
    sig
}

fn createvar(ctx: &mut Ccx<Lower, R>, idx: ObjRef<VAR>, var: &VAR) {
    let lower = &mut *ctx.data;
    let base = ctx.ir.funcs.end();
    lower.bump.push(Var {
        obj: idx.cast(),
        tab: lower.objs[&var.tab.erase()].cast(),
        base,
        n: 0, // will be used as a counter for vsets
        _pad: 0,
        value: []
    });
    lower.bump.reserve_dst::<[VSet]>(var.mark as _);
    let scl = sizeclass(&ctx.objs, var.tab);
    // value:
    {
        let mut func = Func::new(FuncKind::Bundle(Bundle::new(scl)));
        let mut sig = func.build_signature();
        for &ty in decomposition(&ctx.objs, var.ann, &mut lower.tmp_ty) {
            sig = sig.add_return(ty);
        }
        maybeidxarg(sig.finish_returns(), scl).finish_args();
        ctx.ir.funcs.push(func);
    }
    // value.init:
    makeinitfunc(&mut ctx.ir);
    // arm:
    {
        let mut func = Func::new(FuncKind::Bundle(Bundle::new(scl)));
        maybeidxarg(func.build_signature().add_return(IRT_ARM).finish_returns(), scl).finish_args();
        ctx.ir.funcs.push(func);
    }
    // arm.init
    makeinitfunc(&mut ctx.ir);
    trace!(LOWER "VAR {:?} value: {:?}[{:?}] arm: {:?}[{:?}]", idx, base, base+1, base+2, base+3);
}

fn isprefixidx(
    objs: &Objects,
    source: ObjRef<TAB>,
    target: ObjRef<TAB>,
    idx: &[ObjRef<EXPR>]
) -> bool {
    // TODO: analyze explicit indices
    if !idx.is_empty() { return false; }
    if source == target { return true; } // skip
    let sdim = objs.dim(source);
    if sdim == 0 { return true; } // skip
    let tdim = objs.dim(target);
    if sdim > tdim { return false; }
    objs.allequal(
        cast_args(&objs[objs[source].shape].fields),
        cast_args(&objs[objs[target].shape].fields[..sdim])
    )
}

fn issimplemod(objs: &Objects, model: &MOD) -> bool {
    let &[vset] = &model.value else { return false };
    let vset = &objs[vset];
    if !vset.idx.is_empty() { return false };
    objs[vset.var].tab == model.tab
}

fn createmod(ctx: &mut Ccx<Lower, R>, idx: ObjRef<MOD>, obj: &MOD) {
    let lower = &mut *ctx.data;
    let mt = match issimplemod(&ctx.objs, obj) { true => Mod::SIMPLE, false => Mod::COMPLEX };
    let base = ctx.ir.funcs.end();
    let model: BumpRef<Mod> = lower.bump.push(Mod {
        tab: lower.objs[&obj.tab.erase()].cast(),
        guard: obj.guard,
        base,
        n: obj.value.len() as _,
        mt,
        value: []
    }).cast();
    // create vsets
    let mut ret: PhiId = 0.into();
    for &setter in &obj.value {
        let vset = &ctx.objs[setter];
        let var = lower.objs[&vset.var.erase()].cast();
        let vst = if mt == Mod::SIMPLE {
            VSet::SIMPLE
        } else if isprefixidx(&ctx.objs, obj.tab, ctx.objs[vset.var].tab, &vset.idx) {
            VSet::PREFIX
        } else {
            VSet::COMPLEX
        };
        let ptr = lower.bump.push(VSet { obj: setter, model, var, ret, vst, _pad: 0 });
        let vn = lower.bump[var].n;
        lower.bump[var].n = vn+1;
        lower.bump[
            var.cast::<Var<()>>()
                .add_size(1)
                .cast::<BumpRef<VSet>>()
                .add_size(vn as _)
        ] = ptr;
        // note: for var definitions we don't actually need the last dimension sizes (at least for
        // PREFIX models), but they are included here for simpler codegen when forwarding to the
        // model. the optimizer is going to delete them anyway.
        ret += decomposition_size(&ctx.objs, vset.value.erase()) as isize;
    }
    // create functions for complex models only
    if mt == Mod::COMPLEX {
        let scl = sizeclass(&ctx.objs, obj.tab);
        // value:
        {
            let mut func = Func::new(FuncKind::Bundle(Bundle::new(scl)));
            let mut sig = func.build_signature();
            for vset in &lower.bump[model].value {
                for &ty in decomposition(
                    &ctx.objs,
                    ctx.objs[vset.obj].value.erase(),
                    &mut lower.tmp_ty
                ) {
                    sig = sig.add_return(ty);
                }
            }
            maybeidxarg(sig.finish_returns(), scl).finish_args();
            ctx.ir.funcs.push(func);
        }
        // value.init:
        makeinitfunc(&mut ctx.ir);
        // avail
        {
            let mut func = Func::new(FuncKind::Bundle(Bundle::new(scl)));
            maybeidxarg(func.build_signature().add_return(Type::B1).finish_returns(), scl)
                .finish_args();
            ctx.ir.funcs.push(func);
        }
        // avail.init:
        makeinitfunc(&mut ctx.ir);
        trace!(LOWER "MOD {:?} value: {:?}[{:?}] avail: {:?}[{:?}]",
            idx, base, base+1, base+2, base+3);
    }
}

fn collectobjs(ctx: &mut Ccx<Lower>) {
    // pass 1:
    // * count vsets in var.mark
    // * count expr references in expr.mark
    let mut idx = ObjRef::NIL;
    while let Some(i) = ctx.objs.next(idx) {
        idx = i;
        let obj = ctx.objs[idx];
        if obj.op == Obj::VSET {
            let var = ctx.objs[idx.cast::<VSET>()].var;
            ctx.objs[var].mark += 1;
        }
        for i in obj.ref_params() {
            let p: ObjRef = zerocopy::transmute!(ctx.objs.get_raw(idx)[i+1]);
            let pref = &mut ctx.objs[p];
            if Operator::is_expr_raw(pref.op) {
                pref.mark += (pref.mark < EXPR_MANY) as u8;
            }
        }
    }
    // pass 2: allocate objs and functions (note: depends on objs being in topo order)
    ctx.freeze_graph(|ctx| {
        let objs = Access::borrow(&ctx.objs);
        for (idx, obj) in objs.pairs() {
            let bp = ctx.data.bump.end().cast_up();
            match obj {
                ObjectRef::TAB(tab)   => createtab(ctx, idx.cast(), tab),
                ObjectRef::VAR(var)   => createvar(ctx, idx.cast(), var),
                ObjectRef::MOD(model) => createmod(ctx, idx.cast(), model),
                ObjectRef::FUNC(_)    => todo!(),
                ObjectRef::QUERY(_)   => {
                    // NOP: don't need query data, but include it in the hashmap so that all
                    // emitted objects can be found by iterating the hashmap.
                },
                _ => continue
            }
            ctx.data.objs.insert(idx, bp);
        }
    });
    debug_assert!(ctx.data.objs[&ObjRef::GLOBAL.erase()] == Tab::GLOBAL.cast());
}

/* ---- Emit helpers -------------------------------------------------------- */

fn emitarg(func: &Func, idx: usize) -> InsId {
    let phi = func.ret + idx as isize;
    func.code.push(Ins::PHI(func.phis.at(phi).type_, InsId::START, phi))
}

fn reserve(func: &Func, num: usize) -> InsId {
    // FIXME repeat_n stabilizes in 1.82.0
    func.code.extend((0..num).map(|_| Ins::NOP_FX))
}

fn emitjumpifnot(func: &Func, ctr: &mut InsId, cond: InsId, target: InsId) -> InsId {
    let next = reserve(func, 1);
    func.code.set(*ctr, Ins::IF(cond, next, target));
    *ctr = next;
    next
}

fn emitcallvm(func: &Func, idx: InsId, node: FuncId, inline: bool) -> InsId {
    let zero = func.code.push(Ins::KINT(IRT_IDX, 0));
    let knop = func.code.push(Ins::KNOP());
    let callinit = func.code.push(Ins::CALLB(zero, knop, node+1));
    let init = func.code.push(Ins::RES(Type::FX, callinit, 0.into()));
    let opcode = match inline {
        true  => Opcode::CALLBI,
        false => Opcode::CALLB
    };
    func.code.push(
        Ins::new(opcode, Type::FX)
        .set_a(zerocopy::transmute!(idx))
        .set_b(zerocopy::transmute!(init))
        .set_c(zerocopy::transmute!(node))
    )
}

fn emitcallvm1(func: &Func, idx: InsId, node: FuncId) -> InsId {
    emitcallvm(func, idx, node, idx == INS_FLATIDX)
}

// TODO: think of something smarter for indexing in general.
// doing it this way prevents type narrowing.
fn emitarrayptr(func: &Func, base: InsId, mut idx: InsId, ty: Type) -> InsId {
    let size = ty.size();
    if size > 1 {
        let size = func.code.push(Ins::KINT(IRT_IDX, size as _));
        idx = func.code.push(Ins::MUL(IRT_IDX, idx, size));
    }
    func.code.push(Ins::ADDP(base, idx))
}

fn vardata(objs: &HashMap<ObjRef, BumpRef<()>>, var: ObjRef<VAR>) -> BumpRef<Var> {
    objs[&var.erase()].cast()
}

/* ---- Loops --------------------------------------------------------------- */

struct LoopState {
    head: InsId,     // uninitialized slot for initialization (dominates body and tail)
    tail: InsId,     // uninitialized slot for next/exit
    body: InsId,     // uninitialized slot for the loop body (dominates tail)
    out: InsId,      // initialized jump target for breaking the loop
}

impl LoopState {

    fn ctr(&mut self, loopvariant: bool) -> &mut InsId {
        match loopvariant {
            true  => &mut self.tail,
            false => &mut self.head
        }
    }

}

fn emitrangeloop(func: &Func, loop_: &mut LoopState, ty: Type, start: InsId, end: InsId) -> InsId {
    let head = reserve(func, 2);
    let tail = head+1;
    let iphi = func.phis.push(Phi::new(ty));
    let init = func.code.push(Ins::JMP(start, head, iphi));
    let check = func.code.push(Ins::LT(start, end));
    func.code.set(loop_.head, Ins::IF(check, init, loop_.out));
    loop_.head = head;
    let i = func.code.push(Ins::PHI(ty, loop_.body, iphi));
    let one = func.code.push(Ins::KINT(ty, 1));
    let inext = func.code.push(Ins::ADD(ty, i, one));
    let check = func.code.push(Ins::LT(inext, end));
    let jumptail = func.code.push(Ins::JMP(inext, tail, iphi));
    func.code.set(loop_.tail, Ins::IF(check, jumptail, loop_.out));
    loop_.tail = tail;
    i
}

//                       +-------------------------------------------------------+
//                       |                   +---------------------------------+ |
//                       |                   |                                 | v
// +-------+  r=init  +------+  l=init   +------+  r=next  +------+          +-v---+
// | (ctr) | -------> | HEAD | --------> | BODY | -------> | TAIL | -------> | OUT |
// +-------+          +------+           +--^---+          +------+          +-----+
//                                          |       l=next    |              r=result
//                                          +-----------------+
struct Reduce {
    loop_: LoopState,
    l_phi: PhiId, // result phis outside loop (final accumulator)
    r_phi: PhiId, // accumulator phis inside loop body
    init: InsId,  // initial accumulator values (inside loop head)
    value: InsId, // accumulator values (inside loop body)
    body: InsId,  // loop body start
    tail: InsId,  // loop tail start
    num: u16,     // number of accumulators
}

fn newreduce(
    func: &Func,
    ctr: InsId,
    l_phi: PhiId,
    r_phi: PhiId,
    init: InsId,
    num: u16
) -> Reduce {
    let out = reserve(func, 4);
    let head = out+1;
    let body = out+2;
    let tail = out+3;
    let value = func.code.extend(
        (0..num as isize)
        .map(|i| Ins::PHI(func.phis.at(l_phi+i).type_, body, l_phi+i))
    );
    let mut jmp = Ins::JMP(init, head, r_phi);
    for i in 1..num as isize {
        let idx = func.code.push(jmp);
        jmp = Ins::JMP(init + i, idx, r_phi + i);
    }
    func.code.set(ctr, jmp);
    Reduce {
        loop_: LoopState { head, tail, body, out },
        l_phi, r_phi, init, value, body, tail, num
    }
}

fn closereduce(func: &Func, reduce: Reduce, next: InsId) -> InsId {
    let Reduce { l_phi, r_phi, init, loop_, body, tail, num, ..} = reduce;
    let mut jhead = Ins::JMP(init, body, l_phi);
    let mut jbody = Ins::JMP(next, tail, r_phi);
    let mut jtail = Ins::JMP(next, body, l_phi);
    for i in 1..num as isize {
        let base = func.code.extend([jhead, jbody, jtail].into_iter());
        jhead = Ins::JMP(init + i, base, l_phi + i);
        jbody = Ins::JMP(next + i, base+1, r_phi + i);
        jtail = Ins::JMP(next + i, base+2, l_phi + i);
    }
    func.code.set(loop_.head, jhead);
    func.code.set(loop_.body, jbody);
    func.code.set(loop_.tail, jtail);
    func.code.extend(
        (0..num as isize)
        .map(|i| Ins::PHI(func.phis.at(r_phi+i).type_, loop_.out, r_phi+i))
    )
}

/* ---- Indexing ------------------------------------------------------------ */

// NOTE: in the following functions, axes are numbered from 1.
// the zeroth axis is the "axis" for the index in a table with zero dimensions (whose only valid
// flat index is zero).

// given a flat index
//   tab[i1, ..., iN]
// emit the flat index
//   tab[i1, ..., iN, 0]
fn idxftran(
    lcx: &mut Lcx,
    tab: BumpRef<Tab>, // *target* table being indexed
    call: InsId,       // CALLB(I) of tab
    axis: usize,       // current axis (N)
    flat: InsId        // flat index for current axis (N)
) -> InsId {
    // note: if axis=0, then flat is either zero (the only valid index), or one (one past the last
    // valid index)
    let Axis { rank, ret, .. } = lcx.data.bump[tab].axes[axis];
    match rank {
        Axis::SCALAR => {
            let size = lcx.data.func.code.push(Ins::RES(IRT_IDX, call, ret));
            lcx.data.func.code.push(Ins::MUL(IRT_IDX, flat, size))
        },
        _ /* VECTOR */ => {
            // TODO: load from fwd transform table
            todo!()
        }
    }
}

// given a flat index
//   tab[i1, ..., iN, i{N+1}]
// emit the flat index
//   tab[i1, ..., iN]
// (the index i{N+1} can be obtained by doing a forward transform and taking the difference)
fn idxbtran(
    lcx: &mut Lcx,
    tab: BumpRef<Tab>, // *target* table being indexed
    call: InsId,       // CALLB(I) of tab
    axis: usize,       // current axis (N+1)
    flat: InsId        // flat index for current axis (N+1)
) -> InsId {
    debug_assert!(axis > 0);
    if axis == 1 {
        // the only valid flat index for the zeroth axis is zero,
        // therefore back transforming anything to the zeroth axis yields zero.
        return lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    }
    let Axis { rank, ret, .. } = lcx.data.bump[tab].axes[axis-1];
    match rank {
        Axis::SCALAR => {
            let size = lcx.data.func.code.push(Ins::RES(IRT_IDX, call, ret));
            lcx.data.func.code.push(Ins::DIV(IRT_IDX, flat, size))
        },
        _ /* VECTOR */ => {
            // TODO: load from back transform table
            todo!()
        }
    }
}

// given tables
//   A[i1, ..., iN]
//   B[j1, ..., jM]
// returns the largest K such that
//   ik = jk for all 0 <= k < K
fn commonprefix(objs: &Objects, bump: &BumpPtr, a: BumpRef<Tab>, b: BumpRef<Tab>) -> usize {
    if a == b { return bump[a].axes.len() }
    zip(bump[a].axes.iter(), bump[b].axes.iter())
        .take_while(|(a, b)| objs.equal(a.size.erase(), b.size.erase()))
        .count()
}

// do A and B have the exact same shape?
fn sametab(objs: &Objects, bump: &BumpPtr, a: BumpRef<Tab>, b: BumpRef<Tab>) -> bool {
    commonprefix(objs, bump, a, b) == max(bump[a].n, bump[b].n) as usize
}

fn emittabcall(func: &Func, tabf: FuncId) -> InsId {
    let zero = func.code.push(Ins::KINT(IRT_IDX, 0));
    let init = func.code.push(Ins::KNOP());
    func.code.push(Ins::CALLB(zero, init, tabf))
}

// given a flat index
//   source[i1, ..., i{source_axis}]
// emit the flat index
//   target[i1, ..., i{target_axis}]
// (source and target may be equal. if target_axis > source_axis, additional indices are zeros)
fn idxtransfer(
    lcx: &mut Lcx,
    source: BumpRef<Tab>,
    target: BumpRef<Tab>,
    mut source_axis: usize,
    target_axis: usize,
    mut flat: InsId
) -> InsId {
    if target_axis == 0 {
        return lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    }
    let prefix = commonprefix(&lcx.objs, &lcx.data.bump, source, target);
    let sourcecall = match source_axis > min(target_axis, prefix) {
        true  => emittabcall(&lcx.data.func, lcx.data.bump[source].func),
        false => InsId::INVALID.into()
    };
    let targetcall = match target_axis > min(source_axis, prefix) {
        true  => emittabcall(&lcx.data.func, lcx.data.bump[target].func),
        false => InsId::INVALID.into()
    };
    while source_axis > target_axis {
        flat = idxbtran(lcx, source, sourcecall, source_axis, flat);
        source_axis -= 1;
    }
    if source_axis > prefix {
        // here we have target_axis >= source_axis > prefix, due to the previous loop.
        // this necessarily implies source != target.
        // we must now transfer source_axis in `source` to source_axis in `target`.
        // base+i will hold the prefix+1+i'th NON-flat index.
        let source_axis0 = source_axis;
        let mut base = reserve(&lcx.data.func, source_axis-prefix);
        while source_axis > prefix {
            flat = idxbtran(lcx, source, sourcecall, source_axis, flat);
            source_axis -= 1;
            let start = idxftran(lcx, source, sourcecall, source_axis, flat);
            lcx.data.func.code.set(
                base + (source_axis-prefix) as isize,
                Ins::SUB(IRT_IDX, flat, start)
            );
        }
        while source_axis < source_axis0 {
            flat = idxftran(lcx, target, targetcall, source_axis, flat);
            flat = lcx.data.func.code.push(Ins::ADD(IRT_IDX, flat, base));
            base += 1;
            source_axis += 1;
        }
    }
    while source_axis < target_axis {
        flat = idxftran(lcx, target, targetcall, source_axis, flat);
        source_axis += 1;
    }
    flat
}

enum ControlFlow<'a> {
    Straight(&'a mut InsId),
    Loop(&'a mut LoopState)
}

// given a (possibly empty) flat prefix
//   tab[p1, ..., pN]
// and a (possibly empty) index expression
//   [i1, ..., iM]
// emit the flat index
//   tab[p1, ..., pN, i1, ..., iM, :, ..., :]
// where the index is filled with `:`s to fill the unspecified axes.
// if the expression selects more than one flat index, ctr must be a ControlFlow::Loop
fn idxsuffix(
    lcx: &mut Lcx,
    mut ctr: ControlFlow,
    tab: BumpRef<Tab>,
    idx: &[ObjRef<EXPR>],
    mut axis: usize,
    mut flat: InsId
) -> InsId {
    let dim = lcx.data.bump[tab].n as usize;
    debug_assert!(dim >= axis + idx.len());
    if axis == dim {
        // nothing to do here (skip emitting the tabcall).
        return flat;
    }
    let call = emittabcall(&lcx.data.func, lcx.data.bump[tab].func);
    let splat = dim - axis - idx.len();
    let mut inloop = false;
    for &i in idx {
        let j = match isscalarann(&lcx.objs, i.erase()) {
            true  => {
                let c = match &mut ctr {
                    ControlFlow::Straight(ctr) => ctr,
                    ControlFlow::Loop(loop_) => loop_.ctr(inloop)
                };
                emitvalue(lcx, c, i)
            },
            false if inloop || splat > 0 => {
                // TODO: need to emit a nested loop, which is difficult because we don't control
                // the iteration, because we are zipping with other iterators (eg. sum(a*b)).
                // the plan is:
                //   * materialize all explicit indices
                //   * special case emit a 2-deep nested loop with over explicit indices,
                //     then the trailing splat integer range.
                todo!()
            }
            false => {
                inloop = true;
                let ControlFlow::Loop(loop_) = &mut ctr else { unreachable!() };
                emititer(lcx, loop_, i)
            }
        };
        flat = idxftran(lcx, tab, call, axis, flat);
        flat = lcx.data.func.code.push(Ins::ADD(IRT_IDX, flat, j));
        axis += 1;
    }
    if splat > 0 {
        let one = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
        let mut start = flat;
        let mut end = lcx.data.func.code.push(Ins::ADD(IRT_IDX, start, one));
        while axis < dim {
            start = idxftran(lcx, tab, call, axis, start);
            end = idxftran(lcx, tab, call, axis, end);
            axis += 1;
        }
        let ControlFlow::Loop(loop_) = ctr else { unreachable!() };
        emitrangeloop(&lcx.data.func, loop_, IRT_IDX, start, end)
    } else {
        flat
    }
}

// given a target table and an index expression
//   tab[i1, ..., iM],
// emit the (full) flat index
//   tab[p1, ..., pN, i1, ..., iM, :, ..., :],
// where
//   N = min(dim(lcx.data.tab, dim(tab)-M))
// and p1, ..., pN is a flat (prefix) index for the current table.
fn emitidx(lcx: &mut Lcx, ctr: ControlFlow, tab: BumpRef<Tab>, idx: &[ObjRef<EXPR>]) -> InsId {
    let sdim = lcx.data.bump[lcx.data.tab].n as usize;
    let tdim = lcx.data.bump[tab].n as usize;
    if idx.len() == tdim || sdim == 0 {
        idxsuffix(lcx, ctr, tab, idx, 0, lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0)))
    } else {
        let n = min(sdim, tdim-idx.len());
        let prefix = idxtransfer(lcx, lcx.data.tab, tab, sdim, n, INS_FLATIDX);
        idxsuffix(lcx, ctr, tab, idx, n, prefix)
    }
}

// given a target table and an index expression
//   tab[i1, ..., iN]
// emit the shape of the resulting tensor
fn emitidxshape(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    target: BumpRef<Tab>,
    idx: &[ObjRef<EXPR>],
    ann: ObjRef
) -> InsId {
    let dim = typedim(&lcx.objs, ann) as usize;
    let base = reserve(&lcx.data.func, dim);
    let mut axis = 0;
    for &i in idx {
        if !isscalarann(&lcx.objs, i.erase()) {
            // TODO: this only works for int arrays, not explicit splats, ranges, or bool arrays
            let ilen = emitlen(lcx, ctr, i);
            lcx.data.func.code.set(base + axis as isize, Ins::MOV(IRT_IDX, ilen));
            axis += 1;
        }
    }
    if axis < dim {
        let call = emittabcall(&lcx.data.func, lcx.data.bump[target].func);
        for &Axis { rank, ret, .. }
            in &lcx.data.bump[target].axes[lcx.data.bump[lcx.data.tab].n as usize + idx.len()..]
        {
            // vector axis here is a compiler error and should probably be detected earlier
            // (it doesn't make sense to collect dynamically shaped axes into a tensor because
            //  tensors are rectangular)
            debug_assert!(rank == Axis::SCALAR);
            lcx.data.func.code.set(base + axis as isize, Ins::RES(IRT_IDX, call, ret));
            axis += 1;
        }
    }
    debug_assert!(axis == dim);
    base
}

fn emitshapelen(func: &Func, base: InsId, dim: usize) -> InsId {
    if dim == 0 {
        return func.code.push(Ins::KINT(IRT_IDX, 1));
    }
    let mut len = base;
    for i in 1..dim {
        len = func.code.push(Ins::MUL(IRT_IDX, len, base + i as isize));
    }
    len
}

// given a target table and an index expression
//   tab[i1, ..., iN]
// compute the requested attributes, given the source has dimension `source_axis`
fn idxanalyze(
    lcx: &mut Lcx,
    target: BumpRef<Tab>,
    source_axis: usize,
    idx: &[ObjRef<EXPR>],
    mut attrs: EnumSet<IdxAttr>
) -> EnumSet<IdxAttr> {
    if attrs.contains(IdxAttr::Disjoint) {
        // TODO: analyze explicit indices
        if !idx.is_empty() || source_axis > lcx.data.bump[target].n as usize {
            attrs.remove(IdxAttr::Disjoint);
        }
    }
    attrs
}

/* ---- Expressions --------------------------------------------------------- */

// the 4 ways to emit an expression are:
//   * emitvalue()    emit the value (materializes vectors)
//   * emitshape()    same as emitvalue(), but only emit the axis sizes
//   * emititer()     emit an iterator into a given loop
//   * emitcheck()    emit a test for whether the value is computable or not

// AND:
//      IF left ->ri ->fal
// ri:  JMP right merge
// fal: JMP (KINT 0) merge
//
// OR:
//      IF left ->tru ->ri
// ri:  JMP right merge
// tru: JMP (KINT 1) merge
fn emitlogic(func: &Func, ctr: &mut InsId, left: InsId, right: InsId, op: Intrinsic) -> InsId {
    debug_assert!((Intrinsic::AND | Intrinsic::OR).contains(op));
    let merge = reserve(func, 1);
    let phi = func.phis.push(Phi::new(Type::B1));
    let mut ri = func.code.push(Ins::JMP(right, merge, phi));
    let kbool = func.code.push(Ins::KINT(Type::B1, (op == Intrinsic::OR) as _));
    let mut other = func.code.push(Ins::JMP(kbool, merge, phi));
    if op == Intrinsic::OR { (ri, other) = (other, ri); }
    func.code.set(*ctr, Ins::IF(left, ri, other));
    *ctr = merge;
    func.code.push(Ins::PHI(Type::B1, merge, phi))
}

fn emitcmp(func: &Func, left: InsId, right: InsId, op: Intrinsic, ty: Primitive) -> InsId {
    let opcode = match (op, ty.is_unsigned()) {
        (Intrinsic::LT, true)  => Opcode::ULT,
        (Intrinsic::LT, false) => Opcode::LT,
        (Intrinsic::LE, true)  => Opcode::ULE,
        (Intrinsic::LE, false) => Opcode::LE,
        _ => unreachable!()
    };
    func.code.push(
        Ins::new(opcode, Type::B1)
            .set_a(zerocopy::transmute!(left))
            .set_b(zerocopy::transmute!(right))
    )
}

// args passed in lcx.data.tmp_ins[base..]
fn emitscalarintrinsic(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    f: Intrinsic,
    args: &[ObjRef<EXPR>],
    ty: Type,
    base: usize
) -> InsId {
    use Intrinsic::*;
    let argv = &lcx.data.tmp_ins[base..];
    match f {
        OR|AND => emitlogic(&lcx.data.func, ctr, argv[0], argv[1], f),
        ADD   => lcx.data.func.code.push(Ins::ADD(ty, argv[0], argv[1])),
        SUB   => lcx.data.func.code.push(Ins::SUB(ty, argv[0], argv[1])),
        MUL   => lcx.data.func.code.push(Ins::MUL(ty, argv[0], argv[1])),
        DIV   => todo!(), // handle signedness
        POW   => lcx.data.func.code.push(Ins::POW(ty, argv[0], argv[1])),
        EQ    => lcx.data.func.code.push(Ins::EQ(argv[0], argv[1])),
        NE    => lcx.data.func.code.push(Ins::NE(argv[0], argv[1])),
        LT|LE => emitcmp(&lcx.data.func, argv[0], argv[1], f,
            Primitive::from_u8(lcx.objs[lcx.objs[args[0]].ann.cast::<TPRI>()].ty)),
        UNM   => todo!(), // name it consistently UNM? NEG?
        EXP   => todo!(), // ir intrinsic call?
        LOG   => todo!(), // ir intrinsic call?
        NOT   => todo!(),
        CONV  => todo!(),
        _     => unreachable!() // non-scalar
    }
}

fn emitsum(lcx: &mut Lcx, ctr: &mut InsId, arg: ObjRef<EXPR>, ty: Type) -> InsId {
    if isscalarann(&lcx.objs, arg.erase()) {
        return emitvalue(lcx, ctr, arg);
    }
    let zero = lcx.data.func.code.push(Ins::KINT(ty, 0));
    let l_phi = lcx.data.func.phis.push(Phi::new(ty));
    let r_phi = lcx.data.func.phis.push(Phi::new(ty));
    let mut reduce = newreduce(&lcx.data.func, *ctr, l_phi, r_phi, zero, 1);
    let elem = emititer(lcx, &mut reduce.loop_, arg);
    let next = lcx.data.func.code.push(Ins::ADD(ty, reduce.value, elem));
    *ctr = reduce.loop_.out;
    closereduce(&lcx.data.func, reduce, next)
}

fn scalarintrinsic(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    f: Intrinsic,
    args: &[ObjRef<EXPR>],
    ty: Type
) -> InsId {
    match f {
        Intrinsic::SUM => emitsum(lcx, ctr, args[0], ty),
        _ => {
            let base = lcx.data.tmp_ins.len();
            for &arg in args {
                let v = emitvalue(lcx, ctr, arg);
                lcx.data.tmp_ins.push(v);
            }
            let v = emitscalarintrinsic(lcx, ctr, f, args, ty, base);
            lcx.data.tmp_ins.truncate(base);
            v
        }
    }
}

fn broadcastintrinsic(
    lcx: &mut Lcx,
    loop_: &mut LoopState,
    f: Intrinsic,
    args: &[ObjRef<EXPR>],
    ety: ObjRef
) -> InsId {
    let base = lcx.data.tmp_ins.len();
    for &arg in args {
        let v = emititer(lcx, loop_, arg);
        lcx.data.tmp_ins.push(v);
    }
    let v = match lcx.objs.get(ety) {
        ObjectRef::TPRI(&TPRI { ty, .. }) => {
            emitscalarintrinsic(lcx, &mut loop_.body, f, args, Primitive::from_u8(ty).to_ir(), base)
        },
        t => {
            debug_assert!(matches!(t, ObjectRef::TTEN(_)));
            // TODO: this *can* be implemented by materializing it here.
            // whether that's even useful is another question.
            // but it makes sense from the type system perspective
            // (+ :: (T,T) -> T regardless of whether T is scalar or tensor[U,N] or
            // tensor[tensor[U,N],M] or ... you get the idea)
            todo!()
        }
    };
    lcx.data.tmp_ins.truncate(base);
    v
}

fn emitcallx(lcx: &mut Lcx, ctr: &mut InsId, callx: ObjRef<CALLX>) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    let base = lcx.data.tmp_ins.len();
    for &input in &objs[callx].inputs {
        let value = emitvalue(lcx, ctr, input);
        lcx.data.tmp_ins.push(value);
    }
    let lang = Lang::from_u8(objs[callx].lang);
    let value = {
        // safety: this casts (ignoring newtype wrappers):
        //   &mut Ccx<Lower> -> &mut Ccx<UnsafeCell<Lower>>
        let lcx: &mut CLcx = unsafe { core::mem::transmute(&mut *lcx) };
        let lower = Access::borrow(&lcx.data);
        lang.lower_callx(lcx, callx, &lower.func, &lower.tmp_ins[base..])
    };
    lcx.data.tmp_ins.truncate(base);
    value
}

fn emitget(lcx: &mut Lcx, ctr: &mut InsId, get: &GET) -> InsId {
    debug_assert!(lcx.objs[lcx.objs[get.value].ann].op == Obj::TTUP);
    let offset: usize = lcx.objs[lcx.objs[get.value].ann.cast::<TTUP>()].elems[..get.idx as usize]
        .iter()
        .map(|&e| decomposition_size(&lcx.objs, e))
        .sum();
    emitvalue(lcx, ctr, get.value) + offset as isize
}

fn emitvget1(lcx: &mut Lcx, ctr: &mut InsId, vget: &VGET) -> InsId {
    debug_assert!(vget.ann == lcx.objs[vget.var].ann);
    let var = vardata(&lcx.data.objs, vget.var);
    let i = emitidx(lcx, ControlFlow::Straight(ctr), lcx.data.bump[var].tab, &vget.idx);
    let inline = !idxanalyze(
        lcx,
        lcx.data.bump[var].tab,
        lcx.data.bump[lcx.data.tab].n as _,
        &vget.idx,
        IdxAttr::Disjoint.into()
    ).is_empty();
    emitvarload(lcx, var, i, inline)
}

fn computeshape(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    match objs.get(expr.erase()) {
        ObjectRef::VGET(&VGET { var, ann, ref idx, .. }) => {
            let v = vardata(&lcx.data.objs, var);
            let tab = lcx.data.bump[v].tab;
            if ann == lcx.objs[var].ann {
                // scalar load of a vector variable
                let i = emitidx(lcx, ControlFlow::Straight(ctr), tab, idx);
                emitvarloadshape(lcx, v, i, i == INS_FLATIDX)
            } else {
                // vector load of a scalar variable
                emitidxshape(lcx, ctr, tab, idx, ann)
            }
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(&LOAD { ref dims, .. }) => emitvalues(lcx, ctr, dims),
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { func, ref args, .. }) => {
            debug_assert!(Intrinsic::from_u8(func).is_broadcast());
            // TODO: in the case of multiple args, what SHOULD be done here is to compute the
            // shape for all args, and trap if they don't match.
            computeshape(lcx, ctr, args[0])
        },
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn materializecollect(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    expr: ObjRef<EXPR>,
    cty: &TTEN
) -> InsId {
    let shape = computeshape(lcx, ctr, expr);
    let lower = &mut *lcx.data;
    let len = emitshapelen(&lower.func, shape, cty.dim as _);
    let ds = decomposition_size(&lcx.objs, cty.elem);
    // TODO: this needs some thinking because "hardcoding" the element size will make type
    // narrowing impossible in the future.
    let ptrs = reserve(&lower.func, ds);
    let esizes = reserve(&lower.func, ds);
    for (i, ty) in decomposition(&lcx.objs, cty.elem, &mut lower.tmp_ty).iter().enumerate() {
        lower.func.code.set(esizes + i as isize, Ins::KINT(IRT_IDX, ty.size() as _));
        let size = lower.func.code.push(Ins::MUL(IRT_IDX, len, esizes + i as isize));
        lower.func.code.set(ptrs + i as isize, Ins::ALLOC(size, esizes + i as isize));
    }
    // FIXME repeat_n stabilizes in 1.82.0
    let l_phis = lower.func.phis.extend((0..ds).map(|_| Phi::new(Type::FX)));
    let r_phis = lower.func.phis.extend((0..ds).map(|_| Phi::new(Type::FX)));
    let inits = lower.func.code.extend((0..ds).map(|_| Ins::KNOP()));
    let p_phis = lower.func.phis.extend((0..ds).map(|_| Phi::new(Type::PTR)));
    let mut reduce = newreduce(&lower.func, *ctr, l_phis, r_phis, inits, ds as _);
    for i in 0..ds as isize {
        let head = reserve(&lower.func, 1);
        lower.func.code.set(reduce.loop_.head, Ins::JMP(ptrs + i, head, p_phis + i));
        reduce.loop_.head = head;
    }
    let body = reduce.loop_.body;
    let v = emititer(lcx, &mut reduce.loop_, expr);
    let effects = reserve(&lcx.data.func, ds);
    for i in 0..ds as isize {
        let ptr = lcx.data.func.code.push(Ins::PHI(Type::PTR, body, p_phis + i));
        let store = lcx.data.func.code.push(Ins::STORE(ptr, v + i));
        lcx.data.func.code.set(effects+i, Ins::MOVF(Type::FX, reduce.value+i, store));
        let next_ptr = lcx.data.func.code.push(Ins::ADDP(ptr, esizes + i));
        let tail = reserve(&lcx.data.func, 1);
        lcx.data.func.code.set(reduce.loop_.tail, Ins::JMP(next_ptr, tail, p_phis+i));
        reduce.loop_.tail = tail;
    }
    *ctr = reduce.loop_.out;
    let stores = closereduce(&lcx.data.func, reduce, effects);
    let ret = lcx.data.func.code.extend(
        (0..ds as isize)
        .map(|i| Ins::MOVF(Type::PTR, ptrs+i, stores+i))
    );
    lcx.data.func.code.extend((0..cty.dim as isize).map(|i| Ins::MOV(IRT_IDX, shape+i)));
    ret
}

// if ALL of the following are true...
//   (1) the VGET variable has exactly one model,
//   (2) VGET and VSET tables match,
//   (3) VGET and VSET indices match,
// then emit a direct load from the model
fn emitfwdvget(lcx: &mut Lcx, vget: &VGET) -> IndexOption<InsId> {
    let lower = &mut *lcx.data;
    let bump = Access::borrow(&lower.bump);
    let var = &bump[vardata(&lower.objs, vget.var)];
    let [vset] = var.value else { return None.into() };
    let vset = &bump[vset];
    let model = &bump[vset.model];
    // TODO: this check can be relaxed, just need to translate index.
    if !sametab(&lcx.objs, &lower.bump, lower.tab, model.tab) { return None.into() }
    if !lcx.objs.allequal(cast_args(&vget.idx), cast_args(&lcx.objs[vset.obj].idx)) {
        return None.into();
    }
    let call = emitcallvm1(&lower.func, INS_FLATIDX, model.base + Mod::SUB_VALUE);
    let base = lower.func.code.end();
    // scalar load of vector variable is handled separately:
    debug_assert!(vget.ann != lcx.objs[vget.var].ann);
    for (i, &ty) in decomposition(&lcx.objs, lcx.objs[vset.obj].value.erase(), &mut lower.tmp_ty)
        .iter()
        .enumerate()
    {
        lower.func.code.push(Ins::RES(ty, call, vset.ret + i as isize));
    }
    Some(base).into()
}

fn computevalue(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    let ann = objs[expr].ann;
    match objs.get(expr.erase()) {
        ObjectRef::GET(o) => emitget(lcx, ctr, o),
        ObjectRef::CALLX(_) => emitcallx(lcx, ctr, expr.cast()),
        o => match objs.get(ann) {
            ObjectRef::TPRI(&TPRI { ty, .. }) => /* scalar value */ {
                let ty = Primitive::from_u8(ty).to_ir();
                match o {
                    ObjectRef::KINT(&KINT { k, .. }) => lcx.data.func.code.push(
                        Ins::KINT(ty, k as _)),
                    ObjectRef::KINT64(&KINT64 { k, .. }) => lcx.data.func.code.push(
                        Ins::KINT64(ty, zerocopy::transmute!(k))),
                    ObjectRef::KFP64(&KFP64 { k, .. }) => lcx.data.func.code.push(
                        Ins::KFP64(ty, zerocopy::transmute!(k))),
                    ObjectRef::KSTR(&KSTR { k, .. }) => lcx.data.func.code.push(
                        Ins::KSTR(ty, zerocopy::transmute!(k))),
                    ObjectRef::DIM(&DIM { axis, .. }) => {
                        debug_assert!(ty == IRT_IDX);
                        idxtransfer(lcx, lcx.data.tab, lcx.data.tab,
                            lcx.data.bump[lcx.data.tab].n as _, (axis+1) as _, INS_FLATIDX)
                    },
                    ObjectRef::VGET(o) => emitvget1(lcx, ctr, o),
                    ObjectRef::IDX(_) => todo!(),
                    ObjectRef::LOAD(&LOAD { ann, addr, ref dims, .. }) => {
                        debug_assert!(dims.is_empty());
                        debug_assert!(lcx.objs[ann].op == Obj::TPRI);
                        let addr = emitvalue(lcx, ctr, addr);
                        lcx.data.func.code.push(Ins::LOAD(ty, addr))
                    },
                    ObjectRef::FREF(_) => todo!(),
                    ObjectRef::CALL(_) => todo!(),
                    ObjectRef::CALLN(&CALLN { func, ref args, .. }) =>
                        scalarintrinsic(lcx, ctr, Intrinsic::from_u8(func), args, ty),
                    _ => unreachable!()
                }
            },
            ObjectRef::TTEN(cty) => /* vector value */ {
                if let ObjectRef::LOAD(_) = o {
                    // note: this depends on the fact that load.addr and load.dims are consecutive
                    // in memory.
                    return emitvalues(lcx, ctr, cast_args_raw(
                        &objs.get_raw(expr.erase())[obj_index_of!(LOAD,addr)..]));
                }
                if let ObjectRef::VGET(vget) = o {
                    // special case: scalar load of a vector variable is already materialized.
                    if vget.ann == lcx.objs[vget.var].ann {
                        return emitvget1(lcx, ctr, vget);
                    }
                    // special case: ref idx matches complex return
                    if let Some(ins) = emitfwdvget(lcx, vget).unpack() {
                        return ins;
                    }
                    // TODO: special case vector load over a contiguous range, and return a direct
                    //       reference to the buffer
                    // else: fallthrough to general case
                }
                // else: collect iterator into array.
                materializecollect(lcx, ctr, expr, cty)
            },
            _ => unreachable!()
        }
    }
}

fn itervalue(lcx: &mut Lcx, loop_: &mut LoopState, expr: ObjRef<EXPR>) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    match objs.get(expr.erase()) {
        ObjectRef::VGET(&VGET { var, ref idx, .. }) => {
            let var = vardata(&lcx.data.objs, var);
            let i = emitidx(lcx, ControlFlow::Loop(loop_), lcx.data.bump[var].tab, idx);
            let inline = !idxanalyze(
                lcx,
                lcx.data.bump[var].tab,
                lcx.data.bump[lcx.data.tab].n as _,
                idx,
                IdxAttr::Disjoint.into()
            ).is_empty();
            emitvarload(lcx, var, i, inline)
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(&LOAD { ann, addr, ref dims, .. }) => {
            debug_assert!(lcx.objs[ann].op == Obj::TTEN);
            debug_assert!(lcx.objs[lcx.objs[ann.cast::<TTEN>()].elem].op == Obj::TPRI);
            let addr = emitvalue(lcx, &mut loop_.head, addr);
            let shape = emitvalues(lcx, &mut loop_.head, dims);
            let len = emitshapelen(&lcx.data.func, shape, dims.len());
            let zero = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
            let i = emitrangeloop(&lcx.data.func, loop_, IRT_IDX, zero, len);
            let ty = Primitive::from_u8(
                lcx.objs[lcx.objs[ann.cast::<TTEN>()].elem.cast::<TPRI>()].ty).to_ir();
            let ptr = emitarrayptr(&lcx.data.func, addr, i, ty);
            lcx.data.func.code.push(Ins::LOAD(ty, ptr))
        },
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { ann, func, ref args, .. })
            => broadcastintrinsic(lcx, loop_, Intrinsic::from_u8(func), args,
                lcx.objs[ann.cast::<TTEN>()].elem),
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn emitvalue(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    match lcx.objs[expr].mark {
        EXPR_ONE => computevalue(lcx, ctr, expr),
        _ => {
            debug_assert!(lcx.objs[expr].mark == EXPR_MANY);
            if let Some(&ins) = lcx.data.expr.get(&expr) {
                return ins;
            }
            let ins = computevalue(lcx, ctr, expr);
            lcx.data.expr.insert_unique_unchecked(expr, ins);
            ins
        }
    }
}

fn emitvalues(lcx: &mut Lcx, ctr: &mut InsId, exprs: &[ObjRef<EXPR>]) -> InsId {
    match exprs {
        &[] => InsId::INVALID.into(),
        &[v] => emitvalue(lcx, ctr, v),
        vs => {
            let base = reserve(&lcx.data.func, vs.len());
            for (i,&v) in vs.iter().enumerate() {
                let vv = emitvalue(lcx, ctr, v);
                lcx.data.func.code.set(base + i as isize,
                    Ins::MOV(lcx.data.func.code.at(vv).type_(), vv));
            }
            base
        }
    }
}

fn emitshape(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    match lcx.objs[expr].mark {
        EXPR_ONE => computeshape(lcx, ctr, expr),
        _        => emitvalue(lcx, ctr, expr)+1
    }
}

fn emitlen(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    let shape = emitshape(lcx, ctr, expr);
    emitshapelen(&lcx.data.func, shape, typedim(&lcx.objs, expr.erase()) as _)
}

fn emititer(lcx: &mut Lcx, loop_: &mut LoopState, expr: ObjRef<EXPR>) -> InsId {
    match lcx.objs[expr].mark {
        EXPR_ONE => itervalue(lcx, loop_, expr),
        _ => {
            // TODO: emitvalue + iterate
            todo!()
        }
    }
}

fn emitcheckvgetloop(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    var: BumpRef<Var>,
    idx: &[ObjRef<EXPR>],
    inline: bool,
    fail: InsId
) {
    let out = reserve(&lcx.data.func, 3);
    let body = out+1;
    let tail = out+2;
    let mut loop_ = LoopState { head: *ctr, tail, body, out };
    let i = emitidx(lcx, ControlFlow::Loop(&mut loop_), lcx.data.bump[var].tab, idx);
    emitvarcheck(lcx, &mut loop_.body, var, i, inline, fail);
    lcx.data.func.code.set(loop_.head, Ins::GOTO(body));
    lcx.data.func.code.set(loop_.tail, Ins::GOTO(body));
    lcx.data.func.code.set(loop_.body, Ins::GOTO(tail));
    *ctr = out;
}

fn emitcheck(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>, fail: InsId) {
    let objs = Access::borrow(&lcx.objs);
    match objs.get(expr.erase()) {
        ObjectRef::KINT(_) | ObjectRef::KINT64(_) | ObjectRef::KFP64(_) | ObjectRef::KSTR(_)
            | ObjectRef::DIM(_) | ObjectRef::FREF(_) => {},
        ObjectRef::VGET(&VGET { var, ann, ref idx, .. }) => {
            emitcheckall(lcx, ctr, idx, fail);
            let v = vardata(&lcx.data.objs, var);
            let tab = lcx.data.bump[v].tab;
            let inline = !idxanalyze(lcx, tab, lcx.data.bump[lcx.data.tab].n as _, idx,
                IdxAttr::Disjoint.into()).is_empty();
            if ann == lcx.objs[var].ann {
                let i = emitidx(lcx, ControlFlow::Straight(ctr), tab, idx);
                emitvarcheck(lcx, ctr, v, i, inline, fail);
            } else {
                emitcheckvgetloop(lcx, ctr, v, idx, inline, fail);
            }
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(&LOAD { addr, ref dims, .. }) => {
            emitcheck(lcx, ctr, addr, fail);
            emitcheckall(lcx, ctr, dims, fail);
        },
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(CALLN { args, .. }) => emitcheckall(lcx, ctr, args, fail),
        ObjectRef::CALLX(CALLX { inputs, ..}) => emitcheckall(lcx, ctr, inputs, fail),
        _ => unreachable!()
    };
}

fn emitcheckall(lcx: &mut Lcx, ctr: &mut InsId, objs: &[ObjRef<EXPR>], fail: InsId) {
    for &idx in objs {
        emitcheck(lcx, ctr, idx, fail);
    }
}

/* ---- Tables -------------------------------------------------------------- */

// table code is based on the following "mental model":
//
//   * start from a table with zero axes. it has one valid index: 0.
//   * if a table has valid (flattened) indices 0..N, then a new dimension is added as follows:
//      (1) STATIC dimension of size M:
//        * forward transformation ([i,j] -> [k]):   k = M*i + j
//        * backward transformation ([k] -> [i,:]):  i = k/M
//        ie. a static axis only needs to store its size.
//      (2) DYNAMIC dimension of sizes [M_0, ..., M_{N-1}]:
//        * forward transformation ([i,j] -> [k]):   k = F[i] + j
//        * backward transformation ([k] -> [i,:])   i = B[k]
//        where F and B are lookup tables:
//        * F[0] = 0; F[i] = F[i-1] + M_{i-1}
//        * B[F[i]..F[i+1]] = i
//
// note 1: it follows from above that the first axis must be static.
// note 2: the *shape* of the tensor defining a dynamic axis doesn't matter, only its number of
//         entries. eg, consider `table tab[2,2,V]` - V can be 1x4, 2x2, 4x1, 1x1x4, whatever,
//         as long as it has 4 entries.
// note 3: a static dimension is semantically equivalent to a dynamic dimension where each entry
//         has the same value.
//
// * return 0 is the flattened size (i64)
// * returns 1.. are allocated in order, starting from the first axis, with 1 slot (i64 size)
//   per static dimension, and 2 slots (ptr F, ptr B) per dynamic dimension.
fn emittab(lcx: &mut Lcx, tab: BumpRef<Tab>) {
    let mut ctr = InsId::START;
    let mut len: IndexOption<InsId> = None.into();
    let bump = Access::borrow(&lcx.data.bump);
    for &Axis { rank, ret, size, .. } in &bump[tab].axes {
        match rank {
            Axis::SCALAR => {
                // asize = check(axis) ? value(axis) : 0
                let asize = lcx.data.func.phis.push(Phi::new(IRT_IDX));
                let merge = reserve(&lcx.data.func, 1);
                let zero = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
                let fail = lcx.data.func.code.push(Ins::JMP(zero, merge, asize));
                emitcheck(lcx, &mut ctr, size, fail);
                let value = emitvalue(lcx, &mut ctr, size);
                let asizev = lcx.data.func.code.push(Ins::PHI(IRT_IDX, merge, asize));
                len = Some(match len.unpack() {
                    Some(len) => lcx.data.func.code.push(Ins::MUL(IRT_IDX, len, asizev)),
                    None      => asizev
                }).into();
                lcx.data.func.code.set(ctr, Ins::JMP(value, merge, asize));
                ctr = reserve(&lcx.data.func, 1);
                lcx.data.func.code.set(merge, Ins::JMP(asizev, ctr, ret));
            },
            _ /* VECTOR */ => {
                // TODO: see above comment
                todo!()
            }
        }
    }
    let len = len.unpack().unwrap_or_else(|| lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0)));
    let ret = lcx.data.func.code.push(Ins::RET());
    lcx.data.func.code.set(ctr, Ins::JMP(len, ret, 0.into()));
}

/* ---- Initializers -------------------------------------------------------- */

fn emitbinit(lcx: &mut Lcx, tab: BumpRef<Tab>, bundle: FuncId) {
    let tabcall = emittabcall(&lcx.data.func, lcx.data.bump[tab].func);
    let size = lcx.data.func.code.push(Ins::RES(IRT_IDX, tabcall, 0.into()));
    let binit = lcx.data.func.code.push(Ins::BINIT(size, bundle));
    let ret = lcx.data.func.code.push(Ins::RET());
    lcx.data.func.code.set(InsId::START, Ins::JMP(binit, ret, 0.into()));
}

/* ---- Variables ----------------------------------------------------------- */

fn emitvararms(lcx: &mut Lcx, var: BumpRef<Var>) {
    let mut ctr = InsId::START;
    let ret = lcx.data.func.code.push(Ins::RET());
    let bump = Access::borrow(&lcx.data.bump);
    for (i, &setter) in bump[var].value.iter().enumerate() {
        let vset = &bump[setter];
        let model = &bump[vset.model];
        let next = reserve(&lcx.data.func, 1);
        match vset.vst {
            VSet::SIMPLE => {
                if !model.guard.is_nil() {
                    emitcheck(lcx, &mut ctr, model.guard, next);
                    let cond = emitvalue(lcx, &mut ctr, model.guard);
                    emitjumpifnot(&lcx.data.func, &mut ctr, cond, next);
                }
                emitcheck(lcx, &mut ctr, lcx.objs[vset.obj].value, next);
            },
            VSet::PREFIX => {
                let var = &bump[vset.var];
                // SourcePrefix on VSET implies:
                debug_assert!(bump[model.tab].n <= bump[var.tab].n);
                let idx = idxtransfer(lcx, var.tab, model.tab, bump[var.tab].n as _,
                    bump[model.tab].n as _, INS_FLATIDX);
                let call = emitcallvm1(&lcx.data.func, idx, model.base + Mod::SUB_AVAIL);
                let check = lcx.data.func.code.push(Ins::RES(Type::B1, call, 0.into()));
                emitjumpifnot(&lcx.data.func, &mut ctr, check, next);
            },
            _ /* COMPLEX */ => {
                todo!()
            }
        }
        let karm = lcx.data.func.code.push(Ins::KINT(IRT_ARM, i as _));
        lcx.data.func.code.set(ctr, Ins::JMP(karm, ret, 0.into()));
        ctr = next;
    }
    let knone = lcx.data.func.code.push(Ins::KINT(IRT_ARM, !0));
    lcx.data.func.code.set(ctr, Ins::JMP(knone, ret, 0.into()));
}

fn emitvarvalue(lcx: &mut Lcx, var: BumpRef<Var>) {
    let mut ctr = InsId::START;
    let bump = Access::borrow(&lcx.data.bump);
    let var = &bump[var];
    lcx.data.tmp_vty.clear();
    pushdeco(&lcx.objs, var.obj.erase(), &mut lcx.data.tmp_vty);
    let ds = decomposition_size(&lcx.objs, var.obj.erase());
    let vardim = bump[var.tab].n as usize;
    let armcall = emitcallvm1(&lcx.data.func, INS_FLATIDX, var.base + Var::SUB_ARM);
    let arm = lcx.data.func.code.push(Ins::RES(IRT_ARM, armcall, 0.into()));
    let out = lcx.data.func.code.push(Ins::RET());
    for (i, &setter) in var.value.iter().enumerate() {
        let karm = lcx.data.func.code.push(Ins::KINT(IRT_ARM, i as _));
        let check = lcx.data.func.code.push(Ins::EQ(arm, karm));
        let tru = reserve(&lcx.data.func, 2);
        let fal = tru+1;
        lcx.data.func.code.set(ctr, Ins::IF(check, tru, fal));
        ctr = tru;
        let vset = &bump[setter];
        let value = match vset.vst {
            VSet::SIMPLE => emitvalue(lcx, &mut ctr, lcx.objs[vset.obj].value),
            VSet::PREFIX => {
                let model = &bump[vset.model];
                let modeldim = bump[model.tab].n as usize;
                let idx = idxtransfer(lcx, var.tab, model.tab, vardim, modeldim, INS_FLATIDX);
                let call = emitcallvm1(&lcx.data.func, idx, model.base + Mod::SUB_VALUE);
                if lcx.objs[lcx.objs[vset.obj].value].ann == lcx.objs[var.obj].ann {
                    // model returns scalar of var type -> we just forward the value
                    debug_assert!(modeldim == vardim);
                    lcx.data.func.code.extend(
                        lcx.data.tmp_vty
                        .iter()
                        .enumerate()
                        .map(|(j, &ty)| Ins::RES(ty, call, vset.ret + j as isize))
                    )
                } else {
                    // model returns rank-k tensor of var type, where k = number of implicit
                    // dimensions, ie. the dim(var.tab) - dim(mod.tab)
                    // -> we "peel off" one layer by loading the flat index on each return slot.
                    debug_assert!(modeldim < vardim);
                    let baseidx = idxtransfer(lcx, model.tab, var.tab, modeldim, vardim, idx);
                    let ofs = lcx.data.func.code.push(Ins::SUB(IRT_IDX, INS_FLATIDX, baseidx));
                    let base = reserve(&lcx.data.func, ds);
                    for (j, &ty) in lcx.data.tmp_vty.iter().enumerate() {
                        let res = lcx.data.func.code.push(
                            Ins::RES(Type::PTR, call, vset.ret + j as isize));
                        let ptr = emitarrayptr(&lcx.data.func, res + j as isize, ofs, ty);
                        lcx.data.func.code.set(base + j as isize, Ins::LOAD(ty, ptr));
                    }
                    base
                }
            },
            _ /* COMPLEX */ => {
                todo!()
            }
        };
        let mut ret = Ins::JMP(value, out, 0.into());
        for j in 1..ds {
            let r = lcx.data.func.code.push(ret);
            ret = Ins::JMP(value + j as isize, r, j.into());
        }
        lcx.data.func.code.set(ctr, ret);
        ctr = fal;
    }
    lcx.data.func.code.set(ctr, Ins::UB());
}

fn emitvarload(lcx: &mut Lcx, var: BumpRef<Var>, idx: InsId, inline: bool) -> InsId {
    let lower = &mut *lcx.data;
    let Var { base, obj, .. } = lower.bump[var];
    let call = emitcallvm(&lower.func, idx, base + Var::SUB_VALUE, inline);
    lower.func.code.extend(
        decomposition(&lcx.objs, obj.erase(), &mut lower.tmp_ty)
        .iter()
        .enumerate()
        .map(|(i,&ty)| Ins::RES(ty, call, i.into()))
    )
}

fn emitvarloadshape(lcx: &mut Lcx, var: BumpRef<Var>, idx: InsId, inline: bool) -> InsId {
    let Var { base, obj, .. } = lcx.data.bump[var];
    debug_assert!(lcx.objs[lcx.objs[obj].ann].op == Obj::TTEN);
    let call = emitcallvm(&lcx.data.func, idx, base + Var::SUB_VALUE, inline);
    let TTEN { dim, elem, ..} = lcx.objs[lcx.objs[obj].ann.cast()];
    let esz = decomposition_size(&lcx.objs, elem);
    lcx.data.func.code.extend((esz..esz+dim as usize).map(|i| Ins::RES(IRT_IDX, call, i.into())))
}

fn emitvarcheck(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    var: BumpRef<Var>,
    idx: InsId,
    inline: bool,
    fail: InsId
) {
    let base = lcx.data.bump[var].base;
    let call = emitcallvm(&lcx.data.func, idx, base + Var::SUB_ARM, inline);
    let arm = lcx.data.func.code.push(Ins::RES(IRT_ARM, call, 0.into()));
    let none = lcx.data.func.code.push(Ins::KINT(IRT_ARM, !0));
    let check = lcx.data.func.code.push(Ins::NE(arm, none));
    emitjumpifnot(&lcx.data.func, ctr, check, fail);
}

/* ---- Models -------------------------------------------------------------- */

// only non-simple models are handled here.
// simple models emit directly into the variable definition.

fn emitmodavail(lcx: &mut Lcx, model: BumpRef<Mod>) {
    let mut ctr = InsId::START;
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    let model = &bump[model];
    let kfal = lcx.data.func.code.push(Ins::KINT(Type::B1, 0));
    let jfal = lcx.data.func.code.push(Ins::JMP(kfal, ctr, 0.into()));
    if !model.guard.is_nil() {
        emitcheck(lcx, &mut ctr, model.guard, jfal);
        let cond = emitvalue(lcx, &mut ctr, model.guard);
        emitjumpifnot(&lcx.data.func, &mut ctr, cond, jfal);
    }
    for setter in &model.value {
        let vset = &objs[setter.obj];
        emitcheck(lcx, &mut ctr, vset.value, jfal);
        emitcheckall(lcx, &mut ctr, &vset.idx, jfal);
    }
    let ret = lcx.data.func.code.push(Ins::RET());
    let ktru = lcx.data.func.code.push(Ins::KINT(Type::B1, 1));
    lcx.data.func.code.set(ctr, Ins::JMP(ktru, ret, 0.into()));
}

fn emitmodvalue(lcx: &mut Lcx, model: BumpRef<Mod>) {
    let mut ctr = InsId::START;
    let bump = Access::borrow(&lcx.data.bump);
    let model = &bump[model];
    for vset in &model.value {
        let value = lcx.objs[vset.obj].value;
        // TODO: optimization: for full table VSET (ie. empty idx) return only the pointer,
        // and on use load the shape from the tab instead
        let v = emitvalue(lcx, &mut ctr, value);
        for i in 0..decomposition_size(&lcx.objs, value.erase()) {
            let next = reserve(&lcx.data.func, 1);
            lcx.data.func.code.set(ctr, Ins::JMP(v + i as isize, next, vset.ret + i as isize));
            ctr = next;
        }
    }
    lcx.data.func.code.set(ctr, Ins::RET());
}

/* ---- Queries ------------------------------------------------------------- */

fn emitquery(lcx: &mut Lcx, query: ObjRef<QUERY>) {
    let mut ctr = InsId::START;
    let mut ret: PhiId = 0.into();
    let objs = Access::borrow(&lcx.objs);
    for &value in &objs[query].value {
        let mut v = emitvalue(lcx, &mut ctr, value);
        for _ in 0..decomposition_size(&lcx.objs, value.erase()) {
            let next = reserve(&lcx.data.func, 1);
            lcx.data.func.code.set(ctr, Ins::JMP(v, next, ret.into()));
            ctr = next;
            v += 1;
            ret += 1;
        }
    }
    lcx.data.func.code.set(ctr, Ins::RET());
}

/* -------------------------------------------------------------------------- */

enum Template {
    TabInit(BumpRef<Tab>),
    BundleInit(BumpRef<Tab>, FuncId),
    VarVal(BumpRef<Var>),
    VarArm(BumpRef<Var>),
    ModVal(BumpRef<Mod>),
    ModAvail(BumpRef<Mod>),
    Query(ObjRef<QUERY>)
}

fn emittemplate(lcx: &mut Ccx<Lower<R, RW>, R>, id: FuncId, template: Template) {
    swap(&mut *lcx.data.func, &mut lcx.ir.funcs[id]);
    debug_assert!(lcx.data.func.code.is_empty());
    lcx.data.expr.clear();
    // start:
    reserve(&lcx.data.func, 1);
    // flatidx:
    match &lcx.data.func.kind {
        FuncKind::Bundle(bundle) => match bundle.scl {
            SizeClass::GLOBAL => { lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0)); },
            _ => { emitarg(&lcx.data.func, 0); }
        },
        FuncKind::Query(_) => { emitarg(&lcx.data.func, 0); },
        FuncKind::User() => todo!() // no flatidx (?)
    }
    {
        use Template::*;
        let lcx: &mut Lcx = unsafe { core::mem::transmute(&mut *lcx) };
        match template {
            TabInit(tab) => emittab(lcx, tab),
            BundleInit(tab, bundle) => emitbinit(lcx, tab, bundle),
            VarVal(var) => emitvarvalue(lcx, var),
            VarArm(var) => emitvararms(lcx, var),
            ModVal(model) => emitmodvalue(lcx, model),
            ModAvail(model) => emitmodavail(lcx, model),
            Query(query) => emitquery(lcx, query)
        }
    }
    swap(&mut *lcx.data.func, &mut lcx.ir.funcs[id]);
}

fn emitobjs(lcx: &mut Ccx<Lower<R, RW>, R>) {
    let objs = Access::borrow(&lcx.data.objs);
    for (&obj, &bump) in objs {
        match lcx.objs[obj].op {
            Obj::TAB => {
                lcx.data.tab = Tab::GLOBAL;
                let func = lcx.data.bump[bump.cast::<Tab>()].func;
                emittemplate(lcx, func, Template::TabInit(bump.cast()));
            },
            Obj::VAR => {
                let Var { base, tab, .. } = lcx.data.bump[bump.cast::<Var>()];
                lcx.data.tab = tab;
                emittemplate(lcx, base,   Template::VarVal(bump.cast()));
                emittemplate(lcx, base+1, Template::BundleInit(tab, base));
                emittemplate(lcx, base+2, Template::VarArm(bump.cast()));
                emittemplate(lcx, base+3, Template::BundleInit(tab, base+2));
            },
            Obj::MOD => {
                if lcx.data.bump[bump.cast::<Mod>()].mt == Mod::COMPLEX {
                    let Mod { base, tab, .. } = lcx.data.bump[bump.cast::<Mod>()];
                    lcx.data.tab = tab;
                    emittemplate(lcx, base,   Template::ModVal(bump.cast()));
                    emittemplate(lcx, base+1, Template::BundleInit(tab, base));
                    emittemplate(lcx, base+2, Template::ModAvail(bump.cast()));
                    emittemplate(lcx, base+3, Template::BundleInit(tab, base+2));
                }
            },
            Obj::QUERY => {
                let &QUERY { tab, ref value , .. } = &lcx.objs[obj.cast::<QUERY>()];
                lcx.data.tab = objs[&tab.erase()].cast();
                let mut query = Query::new(obj.cast());
                let putofs = lcx.perm.align_for::<Offset>();
                query.offsets = putofs.end();
                let mut func = Func::new(FuncKind::Query(query));
                let mut sig = func.build_signature();
                let mut cursor = 0;
                for &v in value {
                    let ann = lcx.objs[v].ann;
                    let align = match lcx.objs.get(ann) {
                        ObjectRef::TPRI(&TPRI { ty, .. }) => Primitive::from_u8(ty).to_ir(),
                        _ => Type::PTR
                    }.size();
                    // query cannot return FX:
                    debug_assert!(align > 0);
                    // layout query as:
                    //   struct {
                    //     struct {
                    //       ty11 field11;
                    //       ...
                    //       ty1N field1N;
                    //     } value1;
                    //     ...
                    //     struct { ... } valueM;
                    //   }
                    cursor = (cursor + align - 1) & !(align - 1);
                    for &ty in decomposition(&lcx.objs, ann, &mut lcx.data.tmp_ty) {
                        debug_assert!(cursor & (ty.size() - 1) == 0);
                        putofs.push(cursor as Offset);
                        sig = sig.add_return(ty);
                        cursor += ty.size();
                    }
                }
                sig.finish_returns().add_arg(IRT_IDX).finish_args();
                let func = lcx.ir.funcs.push(func);
                emittemplate(lcx, func, Template::Query(obj.cast()));
            },
            Obj::FUNC => todo!(),
            _ => unreachable!()
        }
    }
}

// construct and solve the dataflow equations:
//   for each function F, let R(F) denote its reset set.
//   for each explicit reset r and func F:
//     (1) r ∈ R(F) if node(F) ∈ r,   where node(F) is the node F was generated from.
//   for each pair of functions F, G:
//     (2) R(G) ⊂  R(F) if F calls G
fn computereset(ccx: &mut Ccx<Lower, R>) {
    let mut mat: BitMatrix<FuncId, ResetId> = Default::default();
    mat.resize(ccx.ir.funcs.end(), ResetId::MAXNUM.into());
    // mark explicit resets
    for (_, o) in ccx.objs.pairs() {
        if let ObjectRef::RESET(&RESET { id, ref objs, .. }) = o {
            let id: ResetId = zerocopy::transmute!(id);
            for &obj in objs {
                let ptr = ccx.data.objs[&obj];
                let base = match ccx.objs[obj].op {
                    Obj::VAR => {
                        // var: reset the variable
                        ccx.data.bump[ptr.cast::<Var>()].base
                    },
                    _ /* MOD */ => {
                        let model = &ccx.data.bump[ccx.data.objs[&obj].cast::<Mod>()];
                        match model.mt {
                            Mod::SIMPLE => {
                                // simple model: reset the variable
                                ccx.data.bump[model.value[0].var].base
                            },
                            _ /* COMPLEX */ => {
                                // complex model: reset the model
                                model.base
                            }
                        }
                    }
                };
                mat[base].set(id); // reset value
                mat[base+2].set(id); // reset arm (var) or avail (complex mod)
            }
        }
    }
    // construct call graph
    let mut df: Dataflow<FuncId> = Default::default();
    for (f, func) in ccx.ir.funcs.pairs() {
        df.push();
        for (_, ins) in func.code.pairs() {
            if (Opcode::CALLB|Opcode::CALLBI).contains(ins.opcode()) {
                let (_, _, g) = ins.decode_CALLB();
                if f != g {
                    df.raw_inputs().push(g);
                }
            }
        }
    }
    // we won't be calling compute_uses() so push the dummy end node manually
    df.push();
    // solve the system
    let mut solver: DataflowSystem<FuncId> = Default::default();
    solver.resize(ccx.ir.funcs.end());
    solver.queue_all(ccx.ir.funcs.end());
    while let Some(f) = solver.poll() {
        for &g in df.inputs(f) {
            let [fr, gr] = mat.get_rows_mut([f,g]);
            if !gr.is_subset(fr) {
                fr.union(gr);
                solver.queue(f);
            }
        }
    }
    // update ir
    for (id, func) in ccx.ir.funcs.pairs_mut() {
        if let FuncKind::Bundle(bundle) = &mut func.kind {
            let reset: ResetSet = mat[id].try_into().unwrap();
            bundle.reset = reset | ResetId::GLOBAL;
        }
    }
}

impl Phase for Lower {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Lower {
            bump: Default::default(),
            objs: Default::default(),
            expr: Default::default(),
            tmp_ins: Default::default(),
            tmp_vty: Default::default(),
            tmp_ty: Default::default(),
            func: Access::new(Func::new(FuncKind::User())),
            tab: BumpRef::zero()
        })
    }

    fn run(ccx: &mut Ccx<Lower>) -> compile::Result {
        collectobjs(ccx);
        emitobjs(unsafe { core::mem::transmute(&mut *ccx) });
        ccx.freeze_graph(computereset);
        if trace!(LOWER) {
            trace!("{}", {
                let mut tmp = Default::default();
                dump_ir(&mut tmp, &ccx.ir);
                tmp
            })
        }
        Ok(())
    }

}
