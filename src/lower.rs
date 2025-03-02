//! Graph -> IR.

use core::cmp:: min;
use core::iter::{repeat_n, zip};
use core::mem::{replace, swap};

use alloc::vec::Vec;

use crate::bitmap::BitMatrix;
use crate::bump::{self, Bump, BumpRef};
use crate::compile::{self, Ccx, Stage};
use crate::dump::dump_ir;
use crate::hash::HashMap;
use crate::index::{IndexOption, InvalidValue};
use crate::ir::{self, Chunk, Func, FuncId, FuncKind, Ins, InsId, Opcode, Phi, PhiId, Query, SignatureBuilder, Type, IR};
use crate::lang::Lang;
use crate::mem::{Offset, ResetId, ResetSet, SizeClass};
use crate::obj::{cast_args, cast_args_raw, obj_index_of, BinOp, Intrinsic, Obj, ObjRef, ObjectRef, Objects, Operator, BINOP, CALLX, CAT, DIM, EXPR, FLAT, GET, INTR, KFP64, KINT, KINT64, KSTR, LEN, LOAD, MOD, NEW, QUERY, RESET, SPEC, SPLAT, TAB, TPRI, TTEN, TTUP, VAR, VGET, VSET};
use crate::trace::trace;
use crate::typestate::{Absent, Access, R, RW};
use crate::typing::{Primitive, IRT_IDX};

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

fn pushdeco<'o,'d>(objs: &'o Objects, idx: ObjRef, deco: &'d mut [Type]) -> &'d mut [Type] {
    match objs.get(objs.totype(idx)) {
        ObjectRef::TPRI(&TPRI { ty, ..  }) => {
            deco[0] = Primitive::from_u8(ty).to_ir();
            &mut deco[1..]
        },
        ObjectRef::TTEN(&TTEN { dim, elem, .. }) => {
            let decos = decomposition_size(objs, elem);
            deco[..decos].fill(Type::PTR);
            deco[decos..decos+dim as usize].fill(IRT_IDX);
            &mut deco[decos+dim as usize..]
        },
        ObjectRef::TTUP(TTUP { elems, .. }) => {
            let mut d = deco;
            for &e in elems {
                d = pushdeco(objs, e, d);
            }
            d
        },
        _ => unreachable!()
    }
}

fn pushdeco__old(objs: &Objects, idx: ObjRef, deco: &mut Vec<Type>) {
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
                pushdeco__old(objs, e, deco);
            }
        },
        _ => unreachable!()
    }
}

pub fn decomposition<'objs, 'bump>(
    objs: &'objs Objects,
    idx: ObjRef,
    bump: &'bump mut Bump
) -> &'bump mut [Type] {
    let decos = decomposition_size(objs, idx);
    let (_, deco) = bump.reserve_slice_init(decos, Type::FX);
    pushdeco(objs, idx, deco);
    deco
}

fn decomposition__old<'objs, 'work>(
    objs: &'objs Objects,
    idx: ObjRef,
    work: &'work mut Vec<Type>
) -> &'work [Type] {
    work.clear();
    pushdeco__old(objs, idx, work);
    &*work
}

#[repr(C)] // need repr(C) for transmuting references
pub struct Lower<O=RW, F=RW> {
    bump: Access<Bump<u32>, O>,
    objs: Access<HashMap<ObjRef, BumpRef<()>>, O>,
    expr: HashMap<ObjRef<EXPR>, InsId>,
    // TODO: remove the following tmp_* fields and use ccx.tmp instead:
    tmp_ins: Vec<InsId>,
    tmp_vty: Vec<Type>, // for emitvarvalue
    tmp_ty: Vec<Type>, // for expressions
    // current function:
    func: Access<Func, F>,
    tab: BumpRef<Tab>,
}

// for emit*
pub type Lcx<'a, 'b, 'c> = Ccx<Lower<R<'a>, R<'b>>, R<'c>>;

// for callx (&mut Lcx -> &mut CLcx is ok because &mut T -> &mut UnsafeCell<T> is ok).
// the point of this is to tell the compiler that emitcallx won't replace the current stage data.
pub type CLcx<'a, 'b, 'c> = Ccx<Access<Lower, R<'a>>, R<'b>, R<'c>>;

// integer type used for selecting models.
// note: var.def only has 8 bits anyway, so this can't go higher
const IRT_ARM: Type = Type::I8;

// entry instruction is always emitted as #0
const INS_ENTRY: InsId = zerocopy::transmute!(0u16);

// vars, models, and tabs always emit this as ins #1
const INS_FLATIDX: InsId = zerocopy::transmute!(1u16);

// expr obj.mark:
// const EXPR_NONE: u8 = 0;  // no uses
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
    let mut func = Func::new(FuncKind::Chunk(Chunk::new(SizeClass::GLOBAL)));
    let mut sig = func.build_signature().add_return(IRT_IDX);
    for &size in axes {
        let rank = match ctx.objs[ctx.objs[size].ann].op {
            Obj::TPRI | Obj::TTUP => Axis::SCALAR,
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
    let mut func = Func::new(FuncKind::Chunk(Chunk::new(SizeClass::GLOBAL)));
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
        let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)));
        let mut sig = func.build_signature();
        for &ty in decomposition__old(&ctx.objs, var.ann, &mut lower.tmp_ty) {
            sig = sig.add_return(ty);
        }
        maybeidxarg(sig.finish_returns(), scl).finish_args();
        ctx.ir.funcs.push(func);
    }
    // value.init:
    makeinitfunc(&mut ctx.ir);
    // arm:
    {
        let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)));
        maybeidxarg(func.build_signature().add_return(IRT_ARM).finish_returns(), scl).finish_args();
        ctx.ir.funcs.push(func);
    }
    // arm.init
    makeinitfunc(&mut ctx.ir);
    trace!(LOWER "VAR {:?} value: {:?}[{:?}] arm: {:?}[{:?}]", idx, base, base+1, base+2, base+3);
}

fn iterflatidx<'a>(
    objs: &'a Objects,
    idx: &'a [ObjRef<EXPR>]
) -> impl Iterator<Item=ObjRef<EXPR>> + 'a {
    idx.iter()
        .enumerate()
        .map(|(i,&e)| match objs[e].op {
            Obj::FLAT => &objs[e.cast::<FLAT>()].idx,
            _ => &idx[i..i+1]
        })
        .flatten()
        .cloned()
}

fn issplatidx(objs: &Objects, idx: &[ObjRef<EXPR>]) -> bool {
    iterflatidx(objs, idx).all(ObjRef::<EXPR>::is_nil)
}

fn isprefixidx(objs: &Objects, source: ObjRef<TAB>, vset: &VSET) -> bool {
    if !issplatidx(objs, &vset.idx) { return false }
    let target = objs[vset.var].tab;
    if source == target { return true; } // skip
    let sax = &objs[objs[source].shape].fields;
    let sdim = sax.len();
    if sdim == 0 { return true; } // skip
    let tax = &objs[objs[target].shape].fields;
    let tdim = objs.dim(target);
    if sdim > tdim { return false; }
    if tdim == sdim+1 && tax[..sdim].iter().all(|o| o.is_nil()) {
        // explicitly detect the special case:
        //   table A[...]
        //   table B[:,...,:,A.var]
        // TODO more sophisticated analysis for this
        if let ObjectRef::VGET(&VGET { var, idx: [], .. }) = objs.get(tax[sdim].erase()) {
            if objs[var].tab == source {
                return true;
            }
        }
    }
    objs.allequal(cast_args(sax), cast_args(&tax[..sdim]))
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
        } else if isprefixidx(&ctx.objs, obj.tab, vset) && {
            // TODO: the current code assumes that the value is rectangular,
            // but the optimization itself doesn't necessarily require it, non-rectangular values
            // just require more logic when storing/loading.
            let ann = ctx.objs[vset.value].ann;
            let vann = ctx.objs[vset.var].ann;
            ann == vann
                || (ctx.objs[ann].op == Obj::TTEN && ctx.objs[ann.cast::<TTEN>()].elem == vann)
        } {
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
            let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)));
            let mut sig = func.build_signature();
            for vset in &lower.bump[model].value {
                for &ty in decomposition__old(
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
            let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)));
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
    func.code.push(Ins::PHI(func.phis.at(phi).type_, INS_ENTRY, phi))
}

pub fn reserve(func: &Func, num: usize) -> InsId {
    func.code.extend(repeat_n(Ins::NOP_FX, num))
}

pub fn decompose(func: &Func, objs: &Objects, ty: ObjRef, value: InsId) -> InsId {
    let ds = decomposition_size(objs, ty);
    match ds {
        1 => value,
        _ => {
            let mut ret = func.code.push(Ins::NOP(Type::LSV));
            for i in (0..ds).rev() {
                ret = func.code.push(Ins::CARG(ret, value + i as isize));
            }
            ret
        }
    }
}

#[inline(always)]
pub fn areserve<const K: usize>(func: &Func) -> [InsId; K] {
    let r = reserve(func, K);
    let mut out = [InsId::INVALID.into(); K];
    for i in 0..K { out[i] = r+i as isize; }
    out
}

fn emitjumpifnot(func: &Func, ctr: &mut InsId, cond: InsId, target: InsId) -> InsId {
    let next = reserve(func, 1);
    func.code.set(*ctr, Ins::IF(cond, next, target));
    *ctr = next;
    next
}

fn newcall(idx: InsId, init: InsId, node: FuncId, inline: bool) -> Ins {
    let opcode = match inline {
        false => Opcode::CALLC,
        true  => Opcode::CALLCI
    };
    Ins::new(opcode, Type::FX)
        .set_a(zerocopy::transmute!(idx))
        .set_b(zerocopy::transmute!(init))
        .set_c(zerocopy::transmute!(node))
}

fn emitcallvm(lower: &Lower<R, R>, idx: InsId, node: FuncId, inline: bool) -> InsId {
    let func = &lower.func;
    let zero = func.code.push(Ins::KINT(IRT_IDX, 0));
    let knop = func.code.push(Ins::NOP(Type::FX));
    let callinit = func.code.push(newcall(zero, knop, node+1, lower.bump[lower.tab].n == 0));
    let init = func.code.push(Ins::RES(Type::FX, callinit, 0.into()));
    func.code.push(newcall(idx, init, node, inline))
}

fn emitcallvm1(lower: &Lower<R, R>, idx: InsId, node: FuncId) -> InsId {
    emitcallvm(lower, idx, node, idx == INS_FLATIDX)
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

fn emitmultistoreinto(
    func: &Func,
    buf: InsId,
    stride: InsId,
    idx: InsId,
    value: InsId,
    store: InsId,
    num: usize
) {
    for i in 0..num as isize {
        let ofs = func.code.push(Ins::MUL(IRT_IDX, idx, stride+i));
        let ptr = func.code.push(Ins::ADDP(buf+i, ofs));
        func.code.set(store+i, Ins::STORE(ptr, value+i));
    }
}

fn emitmultistore(
    func: &Func,
    buf: InsId,
    stride: InsId,
    idx: InsId,
    value: InsId,
    num: usize
) -> InsId {
    let store = reserve(func, num);
    emitmultistoreinto(func, buf, stride, idx, value, store, num);
    store
}

fn vardata(objs: &HashMap<ObjRef, BumpRef<()>>, var: ObjRef<VAR>) -> BumpRef<Var> {
    objs[&var.erase()].cast()
}

// TODO: remove this and replace uses with code.set(replace(ctr, new), ins)
fn swapctr(func: &Func, ctr: &mut InsId, ins: Ins, new: InsId) {
    func.code.set(*ctr, ins);
    *ctr = new;
}

/* ---- Loops --------------------------------------------------------------- */

struct LoopState {
    head: InsId,      // uninitialized slot for initialization (dominates body and tail)
    tail: InsId,      // uninitialized slot for next/exit
    body: InsId,      // uninitialized slot for the loop body (dominates tail)
    out: InsId,       // initialized jump target for breaking the loop
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

fn extractshape(objs: &Objects, value: InsId, ty: &TTEN) -> InsId {
    let ds = decomposition_size(objs, ty.elem);
    value + ds as isize
}

fn emittensordataloop(
    lcx: &mut Lcx,
    loop_: &mut LoopState,
    ty: &TTEN,
    value: InsId,
    shape: InsId
) -> InsId {
    let ds = decomposition_size(&lcx.objs, ty.elem);
    let len = emitshapelen(&lcx.data.func, shape, ty.dim as _);
    let zero = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    let i = emitrangeloop(&lcx.data.func, loop_, IRT_IDX, zero, len);
    let loads = reserve(&lcx.data.func, ds as _);
    let base = lcx.tmp.end();
    for (j,&ty) in decomposition(&lcx.objs, ty.elem, &mut lcx.tmp).iter().enumerate() {
        let ptr = emitarrayptr(&lcx.data.func, value + j as isize, i, ty);
        lcx.data.func.code.set(loads + j as isize, Ins::LOAD(ty, ptr));
    }
    lcx.tmp.truncate(base);
    loads
}

fn emittensorloop(
    lcx: &mut Lcx,
    loop_: &mut LoopState,
    ty: &TTEN,
    value: InsId
) -> InsId {
    let shape = extractshape(&lcx.objs, value, ty);
    emittensordataloop(lcx, loop_, ty, value, shape)
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
    start: Ins,   // start instruction (patch ctr)
    l_phi: PhiId, // result phis outside loop (final accumulator)
    r_phi: PhiId, // accumulator phis inside loop body
    init: InsId,  // initial accumulator values (inside loop head)
    value: InsId, // accumulator values (inside loop body)
    body: InsId,  // loop body start
    tail: InsId,  // loop tail start
    num: u16,     // number of accumulators
}

fn newreduce(func: &Func, l_phi: PhiId, r_phi: PhiId, init: InsId, num: u16) -> Reduce {
    let [out, head, body, tail] = areserve(func);
    let value = func.code.extend(
        (0..num as isize)
        .map(|i| Ins::PHI(func.phis.at(l_phi+i).type_, body, l_phi+i))
    );
    let mut start = Ins::JMP(init, head, r_phi);
    for i in 1..num as isize {
        let idx = func.code.push(start);
        start = Ins::JMP(init + i, idx, r_phi + i);
    }
    Reduce {
        loop_: LoopState { head, tail, body, out },
        start, l_phi, r_phi, init, value, body, tail, num
    }
}

fn newreducety<const K: usize>(func: &Func, ty: [Type; K], init: InsId) -> Reduce {
    let l_phis = func.phis.extend(ty.map(Phi::new));
    let r_phis = func.phis.extend(ty.map(Phi::new));
    newreduce(func, l_phis, r_phis, init, K as _)
}

fn newreducefx(func: &Func, num: u16) -> Reduce {
    let l_phis = func.phis.extend(repeat_n(Phi::new(Type::FX), num as usize));
    let r_phis = func.phis.extend(repeat_n(Phi::new(Type::FX), num as usize));
    let inits = func.code.extend(repeat_n(Ins::NOP(Type::FX), num as usize));
    newreduce(func, l_phis, r_phis, inits, num)
}

// logically this takes ownership of the reduce, in the sense that it shouldn't be used anymore.
// but taking a reference here makes usage a bit more ergonomic.
fn closereduce(func: &Func, reduce: &Reduce, next: InsId) -> InsId {
    let &Reduce { l_phi, r_phi, init, body, tail, num, ..} = reduce;
    let mut jhead = Ins::JMP(init, body, l_phi);
    let mut jbody = Ins::JMP(next, tail, r_phi);
    let mut jtail = Ins::JMP(next, body, l_phi);
    for i in 1..num as isize {
        let base = func.code.extend([jhead, jbody, jtail].into_iter());
        jhead = Ins::JMP(init + i, base, l_phi + i);
        jbody = Ins::JMP(next + i, base+1, r_phi + i);
        jtail = Ins::JMP(next + i, base+2, l_phi + i);
    }
    func.code.set(reduce.loop_.head, jhead);
    func.code.set(reduce.loop_.body, jbody);
    func.code.set(reduce.loop_.tail, jtail);
    func.code.extend(
        (0..num as isize)
        .map(|i| Ins::PHI(func.phis.at(r_phi+i).type_, reduce.loop_.out, r_phi+i))
    )
}

fn emitreducestore(
    func: &Func,
    reduce: &mut Reduce,
    bufs: InsId,
    strides: InsId,
    values: InsId,
    start: IndexOption<InsId>
) -> InsId {
    let idx_phi = func.phis.push(Phi::new(IRT_IDX));
    let [head, tail] = areserve(func);
    let start = match start.unpack() {
        Some(i) => i,
        None => func.code.push(Ins::KINT(IRT_IDX, 0))
    };
    func.code.set(reduce.loop_.head, Ins::JMP(start, head, idx_phi));
    reduce.loop_.head = head;
    let idx = func.code.push(Ins::PHI(IRT_IDX, reduce.loop_.body, idx_phi));
    let next = emitmultistore(func, bufs, strides, idx, values, reduce.num as _);
    let one = func.code.push(Ins::KINT(IRT_IDX, 1));
    let next_idx = func.code.push(Ins::ADD(IRT_IDX, idx, one));
    func.code.set(reduce.loop_.tail, Ins::JMP(next_idx, tail, idx_phi));
    reduce.loop_.tail = tail;
    next
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
    tab: &Tab,         // *target* table being indexed
    call: InsId,       // CALLC(I) of tab
    axis: usize,       // current axis (N)
    flat: InsId        // flat index for current axis (N)
) -> InsId {
    // note: if axis=0, then flat is either zero (the only valid index), or one (one past the last
    // valid index)
    match &tab.axes[axis] {
        &Axis { rank: Axis::SCALAR, ret, .. } => {
            let size = lcx.data.func.code.push(Ins::RES(IRT_IDX, call, ret));
            lcx.data.func.code.push(Ins::MUL(IRT_IDX, flat, size))
        },
        &Axis { /* VECTOR */ ret, .. } => {
            let f = lcx.data.func.code.push(Ins::RES(Type::PTR, call, ret));
            let ptr = emitarrayptr(&lcx.data.func, f, flat, IRT_IDX);
            lcx.data.func.code.push(Ins::LOAD(IRT_IDX, ptr))
        }
    }
}

// forward transform multiple times
fn idxftrann(
    lcx: &mut Lcx,
    tab: &Tab,
    call: InsId,
    start_axis: usize,
    end_axis: usize,
    mut flat: InsId
) -> InsId {
    debug_assert!(start_axis <= end_axis);
    for axis in start_axis..end_axis {
        flat = idxftran(lcx, tab, call, axis, flat);
    }
    flat
}

// given a flat index
//   tab[i1, ..., iN, i{N+1}]
// emit the flat index
//   tab[i1, ..., iN]
// (the index i{N+1} can be obtained by doing a forward transform and taking the difference)
fn idxbtran(
    lcx: &mut Lcx,
    tab: &Tab,         // *target* table being indexed
    call: InsId,       // CALLC(I) of tab
    axis: usize,       // current axis (N+1)
    flat: InsId        // flat index for current axis (N+1)
) -> InsId {
    debug_assert!(axis > 0);
    if axis == 1 {
        // the only valid flat index for the zeroth axis is zero,
        // therefore back transforming anything to the zeroth axis yields zero.
        return lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    }
    let Axis { rank, ret, .. } = tab.axes[axis-1];
    match rank {
        Axis::SCALAR => {
            let size = lcx.data.func.code.push(Ins::RES(IRT_IDX, call, ret));
            lcx.data.func.code.push(Ins::DIV(IRT_IDX, flat, size))
        },
        _ /* VECTOR */ => {
            let b = lcx.data.func.code.push(Ins::RES(Type::PTR, call, ret+1));
            let ptr = emitarrayptr(&lcx.data.func, b, flat, IRT_IDX);
            lcx.data.func.code.push(Ins::LOAD(IRT_IDX, ptr))
        }
    }
}

fn commonprefixobj(objs: &Objects, a: &Tab, b: &Tab) -> usize {
    zip(a.axes.iter(), b.axes.iter())
        .take_while(|(aa, ab)| objs.equal(aa.size.erase(), ab.size.erase()))
        .count()
}

// given tables
//   A[i1, ..., iN]
//   B[j1, ..., jM]
// returns the largest K such that
//   ik = jk for all 0 <= k < K
fn commonprefix(lcx: &Lcx, mut a: BumpRef<Tab>, b: BumpRef<Tab>) -> usize {
    let mut ta = &lcx.data.bump[a];
    if a == b { return ta.axes.len() };
    let mut tb = &lcx.data.bump[b];
    if tb.axes.len() < ta.axes.len() {
        (a, ta, tb) = (b, tb, ta);
    }
    let adim = ta.axes.len();
    let bdim = tb.axes.len();
    if bdim == adim+1 && tb.axes[..adim].iter().all(|x| x.size.is_nil()) {
        // explicitly detect:
        //   table A[...]
        //   table B[;...,:,A.var]
        // TODO more sophisticated analysis for this
        if let ObjectRef::VGET(&VGET { var, idx: [], .. }) = lcx.objs.get(tb.axes[adim].size.erase()) {
            if let Some(v) = lcx.data.objs.get(&var.erase()) {
                if lcx.data.bump[v.cast::<Var>()].tab == a {
                    return adim;
                }
            }
        }
    }
    commonprefixobj(&lcx.objs, ta, tb)
}

// do A and B have the exact same shape?
fn sametab(objs: &Objects, a: &Tab, b: &Tab) -> bool {
    (a as *const Tab as *const () == b as *const Tab as *const ())
        || (a.n == b.n && a.n as usize == commonprefixobj(objs, a, b))
}

fn emittabcall(func: &Func, tabf: FuncId) -> InsId {
    let zero = func.code.push(Ins::KINT(IRT_IDX, 0));
    let init = func.code.push(Ins::NOP(Type::FX));
    func.code.push(Ins::CALLC(zero, init, tabf))
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
    let prefix = commonprefix(lcx, source, target);
    let bump = Access::borrow(&lcx.data.bump);
    let source = &bump[source];
    let target = &bump[target];
    let sourcecall = match source_axis > min(target_axis, prefix) {
        true  => emittabcall(&lcx.data.func, source.func),
        false => InsId::INVALID.into()
    };
    let targetcall = match target_axis > min(source_axis, prefix) {
        true  => emittabcall(&lcx.data.func, target.func),
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
        // base+i will hold the prefix+1+i'th NON-flat index in `source`.
        let source_axis0 = source_axis;
        let mut base = reserve(&lcx.data.func, source_axis-prefix);
        while source_axis > prefix {
            let prev = idxbtran(lcx, source, sourcecall, source_axis, flat);
            source_axis -= 1;
            let start = idxftran(lcx, source, sourcecall, source_axis, prev);
            lcx.data.func.code.set(
                base + (source_axis-prefix) as isize,
                Ins::SUB(IRT_IDX, flat, start)
            );
            flat = prev;
        }
        while source_axis < source_axis0 {
            flat = idxftran(lcx, target, targetcall, source_axis, flat);
            flat = lcx.data.func.code.push(Ins::ADD(IRT_IDX, flat, base));
            base += 1;
            source_axis += 1;
        }
    }
    if source_axis < target_axis {
        flat = idxftrann(lcx, target, targetcall, source_axis, target_axis, flat);
    }
    flat
}

// given a flat index
//   tab[i1, ..., i{source_axis}]
// emit
//   i{target_axis}
fn axisidx(
    lcx: &mut Lcx,
    tab: BumpRef<Tab>,
    source_axis: usize,
    target_axis: usize,
    flat: InsId
) -> InsId {
    let flat = idxtransfer(lcx, tab, tab, source_axis, target_axis, flat);
    if target_axis <= 1 {
        // 0: index is zero
        // 1: index is `flat-0`
        return flat;
    }
    let bump = Access::borrow(&lcx.data.bump);
    let tab = &bump[tab];
    let call = emittabcall(&lcx.data.func, tab.func);
    let back = idxbtran(lcx, tab, call, target_axis, flat);
    let fwd = idxftran(lcx, tab, call, target_axis-1, back);
    lcx.data.func.code.push(Ins::SUB(IRT_IDX, flat, fwd))
}

// given a target table and an index expression
//   tab[i1, ..., iN]
// return true iff instances of the source table will NOT select overlapping indices.
fn isdisjointidx(source: &Tab, target: &Tab, idx: &[ObjRef<EXPR>]) -> bool {
    // TODO: analyze explicit indices
    source.n <= target.n && idx.len() <= (target.n-source.n) as usize
}

// return the number of implicit prefix dimensions when indexing from a `source_dim`-dimensional
// table into a `target_dim`-dimensional table with `explicit` explicit indices.
fn prefixlen(source_dim: usize, target_dim: usize, explicit: usize) -> usize {
    min(source_dim, target_dim-explicit)
}

// return the number of tail dimensions
fn taillen(source_dim: usize, target_dim: usize, explicit: usize) -> usize {
    target_dim - (prefixlen(source_dim, target_dim, explicit) + explicit)
}

// given a target table and an index expression
//   target[i1, ..., iN]
// return true if iterating over flat indices requires two or more nested loops.
fn isnestedloopidx(lcx: &Lcx, source: &Tab, target: &Tab, idx: &[ObjRef<EXPR>]) -> bool {
    if idx.is_empty() {
        // fast path
        return false
    }
    let mut foundloop = false;
    let mut nil = false;
    let mut explicit = 0;
    for i in iterflatidx(&lcx.objs, idx) {
        explicit += 1;
        let wasnil = nil;
        nil = i.is_nil();
        if isscalarann(&lcx.objs, i.erase()) {
            continue
        }
        if (lcx.objs[i].op, lcx.objs[i].data) == (Obj::SPEC, SPEC::SLURP) {
            continue
        }
        if nil && wasnil {
            continue
        }
        if foundloop {
            return true
        }
        foundloop = true;
    }
    foundloop && !nil && taillen(source.axes.len(), target.axes.len(), explicit) > 0
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

fn emitsplatbounds(
    lcx: &mut Lcx,
    tab: &Tab,
    flat: InsId,
    call: InsId,
    start_axis: usize,
    end_axis: usize,
) -> (InsId, InsId) {
    let one = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
    let end = lcx.data.func.code.push(Ins::ADD(IRT_IDX, flat, one));
    let start = idxftrann(lcx, tab, call, start_axis, end_axis, flat);
    let end = idxftrann(lcx, tab, call, start_axis, end_axis, end);
    (start, end)
}

fn emitsplatloop(
    lcx: &mut Lcx,
    loop_: &mut LoopState,
    tab: &Tab,
    flat: InsId,
    call: InsId,
    axis: usize,
    endaxis: usize,
) -> InsId {
    let (start, end) = emitsplatbounds(lcx, tab, flat, call, axis, endaxis);
    emitrangeloop(&lcx.data.func, loop_, IRT_IDX, start, end)
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
fn emitlogic(func: &Func, ctr: &mut InsId, left: InsId, right: InsId, op: BinOp) -> InsId {
    debug_assert!((BinOp::AND | BinOp::OR).contains(op));
    let merge = reserve(func, 1);
    let phi = func.phis.push(Phi::new(Type::B1));
    let mut ri = func.code.push(Ins::JMP(right, merge, phi));
    let kbool = func.code.push(Ins::KINT(Type::B1, (op == BinOp::OR) as _));
    let mut other = func.code.push(Ins::JMP(kbool, merge, phi));
    if op == BinOp::OR { (ri, other) = (other, ri); }
    swapctr(func, ctr, Ins::IF(left, ri, other), merge);
    func.code.push(Ins::PHI(Type::B1, merge, phi))
}

fn emitcmp(func: &Func, left: InsId, right: InsId, op: BinOp, ty: Primitive) -> InsId {
    let opcode = match (op, ty.is_unsigned()) {
        (BinOp::LT, true)  => Opcode::ULT,
        (BinOp::LT, false) => Opcode::LT,
        (BinOp::LE, true)  => Opcode::ULE,
        (BinOp::LE, false) => Opcode::LE,
        _ => unreachable!()
    };
    func.code.push(
        Ins::new(opcode, Type::B1)
            .set_a(zerocopy::transmute!(left))
            .set_b(zerocopy::transmute!(right))
    )
}

fn emitscalarbinop(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    op: BinOp,
    ty: Primitive,
    left: InsId,
    right: InsId
) -> InsId {
    use BinOp::*;
    let irt = ty.to_ir();
    match op {
        OR|AND => emitlogic(&lcx.data.func, ctr, left, right, op),
        ADD   => lcx.data.func.code.push(Ins::ADD(irt, left, right)),
        SUB   => lcx.data.func.code.push(Ins::SUB(irt, left, right)),
        MUL   => lcx.data.func.code.push(Ins::MUL(irt, left, right)),
        DIV if ty.is_unsigned() => lcx.data.func.code.push(Ins::UDIV(irt, left, right)),
        DIV   => lcx.data.func.code.push(Ins::DIV(irt, left, right)),
        POW   => lcx.data.func.code.push(Ins::POW(irt, left, right)),
        EQ    => lcx.data.func.code.push(Ins::EQ(left, right)),
        NE    => lcx.data.func.code.push(Ins::NE(left, right)),
        LT|LE => emitcmp(&lcx.data.func, left, right, op, ty)
    }
}

fn broadcastbinop(
    lcx: &mut Lcx,
    loop_: &mut LoopState,
    op: BinOp,
    ty: ObjRef,
    left: ObjRef<EXPR>,
    right: ObjRef<EXPR>
) -> InsId {
    let lhs = emitbroadcast(lcx, loop_, left);
    let rhs = emitbroadcast(lcx, loop_, right);
    match lcx.objs.get(ty) {
        ObjectRef::TPRI(&TPRI { ty, .. }) => emitscalarbinop(lcx, &mut loop_.body, op,
            Primitive::from_u8(ty), lhs, rhs),
        t => {
            debug_assert!(matches!(t, ObjectRef::TTEN(_)));
            // TODO: this *can* be implemented by materializing it here.
            // whether that's even useful is another question.
            // but it makes sense from the type system perspective
            // (+ :: (T,T) -> T regardless of whether T is scalar or tensor[U,N] or
            // tensor[tensor[U,N],M] or ... you get the idea)
            todo!()
        }
    }
}

fn emitscalarintrinsic(
    lcx: &mut Lcx,
    _ctr: &mut InsId,
    f: Intrinsic,
    _args: &[ObjRef<EXPR>],
    ty: Type,
    base: BumpRef<InsId>
) -> InsId {
    use Intrinsic::*;
    let argv = &lcx.tmp[base..];
    let func = &lcx.data.func;
    match f {
        UNM|NOT => func.code.push(Ins::NEG(ty, argv[0])),
        EXP     => todo!(), // ir intrinsic call?
        LOG     => todo!(), // ir intrinsic call?
        CONV    => todo!(),
        _       => unreachable!() // non-scalar
    }
}

fn emitsum(lcx: &mut Lcx, ctr: &mut InsId, arg: ObjRef<EXPR>, ty: Type) -> InsId {
    if isscalarann(&lcx.objs, arg.erase()) {
        return emitvalue(lcx, ctr, arg);
    }
    let zero = lcx.data.func.code.push(Ins::KINT(ty, 0));
    let mut reduce = newreducety(&lcx.data.func, [ty], zero);
    let elem = emititer(lcx, &mut reduce.loop_, arg);
    let next = lcx.data.func.code.push(Ins::ADD(ty, reduce.value, elem));
    swapctr(&lcx.data.func, ctr, reduce.start, reduce.loop_.out);
    closereduce(&lcx.data.func, &reduce, next)
}

fn emitanyall(lcx: &mut Lcx, ctr: &mut InsId, arg: ObjRef<EXPR>, f: Intrinsic) -> InsId {
    let resphi = lcx.data.func.phis.push(Phi::new(Type::B1));
    let [tail, body, merge] = areserve(&lcx.data.func);
    let default = lcx.data.func.code.push(Ins::KINT(Type::B1, (f == Intrinsic::ALL) as _));
    let notdefault = lcx.data.func.code.push(Ins::KINT(Type::B1, (f == Intrinsic::ANY) as _));
    let out = lcx.data.func.code.push(Ins::JMP(default, merge, resphi));
    let found = lcx.data.func.code.push(Ins::JMP(notdefault, merge, resphi));
    let mut loop_ = LoopState { head: *ctr, tail, body, out };
    let value = emititer(lcx, &mut loop_, arg);
    lcx.data.func.code.set(loop_.body, if f == Intrinsic::ALL {
        Ins::IF(value, tail, found)
    } else {
        Ins::IF(value, found, tail)
    });
    lcx.data.func.code.set(loop_.tail, Ins::GOTO(body));
    lcx.data.func.code.set(loop_.head, Ins::GOTO(body));
    *ctr = merge;
    lcx.data.func.code.push(Ins::PHI(Type::B1, merge, resphi))
}

fn scalarintrinsic(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    f: Intrinsic,
    args: &[ObjRef<EXPR>],
    ty: Type
) -> InsId {
    use Intrinsic::*;
    match f {
        SUM => emitsum(lcx, ctr, args[0], ty),
        ANY|ALL => emitanyall(lcx, ctr, args[0], f),
        _ => {
            let base = lcx.tmp.end();
            for &arg in args {
                let v = emitvalue(lcx, ctr, arg);
                lcx.tmp.push(v);
            }
            let v = emitscalarintrinsic(lcx, ctr, f, args, ty, base.cast_up());
            lcx.tmp.truncate(base);
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
    let base = lcx.tmp.end();
    for &arg in args {
        let v = emititer(lcx, loop_, arg);
        lcx.tmp.push(v);
    }
    let v = match lcx.objs.get(ety) {
        ObjectRef::TPRI(&TPRI { ty, .. }) => {
            emitscalarintrinsic(lcx, &mut loop_.body, f, args, Primitive::from_u8(ty).to_ir(),
                base.cast_up())
        },
        _ => {
            // see comment in `broadcastbinop`
            todo!()
        }
    };
    lcx.tmp.truncate(base);
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
        lang.lower(lcx, *ctr, callx, &lower.func, &lower.tmp_ins[base..])
    };
    lcx.data.tmp_ins.truncate(base);
    value
}

fn emitcat(lcx: &mut Lcx, ctr: &mut InsId, cat: &CAT) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    let cty = &objs[cat.ann.cast::<TTEN>()];
    debug_assert!(cty.op == Obj::TTEN);
    if cty.dim != 1 { todo!() }
    let idxs = reserve(&lcx.data.func, (cat.elems.len()+1) as _);
    lcx.data.func.code.set(idxs, Ins::KINT(IRT_IDX, 0));
    for (i, &e) in cat.elems.iter().enumerate() {
        let len = match objs[e].op {
            Obj::SPLAT => emitshape(lcx, ctr, objs[e.cast::<SPLAT>()].value),
            _ => lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1))
        };
        lcx.data.func.code.set(idxs + 1 + i as isize, Ins::ADD(IRT_IDX, idxs + i as isize, len));
    }
    let ds = decomposition_size(objs, cty.elem);
    let (ptrs, esizes) = alloctensordata(lcx, *ctr, cty, idxs + cat.elems.len() as isize);
    let mut effects: IndexOption<InsId> = None.into();
    for (i, &e) in cat.elems.iter().enumerate() {
        let stores = match objs[e].op {
            Obj::SPLAT => {
                let mut reduce = newreducefx(&lcx.data.func, ds as _);
                let value = emititer(lcx, &mut reduce.loop_, objs[e.cast::<SPLAT>()].value);
                let next = emitreducestore(&lcx.data.func, &mut reduce, ptrs, esizes, value,
                    Some(idxs + i as isize).into());
                swapctr(&lcx.data.func, ctr, reduce.start, reduce.loop_.out);
                closereduce(&lcx.data.func, &reduce, next)
            },
            _ => {
                let value = emitvalue(lcx, ctr, e);
                emitmultistore(&lcx.data.func, ptrs, esizes, idxs + i as isize, value, ds)
            }
        };
        effects = Some(match effects.unpack() {
            Some(fx) => lcx.data.func.code.extend(
                (0..ds as isize).map(|j| Ins::MOVF(Type::FX, fx+j, stores+j))),
            None => stores
        }).into();
    }
    let ret = match effects.unpack() {
        Some(fx) => lcx.data.func.code.extend(
            (0..ds as isize).map(|i| Ins::MOVF(Type::PTR, ptrs+i, fx+i))),
        None => lcx.data.func.code.extend((0..ds as isize).map(|i| Ins::MOV(Type::PTR, ptrs+i)))
    };
    lcx.data.func.code.push(Ins::MOV(IRT_IDX, idxs + cat.elems.len() as isize));
    ret
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
    let i = emitvgetidx(lcx, ControlFlow::Straight(ctr), vget);
    let var = vardata(&lcx.data.objs, vget.var);
    let inline = isdisjointidx(&lcx.data.bump[lcx.data.tab],
        &lcx.data.bump[lcx.data.bump[var].tab], &vget.idx);
    emitvarload(lcx, var, i, inline)
}

fn computeshape(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    match objs.get(expr.erase()) {
        ObjectRef::VGET(vget @ &VGET { var, ann, ref idx, .. }) => {
            debug_assert!(objs[ann].op == Obj::TTEN);
            let bump = Access::borrow(&lcx.data.bump);
            let v = vardata(&lcx.data.objs, var);
            let tab = bump[v].tab;
            if ann == lcx.objs[var].ann {
                // scalar load of a vector variable
                let i = emitvgetidx(lcx, ControlFlow::Straight(ctr), vget);
                emitvarloadshape(lcx, v, i, i == INS_FLATIDX)
            } else {
                // vector load
                let target = &bump[tab];
                debug_assert!(!isnestedloopidx(lcx, &bump[lcx.data.tab], target, idx));
                let base = lcx.tmp.end();
                let call = emittabcall(&lcx.data.func, target.func);
                let shape = reserve(&lcx.data.func, objs[ann.cast::<TTEN>()].dim as _);
                vgetidx(&lcx.data, objs, vget, lcx.tmp.align_for());
                if let Some(p) = vgetshape(lcx, ctr, call, target, base.cast_up(), shape).unpack() {
                    let source = &bump[lcx.data.tab];
                    let nprefix = prefixlen(source.axes.len(), target.axes.len(), vget.dim as _);
                    let prefix = idxtransfer(lcx, lcx.data.tab, bump[v].tab, source.axes.len(),
                        nprefix, INS_FLATIDX);
                    lcx.data.func.code.set(p, Ins::MOV(IRT_IDX, prefix));
                }
                lcx.tmp.truncate(base);
                shape
            }
        },
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::BINOP(&BINOP { left, right, .. }) => {
            // TODO: this should really insert an assertion that both shapes indeed are equal.
            let n = match objs[objs[left].ann].op {
                Obj::TPRI => right,
                _ /* TTEN */ => left
            };
            computeshape(lcx, ctr, n)
        },
        ObjectRef::INTR(&INTR { func, ref args, .. }) => {
            let func = Intrinsic::from_u8(func);
            debug_assert!(func.is_broadcast());
            computeshape(lcx, ctr, args[0])
        },
        ObjectRef::LOAD(LOAD { shape, .. }) | ObjectRef::NEW(NEW { shape, .. })
            => emitvalues(lcx, ctr, shape),
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn alloctensordata(
    lcx: &mut Lcx,
    ctr: InsId,
    type_: &TTEN,
    shape: InsId
) -> (
    /* data pointers: */ InsId,
    /* element sizes: */ InsId
) {
    let lower = &*lcx.data;
    let len = emitshapelen(&lower.func, shape, type_.dim as _);
    let ds = decomposition_size(&lcx.objs, type_.elem);
    let ptrs = reserve(&lower.func, ds);
    let esizes = reserve(&lower.func, ds);
    let base = lcx.tmp.end();
    for (i, ty) in decomposition(&lcx.objs, type_.elem, &mut lcx.tmp).iter().enumerate() {
        lower.func.code.set(esizes + i as isize, Ins::KINT(IRT_IDX, ty.size() as _));
        let size = lower.func.code.push(Ins::MUL(IRT_IDX, len, esizes + i as isize));
        lower.func.code.set(ptrs + i as isize, Ins::ALLOC(size, esizes + i as isize, ctr));
    }
    lcx.tmp.truncate(base);
    (ptrs, esizes)
}

struct Collect {
    reduce: Reduce,
    dim: u8,
    shape: InsId,
    esizes: InsId,
    ptrs: InsId
}

fn newcollect(lcx: &mut Lcx, cty: &TTEN, shape: InsId) -> Collect {
    let ds = decomposition_size(&lcx.objs, cty.elem) as u16;
    let reduce = newreducefx(&lcx.data.func, ds);
    let (ptrs, esizes) = alloctensordata(lcx, reduce.loop_.head, cty, shape);
    Collect { reduce, esizes, dim: cty.dim, shape, ptrs }
}

fn closecollect(
    lcx: &mut Lcx,
    collect: Collect,
    value: InsId,
) -> (
    /* out: */ InsId,
    /* result (dominated by out): */ InsId,
    /* ctr instruction: */ Ins,
) {
    let Collect { mut reduce, esizes, dim, shape, ptrs } = collect;
    let func = &lcx.data.func;
    let next = emitreducestore(func, &mut reduce, ptrs, esizes, value, None.into());
    let stores = closereduce(func, &reduce, next);
    let ret = func.code.extend(
        (0..reduce.num as isize).map(|i| Ins::MOVF(Type::PTR, ptrs+i, stores+i)));
    func.code.extend((0..dim as isize).map(|i| Ins::MOV(IRT_IDX, shape+i)));
    (reduce.loop_.out, ret, reduce.start)
}

fn materializecollect(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>, cty: &TTEN) -> InsId {
    let shape = computeshape(lcx, ctr, expr);
    let mut collect = newcollect(lcx, cty, shape);
    let value = emititer(lcx, &mut collect.reduce.loop_, expr);
    let (out, result, start) = closecollect(lcx, collect, value);
    swapctr(&lcx.data.func, ctr, start, out);
    result
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct IdxExpr {
    expr: ObjRef<EXPR>,
    axis: u8,
    span: u8,
    _pad: [u8; 2]
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct IdxStruct {
    idx: IdxExpr,
    value: IndexOption<InsId>,
    oaxis: u8,
    flags: u8
}

impl IdxStruct {
    const SCALAR_VALUE: u8 = 0x1; // set iff `expr` is scalar-valued, must be 0x1.
    const SCALAR_AXIS: u8  = 0x2; // set iff all target axes in [axis, axis+span) are scalar axes
}

// note: this doesn't fill in value
fn vgetidx(lower: &Lower<R, R>, objs: &Objects, vget: &VGET, buf: &mut Bump<IdxStruct>) {
    let base = buf.end();
    let var = vardata(&lower.objs, vget.var);
    let target = &lower.bump[lower.bump[var].tab];
    let mut taxis = prefixlen(lower.bump[lower.tab].axes.len(), target.axes.len(), vget.dim as _);
    let mut span = 0;
    let mut oaxis = 0;
    for &expr in &vget.idx {
        let o = objs[expr.erase()];
        match o.op {
            Obj::SPEC if o.data == SPEC::SLURP => span += 1,
            Obj::FLAT => {
                debug_assert!(span == 0);
                let fidx = &objs[expr.cast::<FLAT>()].idx;
                let mut nil = false;
                for (i, &v) in fidx.iter().enumerate() {
                    if nil && v.is_nil() {
                        debug_assert!(span == 0);
                        let top = buf.end().add_size(-1);
                        buf[top].idx.span += 1;
                        continue
                    }
                    nil = v.is_nil();
                    if (objs[v].op, objs[v].data) == (Obj::SPEC, SPEC::SLURP) {
                        span += 1;
                        continue
                    }
                    buf.push(IdxStruct {
                        idx: IdxExpr {
                            expr: v,
                            axis: (taxis + i) as _,
                            span: span+1,
                            _pad: Default::default()
                        },
                        value: None.into(),
                        oaxis,
                        flags: isscalarann(objs, v.erase()) as _,
                    });
                    span = 0;
                }
                taxis += fidx.len();
                oaxis += 1;
            },
            _ => {
                let is_scalar = isscalarann(objs, expr.erase());
                buf.push(IdxStruct {
                    idx: IdxExpr {
                        expr,
                        axis: taxis as _,
                        span: span+1,
                        _pad: Default::default()
                    },
                    value: None.into(),
                    oaxis,
                    flags: is_scalar as _
                });
                (taxis, span) = (taxis+1, 0);
                if !is_scalar { oaxis += 1 }
            }
        }
    }
    debug_assert!(span == 0);
    let odim = objs[vget.ann.cast::<TTEN>()].dim;
    debug_assert!(oaxis <= odim);
    while oaxis < odim {
        buf.push(IdxStruct {
            idx: IdxExpr {
                expr: ObjRef::NIL.cast(),
                axis: taxis as _,
                span: 1,
                _pad: Default::default()
            },
            value: None.into(),
            oaxis,
            flags: 0
        });
        taxis += 1;
        oaxis += 1;
    }
    debug_assert!(!matches!(target.axes.get(taxis), Some(Axis { rank: Axis::SCALAR, .. })));
    for i in &mut buf[base..] {
        if target.axes[i.idx.axis as usize..(i.idx.axis+i.idx.span) as usize]
            .iter().all(|a| a.rank == Axis::SCALAR)
        {
            i.flags |= IdxStruct::SCALAR_AXIS;
        }
    }
}

fn vgetidxvalue(lcx: &mut Lcx, ctr: &mut InsId, base: BumpRef<IdxStruct>) {
    let first_vsplat = lcx.tmp[base..]
        .iter()
        .find_map(|i| if (i.flags & IdxStruct::SCALAR_AXIS) == 0 && i.idx.expr.is_nil() {
            Some(i.oaxis)
        } else {
            None
        })
        .unwrap_or(!0);
    let end: BumpRef<IdxStruct> = lcx.tmp.end().cast();
    let mut i = base;
    let mut first_vector = true;
    while i < end {
        let expr = lcx.tmp[i].idx.expr;
        if (lcx.tmp[i].flags & IdxStruct::SCALAR_VALUE) == 0 && first_vector {
            first_vector = false;
            if first_vsplat > lcx.tmp[i].oaxis {
                // first group is rectangular, so it only needs to be iterated once.
                // don't emitvalue here, use emititer later instead.
                i = i.add_size(1);
                continue;
            }
        }
        if !expr.is_nil() {
            lcx.tmp[i].value = Some(emitvalue(lcx, ctr, expr)).into();
        }
        i = i.add_size(1);
    }
}

fn pushflatidx(
    objs: &Objects,
    source_dim: usize,
    target_dim: usize,
    explicit: usize,
    idx: &[ObjRef<EXPR>],
    buf: &mut Bump<IdxExpr>
) {
    let prefix = prefixlen(source_dim, target_dim, explicit);
    let mut axis = prefix;
    let mut span = 0;
    let mut nil = false;
    for expr in iterflatidx(objs, idx) {
        if expr.is_nil() {
            span += 1;
            nil = true;
        } else {
            if nil {
                buf.push(IdxExpr {
                    expr: ObjRef::NIL.cast(),
                    axis: axis as _,
                    span: span as _,
                    _pad: Default::default()
                });
                axis += span;
                span = 0;
                nil = false;
            }
            if objs[expr].op == Obj::SPEC && objs[expr].op == SPEC::SLURP {
                span += 1;
            } else {
                buf.push(IdxExpr {
                    expr,
                    axis: axis as _,
                    span: (span+1) as _,
                    _pad: Default::default()
                });
                axis += span+1;
                span = 0;
            }
        }
    }
    debug_assert!(nil || span == 0);
    debug_assert!(axis+span <= target_dim);
    if axis < target_dim {
        buf.push(IdxExpr {
            expr: ObjRef::NIL.cast(),
            axis: axis as _,
            span: (target_dim-axis) as _,
            _pad: Default::default()
        });
    }
}

enum ControlFlow<'a> {
    Straight(&'a mut InsId),
    Loop(&'a mut LoopState)
}

fn emitvgetidx(lcx: &mut Lcx, mut ctr: ControlFlow, vget: &VGET) -> InsId {
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    let var = vardata(&lcx.data.objs, vget.var);
    let tab = bump[var].tab;
    let target = &bump[tab];
    debug_assert!(!isnestedloopidx(lcx, &bump[lcx.data.tab], target, &vget.idx));
    let sdim = bump[lcx.data.tab].axes.len();
    let tdim = target.axes.len();
    let prefix = prefixlen(sdim, tdim, vget.dim as _);
    let mut flat = idxtransfer(lcx, lcx.data.tab, tab, sdim, prefix, INS_FLATIDX);
    if prefix == tdim {
        // nothing to do here (skip emitting the tabcall).
        return flat;
    }
    let call = emittabcall(&lcx.data.func, target.func);
    let base = lcx.tmp.end();
    pushflatidx(objs, sdim, tdim, vget.dim as _, &vget.idx, lcx.tmp.align_for());
    let mut i: BumpRef<IdxExpr> = base.cast_up();
    let end: BumpRef<IdxExpr> = lcx.tmp.end().cast();
    while i < end {
        flat = match lcx.tmp[i] {
            IdxExpr { expr, axis, span, .. } if expr.is_nil() => {
                let ControlFlow::Loop(loop_) = &mut ctr else { unreachable!() };
                emitsplatloop(lcx, loop_, target, flat, call, axis as _, (axis+span) as _)
            },
            IdxExpr { expr, axis, span, .. } => {
                let j = match isscalarann(objs, expr.erase()) {
                    true => {
                        let ctr = match &mut ctr {
                            ControlFlow::Straight(ctr) => ctr,
                            ControlFlow::Loop(loop_) => &mut loop_.head
                        };
                        emitvalue(lcx, ctr, expr)
                    },
                    false => {
                        let ControlFlow::Loop(loop_) = &mut ctr else { unreachable!() };
                        emititer(lcx, loop_, expr)
                    }
                };
                let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _, flat);
                lcx.data.func.code.push(Ins::ADD(IRT_IDX, baseflat, j))
            }
        };
        i = i.add_size(1);
    }
    lcx.tmp.truncate(base);
    flat
}

// compute the shape of the result of a tensor-valued VGET expressions.
// return an instruction placeholder to be filled with the prefix if the shape of the first group
// depends on the prefix index (see eg. tests/vget-vector-splat.t for an example)
fn vgetshape(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    call: InsId,
    target: &Tab,
    base: BumpRef<IdxStruct>,
    shape: InsId
) -> IndexOption<InsId> {
    let objs = Access::borrow(&lcx.objs);
    let mut idx: BumpRef<IdxStruct> = lcx.tmp.end().cast();
    let mut prefix: IndexOption<InsId> = None.into();
    while idx > base {
        let mut tail = idx;
        idx = idx.add_size(-1);
        while idx > base && lcx.tmp[idx].oaxis == lcx.tmp[tail.add_size(-1)].oaxis {
            idx = idx.add_size(-1);
        }
        let mut len: IndexOption<InsId> = None.into();
        while tail > idx {
            tail = tail.add_size(-1);
            // rectangularity should be checked earlier (TODO)
            debug_assert!((lcx.tmp[tail].flags & IdxStruct::SCALAR_VALUE != 0) || prefix.is_none());
            let num = match lcx.tmp[tail] {
                IdxStruct { value, flags, idx: IdxExpr { axis, span, ..}, .. }
                        if (flags & IdxStruct::SCALAR_VALUE) != 0 => {
                    if let Some(p) = prefix.unpack() {
                        let [flat] = areserve(&lcx.data.func);
                        let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _, flat);
                        lcx.data.func.code.set(p, Ins::ADD(IRT_IDX, baseflat, value.unwrap()));
                        prefix = Some(flat).into();
                    }
                    continue
                },
                IdxStruct { value, idx: IdxExpr { expr, .. }, .. } if value.is_some()
                    => extractshape(objs, value.raw, &objs[objs[expr].ann.cast()]),
                IdxStruct { idx: IdxExpr { expr, .. }, .. } if !expr.is_nil()
                    => emitshape(lcx, ctr, expr),
                IdxStruct { flags: IdxStruct::SCALAR_AXIS, idx: IdxExpr { axis, span, .. }, .. } => {
                    let mut size = lcx.data.func.code.push(
                        Ins::RES(IRT_IDX, call, target.axes[axis as usize].ret));
                    for i in 1..span {
                        let s = lcx.data.func.code.push(
                            Ins::RES(IRT_IDX, call, target.axes[(axis+i) as usize].ret));
                        size = lcx.data.func.code.push(Ins::MUL(IRT_IDX, size, s));
                    }
                    size
                },
                IdxStruct { idx: IdxExpr { axis, span, .. }, .. } => {
                    let [mut flat] = areserve(&lcx.data.func);
                    let (start, end) = emitsplatbounds(lcx, target, flat, call,
                        axis as _, (axis+span) as _);
                    let mut num = lcx.data.func.code.push(Ins::SUB(IRT_IDX, end, start));
                    let mut innerloop: Option<(/*init:*/ InsId, /*start:*/ Ins, /*out:*/ InsId)>
                        = None;
                    while tail > idx {
                        tail = tail.add_size(-1);
                        let [nextflat] = areserve(&lcx.data.func);
                        let j = match lcx.tmp[tail] {
                            IdxStruct { flags, value, idx: IdxExpr  { axis, span, ..}, .. }
                                    if (flags & IdxStruct::SCALAR_VALUE) != 0 => {
                                let baseflat = idxftrann(lcx, target, call, axis as _,
                                    (axis+span) as _, nextflat);
                                Ins::ADD(IRT_IDX, baseflat, value.unwrap())
                            },
                            IdxStruct { value, idx: IdxExpr { expr, axis, span, .. }, .. } => {
                                let [init] = areserve(&lcx.data.func);
                                let mut reduce = newreducety(&lcx.data.func, [IRT_IDX], init);
                                let j = match expr.is_nil() {
                                    true => {
                                        let j = emitsplatloop(lcx, &mut reduce.loop_, target,
                                            nextflat, call, axis as _, (axis+span) as _);
                                        Ins::MOV(IRT_IDX, j)
                                    },
                                    false => {
                                        let baseflat = idxftrann(lcx, target, call,
                                            axis as _, (axis+span) as _, nextflat);
                                        let j = emittensorloop(lcx, &mut reduce.loop_,
                                            &objs[objs[expr].ann.cast()], value.unwrap());
                                        Ins::ADD(IRT_IDX, baseflat, j)
                                    }
                                };
                                match innerloop {
                                    Some((inner_init, start, out)) => {
                                        lcx.data.func.code.set(inner_init,
                                            Ins::MOV(IRT_IDX, reduce.value));
                                        lcx.data.func.code.set(replace(&mut reduce.loop_.body, out),
                                            start);
                                    },
                                    None => {
                                        num = lcx.data.func.code.push(
                                            Ins::ADD(IRT_IDX, reduce.value, num));
                                    }
                                }
                                num = closereduce(&lcx.data.func, &reduce, num);
                                innerloop = Some((init, reduce.start, reduce.loop_.out));
                                j
                            },
                        };
                        lcx.data.func.code.set(replace(&mut flat, nextflat), j);
                    }
                    prefix = Some(flat).into();
                    if let Some((init, start, out)) = innerloop {
                        lcx.data.func.code.set(init, Ins::KINT(IRT_IDX, 0));
                        lcx.data.func.code.set(replace(ctr, out), start);
                    }
                    num
                }
            };
            len = Some(match len.unpack() {
                Some(len) => lcx.data.func.code.push(Ins::MUL(IRT_IDX, len, num)),
                None => num
            }).into();
        }
        let len = match len.unpack() {
            Some(len) => Ins::MOV(IRT_IDX, len),
            None => Ins::KINT(IRT_IDX, 1)
        };
        lcx.data.func.code.set(shape + lcx.tmp[idx].oaxis as isize, len);
    }
    prefix
}

struct VGetState {
    value: InsId,  // value collected in the rectangular part
    flat: InsId,   // **placeholder** for flat index in the current loop
    innerloop: Option<(/*start:*/Ins, /*out:*/InsId)>, // current inner loop
}

fn vgetnonrect(
    lcx: &mut Lcx,
    vgs: &mut VGetState,
    target: &Tab,
    mut elem: ObjRef,
    call: InsId,
    var: ObjRef<VAR>
) {
    let objs = Access::borrow(&lcx.objs);
    let ann = objs[var].ann;
    // we only go here if there is a non-rectangular tail part:
    debug_assert!(ann != elem);
    // compute non-rectangular loop nest in lcx.tmp
    let base = lcx.tmp.end();
    let nest = lcx.tmp.align_for::<ObjRef>();
    while elem != ann {
        debug_assert!(objs[elem].op == Obj::TTEN);
        nest.push(elem);
        elem = objs[elem.cast::<TTEN>()].elem;
    }
    // work through loop nest in reverse order (inside out)
    let mut axis = target.axes.len();
    while lcx.tmp.end().cast::<ObjRef>() > base.cast_up() {
        let ty: &TTEN = &objs[lcx.tmp.pop().unwrap()];
        let dim = ty.dim as usize;
        axis -= dim;
        let [flat] = areserve(&lcx.data.func);
        let shape = reserve(&lcx.data.func, dim);
        let mut start = flat;
        for i in 0..dim {
            let s = shape + i as isize;
            match &target.axes[axis+i] {
                &Axis { rank: Axis::SCALAR, ret, .. } => {
                    lcx.data.func.code.set(s, Ins::RES(IRT_IDX, call, ret));
                    start = lcx.data.func.code.push(Ins::MUL(IRT_IDX, start, s));
                },
                &Axis { /* VECTOR */ ret, .. } => {
                    debug_assert!(i == 0);
                    let idxsize = lcx.data.func.code.push(
                        Ins::KINT(IRT_IDX, IRT_IDX.size() as _));
                    let f = lcx.data.func.code.push(Ins::RES(Type::PTR, call, ret));
                    let ofs = lcx.data.func.code.push(Ins::MUL(IRT_IDX, start, idxsize));
                    let fstart = lcx.data.func.code.push(Ins::ADDP(f, ofs));
                    let fstart1 = lcx.data.func.code.push(Ins::ADDP(fstart, idxsize));
                    start = lcx.data.func.code.push(Ins::LOAD(IRT_IDX, fstart));
                    let end = lcx.data.func.code.push(Ins::LOAD(IRT_IDX, fstart1));
                    lcx.data.func.code.set(s, Ins::SUB(IRT_IDX, end, start));
                }
            }
        }
        let len = emitshapelen(&lcx.data.func, shape, dim);
        let end = lcx.data.func.code.push(Ins::ADD(IRT_IDX, start, len));
        let mut col = newcollect(lcx, ty, shape);
        let j = emitrangeloop(&lcx.data.func, &mut col.reduce.loop_, IRT_IDX, start, end);
        lcx.data.func.code.set(replace(&mut vgs.flat, flat), Ins::MOV(IRT_IDX, j));
        if let Some((start, out)) = vgs.innerloop {
            lcx.data.func.code.set(replace(&mut col.reduce.loop_.body, out), start);
        }
        let (out, result, start) = closecollect(lcx, col, vgs.value);
        vgs.innerloop = Some((start, out));
        vgs.value = result;
    }
    lcx.tmp.truncate(base);
}

fn vgetrect(
    lcx: &mut Lcx,
    vgs: &mut VGetState,
    ctr: InsId,
    target: &Tab,
    cty: &TTEN,
    call: InsId,
    eds: usize,
    idx_base: BumpRef<IdxStruct>,
    out: InsId
) {
    let objs = Access::borrow(&lcx.objs);
    let idx_end: BumpRef<IdxStruct> = lcx.tmp.end().cast();
    let shape = out + eds as isize;
    let (data, esizes) = alloctensordata(lcx, ctr, cty, shape);
    let mut idx = idx_end;
    let mut inner: Option<(/*init:*/ InsId, /*value:*/ InsId)> = None;
    while idx > idx_base {
        idx = idx.add_size(-1);
        let [nextflat] = areserve(&lcx.data.func);
        let j = match lcx.tmp[idx] {
            IdxStruct { flags, value, idx: IdxExpr { axis, span, .. }, .. }
                    if (flags & IdxStruct::SCALAR_VALUE) != 0 => {
                let baseflat = idxftrann(lcx, target, call, axis as _,
                    (axis+span) as _, nextflat);
                Ins::ADD(IRT_IDX, baseflat, value.unwrap())
            },
            IdxStruct { value, idx: IdxExpr { expr, mut span, mut axis, .. }, .. } => {
                if expr.is_nil() {
                    while idx > idx_base && lcx.tmp[idx.add_size(-1)].idx.expr.is_nil() {
                        idx = idx.add_size(-1);
                        span += lcx.tmp[idx].idx.span;
                        axis = lcx.tmp[idx].idx.axis;
                    }
                }
                let l_phi = lcx.data.func.phis.push(Phi::new(IRT_IDX));
                lcx.data.func.phis.extend(repeat_n(Phi::new(Type::FX), eds));
                let r_phi = lcx.data.func.phis.push(Phi::new(IRT_IDX));
                lcx.data.func.phis.extend(repeat_n(Phi::new(Type::FX), eds));
                let init = reserve(&lcx.data.func, 1+eds);
                let mut reduce = newreduce(&lcx.data.func, l_phi, r_phi, init, (1+eds) as _);
                let j = match expr.is_nil() {
                    true => {
                        let j = emitsplatloop(lcx, &mut reduce.loop_, target, nextflat, call,
                            axis as _, (axis+span) as _);
                        Ins::MOV(IRT_IDX, j)
                    },
                    false => {
                        let baseflat = idxftrann(lcx, target, call,
                            axis as _, (axis+span) as _, nextflat);
                        let j = match value.unpack() {
                            Some(value) => emittensorloop(lcx, &mut reduce.loop_,
                                &objs[objs[expr].ann.cast()], value),
                            None => emititer(lcx, &mut reduce.loop_, expr),
                        };
                        Ins::ADD(IRT_IDX, baseflat, j)
                    }
                };
                if let Some((start, out)) = vgs.innerloop {
                    lcx.data.func.code.set(replace(&mut reduce.loop_.body, out), start);
                }
                let next = match inner {
                    Some((init, value)) => {
                        lcx.data.func.code.set(init, Ins::MOV(IRT_IDX, reduce.value));
                        for i in 1..(1+eds) as isize {
                            lcx.data.func.code.set(init+i, Ins::MOV(Type::FX, reduce.value+i));
                        }
                        value
                    },
                    None => {
                        let stores = emitmultistore(&lcx.data.func, data, esizes, reduce.value,
                            vgs.value, eds);
                        let one = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
                        let next = lcx.data.func.code.push(Ins::ADD(IRT_IDX, reduce.value, one));
                        lcx.data.func.code.extend(
                            (0..eds as isize)
                            .map(|i| Ins::MOVF(Type::FX, reduce.value+1+i, stores+i))
                        );
                        next
                    }
                };
                let result = closereduce(&lcx.data.func, &reduce, next);
                inner = Some((init, result));
                vgs.innerloop = Some((reduce.start, reduce.loop_.out));
                j
            },
        };
        lcx.data.func.code.set(replace(&mut vgs.flat, nextflat), j);
    }
    let stores = match inner {
        Some((init, result)) => {
            lcx.data.func.code.set(init, Ins::KINT(IRT_IDX, 0));
            for i in 1..(1+eds) as isize {
                lcx.data.func.code.set(init+i, Ins::NOP(Type::FX));
            }
            result
        },
        None => {
            // no inner loop. this is a "degenerate" case, like A[(i,j)].
            lcx.data.func.code.extend((0..eds as isize) .map(|i| Ins::STORE(data+i, vgs.value+i)))
        }
    };
    for i in 0..eds as isize {
        lcx.data.func.code.set(out+i, Ins::MOVF(Type::PTR, data+i, stores+i));
    }
}

// TODO: this does not verify that the index is actually rectangular.
// it should be checked (preferably earlier, after type inference) and an error should be raised.
// this will return garbage values if the expression selects a non-rectangular array.
fn materializevget(lcx: &mut Lcx, ctr: &mut InsId, vget: &VGET) -> InsId {
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    let var = vardata(&lcx.data.objs, vget.var);
    let target = &bump[bump[var].tab];
    let tcall = emittabcall(&lcx.data.func, target.func);
    let cty = &objs[vget.ann.cast::<TTEN>()];
    let eds = decomposition_size(objs, cty.elem);
    let source = &bump[lcx.data.tab];
    let nprefix = prefixlen(source.axes.len(), target.axes.len(), vget.dim as _);
    let prefix = idxtransfer(lcx, lcx.data.tab, bump[var].tab, source.axes.len(), nprefix, INS_FLATIDX);
    let base = lcx.tmp.end();
    vgetidx(&lcx.data, &lcx.objs, vget, lcx.tmp.align_for());
    vgetidxvalue(lcx, ctr, base.cast_up());
    let ret = reserve(&lcx.data.func, eds + cty.dim as usize);
    if let Some(p) = vgetshape(lcx, ctr, tcall, target, base.cast_up(), ret + eds as isize).unpack() {
        lcx.data.func.code.set(p, Ins::MOV(IRT_IDX, prefix));
    }
    let [flat] = areserve(&lcx.data.func);
    let inline = isdisjointidx(&bump[lcx.data.tab], target, &vget.idx);
    let value = emitvarload(lcx, var, flat, inline);
    let mut vgs = VGetState { flat, value, innerloop: None };
    if cty.elem != objs[vget.var].ann {
        vgetnonrect(lcx, &mut vgs, target, cty.elem, tcall, vget.var);
    }
    vgetrect(lcx, &mut vgs, *ctr, target, cty, tcall, eds, base.cast_up(), ret);
    lcx.tmp.truncate(base);
    lcx.data.func.code.set(vgs.flat, Ins::MOV(IRT_IDX, prefix));
    let (start, out) = vgs.innerloop.unwrap();
    lcx.data.func.code.set(replace(ctr, out), start);
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
    if !sametab(&lcx.objs, &bump[lower.tab], &bump[model.tab]) { return None.into() }
    if !lcx.objs.allequal(cast_args(&vget.idx), cast_args(&lcx.objs[vset.obj].idx)) {
        return None.into();
    }
    let call = emitcallvm1(lower, INS_FLATIDX, model.base + Mod::SUB_VALUE);
    let base = lower.func.code.end();
    // scalar load of vector variable is handled separately:
    debug_assert!(vget.ann != lcx.objs[vget.var].ann);
    for (i, &ty) in decomposition__old(&lcx.objs, lcx.objs[vset.obj].value.erase(), &mut lower.tmp_ty)
        .iter()
        .enumerate()
    {
        lower.func.code.push(Ins::RES(ty, call, vset.ret + i as isize));
    }
    Some(base).into()
}

fn emitnew(lcx: &mut Lcx, ctr: &mut InsId, new: &NEW) -> InsId {
    debug_assert!(lcx.objs[new.ann].op == Obj::TTEN);
    let shape = emitvalues(lcx, ctr, &new.shape);
    let len = emitshapelen(&lcx.data.func, shape, new.shape.len());
    let base = lcx.tmp.end();
    let deco = decomposition(&lcx.objs, lcx.objs[new.ann.cast::<TTEN>()].elem, &mut lcx.tmp);
    let ds = deco.len();
    let out = reserve(&lcx.data.func, deco.len() + new.shape.len());
    for (i,&ty) in deco.iter().enumerate() {
        let size = lcx.data.func.code.push(Ins::KINT(IRT_IDX, ty.size() as _));
        let num = lcx.data.func.code.push(Ins::MUL(IRT_IDX, len, size));
        lcx.data.func.code.set(out + i as isize, Ins::ALLOC(num, size, *ctr));
    }
    lcx.tmp.truncate(base);
    for i in 0..0+new.shape.len() {
        lcx.data.func.code.set(out + (ds+i) as isize, Ins::MOV(IRT_IDX, shape + i as isize));
    }
    out
}

// in pseudocode:
//   (dim1, ..., dimN) = shape(expr)
//   buf1 = alloc(dim1 * ... * dimN)
//   ...
//   bufN = alloc(dim1 * ... * dimN)
//   num = 0
//   for i1 in 0..dim1:
//     ...
//       for iN in 0..dimN:
//         if next(expr):
//           buf1[num] = i1
//           ...
//           bufN[num] = iN
//           num = num+1
//   return (buf1, ..., bufN, num)
// (TODO: this only implements the 1D case.)
fn emitwhich(lcx: &mut Lcx, ctr: &mut InsId, cty: &TTEN, expr: ObjRef<EXPR>) -> InsId {
    debug_assert!(cty.dim == 1);
    debug_assert!(lcx.objs[lcx.objs[expr].ann].op == Obj::TTEN);
    let edim = lcx.objs[lcx.objs[expr].ann.cast::<TTEN>()].dim as usize;
    debug_assert!(edim == 1);
    // ND case: debug_assert!(decomposition_size(&lcx.objs, cty.elem) == edim);
    let shape = computeshape(lcx, ctr, expr);
    let lower = &mut *lcx.data;
    let idxsize = lower.func.code.push(Ins::KINT(IRT_IDX, IRT_IDX.size() as _));
    let size = lower.func.code.push(Ins::MUL(IRT_IDX, shape, idxsize));
    let buf = lower.func.code.push(Ins::ALLOC(size, idxsize, *ctr));
    let bufphi = lower.func.phis.push(Phi::new(Type::PTR));
    let nop = lower.func.code.push(Ins::NOP(Type::FX));
    let zero = lower.func.code.push(Ins::KINT(IRT_IDX, 0)); // must be here for num init
    let mut reduce = newreducety(&lower.func, [Type::FX, IRT_IDX], nop);
    let head = reserve(&lower.func, 1);
    lower.func.code.set(reduce.loop_.head, Ins::JMP(buf, head, bufphi));
    reduce.loop_.head = head;
    let loop_store = reduce.value;
    let loop_num = reduce.value+1;
    let loop_buf = lower.func.code.push(Ins::PHI(Type::PTR, reduce.loop_.body, bufphi));
    let i = emitrangeloop(&lower.func, &mut reduce.loop_, IRT_IDX, zero, shape);
    let v = emititer(lcx, &mut reduce.loop_, expr);
    let lower = &mut *lcx.data;
    let loop_nextstore = lower.func.code.push(Ins::STORE(loop_buf, i));
    let loop_nextbuf = lower.func.code.push(Ins::ADDP(loop_buf, idxsize));
    let one = lower.func.code.push(Ins::KINT(IRT_IDX, 1));
    let loop_nextnum = lower.func.code.push(Ins::ADD(IRT_IDX, loop_num, one));
    let merge = reserve(&lower.func, 1);
    let next_storephi = lower.func.phis.push(Phi::new(Type::FX));
    let next_numphi = lower.func.phis.push(Phi::new(IRT_IDX));
    let next_bufphi = lower.func.phis.push(Phi::new(Type::PTR));
    let store_branch = lower.func.code.push(Ins::JMP(loop_nextstore, merge, next_storephi));
    let store_branch = lower.func.code.push(Ins::JMP(loop_nextnum, store_branch, next_numphi));
    let store_branch = lower.func.code.push(Ins::JMP(loop_nextbuf, store_branch, next_bufphi));
    let skip_branch = lower.func.code.push(Ins::JMP(loop_store, merge, next_storephi));
    let skip_branch = lower.func.code.push(Ins::JMP(loop_num, skip_branch, next_numphi));
    let skip_branch = lower.func.code.push(Ins::JMP(loop_buf, skip_branch, next_bufphi));
    lower.func.code.set(reduce.loop_.body, Ins::IF(v, store_branch, skip_branch));
    reduce.loop_.body = merge;
    let next = lower.func.code.push(Ins::PHI(Type::FX, merge, next_storephi));
    lower.func.code.push(Ins::PHI(IRT_IDX, merge, next_numphi)); // next num, must be here.
    let next_buf = lower.func.code.push(Ins::PHI(Type::PTR, merge, next_bufphi));
    let tail = reserve(&lower.func, 1);
    lower.func.code.set(reduce.loop_.tail, Ins::JMP(next_buf, tail, bufphi));
    reduce.loop_.tail = tail;
    let results = closereduce(&lower.func, &reduce, next);
    swapctr(&lower.func, ctr, reduce.start, reduce.loop_.out);
    let out = lower.func.code.push(Ins::MOVF(Type::PTR, buf, results));
    lower.func.code.push(Ins::MOV(IRT_IDX, results+1)); // num, must be out+1
    out
}

fn computevalue(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    let ann = objs[expr].ann;
    match objs.get(expr.erase()) {
        ObjectRef::GET(o) => emitget(lcx, ctr, o),
        ObjectRef::CALLX(_) => emitcallx(lcx, ctr, expr.cast()),
        ObjectRef::CAT(cat) => emitcat(lcx, ctr, cat),
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
                        let source = lcx.data.bump[lcx.data.tab].axes.len();
                        axisidx(lcx, lcx.data.tab, source, (axis+1) as _, INS_FLATIDX)
                    },
                    ObjectRef::LEN(&LEN { axis, value, .. }) =>
                        emitshape(lcx, ctr, value) + axis as isize,
                    ObjectRef::VGET(o) => emitvget1(lcx, ctr, o),
                    ObjectRef::IDX(_) => todo!(),
                    ObjectRef::BINOP(&BINOP { binop, left, right, .. }) => {
                        let lhs = emitvalue(lcx, ctr, left);
                        let rhs = emitvalue(lcx, ctr, right);
                        let pri = Primitive::from_u8(objs[objs[left].ann.cast::<TPRI>()].ty);
                        emitscalarbinop(lcx, ctr, BinOp::from_u8(binop), pri, lhs, rhs)
                    },
                    ObjectRef::INTR(&INTR { func, ref args, .. }) =>
                        scalarintrinsic(lcx, ctr, Intrinsic::from_u8(func), args, ty),
                    ObjectRef::LOAD(&LOAD { ann, addr, ref shape, .. }) => {
                        debug_assert!(shape.is_empty());
                        debug_assert!(lcx.objs[ann].op == Obj::TPRI);
                        let addr = emitvalue(lcx, ctr, addr);
                        lcx.data.func.code.push(Ins::LOAD(ty, addr))
                    },
                    ObjectRef::FREF(_) => todo!(),
                    ObjectRef::CALL(_) => todo!(),
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
                if let ObjectRef::NEW(new) = o {
                    return emitnew(lcx, ctr, new);
                }
                if let ObjectRef::INTR(&INTR { func, ref args, .. }) = o {
                    if func == Intrinsic::WHICH as _ {
                        return emitwhich(lcx, ctr, cty, args[0]);
                    }
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
                    // else: collect
                    return materializevget(lcx, ctr, vget);
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
        ObjectRef::VGET(vget @ &VGET { ann, var, ref idx, .. }) => {
            debug_assert!(lcx.objs[ann].op == Obj::TTEN);
            let i = emitvgetidx(lcx, ControlFlow::Loop(loop_), vget);
            let v = vardata(&lcx.data.objs, var);
            let inline = isdisjointidx(&lcx.data.bump[lcx.data.tab],
                &lcx.data.bump[lcx.data.bump[v].tab], idx);
            let mut value = emitvarload(lcx, v, i, inline);
            if ann == lcx.objs[var].ann {
                let objs = Access::borrow(&lcx.objs);
                value = emittensorloop(lcx, loop_, &objs[ann.cast()], value);
            }
            value
        },
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::BINOP(&BINOP { ann, binop, left, right, .. }) => {
            debug_assert!(lcx.objs[ann].op == Obj::TTEN);
            broadcastbinop(lcx, loop_, BinOp::from_u8(binop), lcx.objs[ann.cast::<TTEN>()].elem,
                left, right)
        },
        ObjectRef::INTR(&INTR { ann, func, ref args, .. }) => {
            debug_assert!(lcx.objs[ann].op == Obj::TTEN);
            let func = Intrinsic::from_u8(func);
            if func.is_broadcast() {
                broadcastintrinsic(lcx, loop_, func, args, lcx.objs[ann.cast::<TTEN>()].elem)
            } else {
                // should go through emitvalue + iterate array.
                unreachable!()
            }
        },
        ObjectRef::LOAD(&LOAD { ann, addr, shape: ref dims, .. }) => {
            debug_assert!(objs[ann].op == Obj::TTEN);
            debug_assert!(objs[objs[ann.cast::<TTEN>()].elem].op == Obj::TPRI);
            let addr = emitvalue(lcx, &mut loop_.head, addr);
            let shape = emitvalues(lcx, &mut loop_.head, dims);
            emittensordataloop(lcx, loop_, &objs[ann.cast()], addr, shape)
        },
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn emitvalue(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    // this is saved here even if it only has one reference, because for non-iterable objects
    // the value may be used multiple times per reference, eg. when a caller does
    // emitshape+emititer
    if let Some(&ins) = lcx.data.expr.get(&expr) {
        return ins;
    }
    let ins = computevalue(lcx, ctr, expr);
    lcx.data.expr.insert_unique_unchecked(expr, ins);
    ins
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
    // XXX: the isiterable condition is here because all callers that want the shape will
    // eventually want to iterate as well. if the object is non-iterable then iteration requires
    // materializing the value anyway.
    // a better way to do this would be eg. emit both the shape and iterator at the same time, but
    // that requires careful handling of the control flow
    if lcx.objs[expr].mark == EXPR_ONE && isiterable(lcx, expr) {
        computeshape(lcx, ctr, expr)
    } else {
        let value = emitvalue(lcx, ctr, expr);
        let ty = &lcx.objs[lcx.objs[expr].ann.cast()];
        extractshape(&lcx.objs, value, ty)
    }
}

fn isiterable(lcx: &Lcx, expr: ObjRef<EXPR>) -> bool {
    let obj = lcx.objs[expr.erase()];
    match obj.op {
        Obj::INTR => Intrinsic::from_u8(obj.data).is_broadcast(),
        Obj::CAT  => false,
        Obj::VGET => {
            let vget: &VGET = &lcx.objs[expr.cast()];
            let v = vardata(&lcx.data.objs, vget.var);
            !isnestedloopidx(lcx, &lcx.data.bump[lcx.data.tab],
                &lcx.data.bump[lcx.data.bump[v].tab], &vget.idx)
        },
        _ => true
    }
}

fn emititer(lcx: &mut Lcx, loop_: &mut LoopState, expr: ObjRef<EXPR>) -> InsId {
    match lcx.objs[expr].mark {
        EXPR_ONE if isiterable(lcx, expr) => itervalue(lcx, loop_, expr),
        _ => {
            let objs = Access::borrow(&lcx.objs);
            debug_assert!(objs[objs[expr].ann].op == Obj::TTEN);
            let value = emitvalue(lcx, &mut loop_.head, expr);
            emittensorloop(lcx, loop_, &objs[objs[expr].ann.cast()], value)
        }
    }
}

fn emitbroadcast(lcx: &mut Lcx, loop_: &mut LoopState, expr: ObjRef<EXPR>) -> InsId {
    match lcx.objs[lcx.objs[expr].ann].op {
        Obj::TPRI => emitvalue(lcx, &mut loop_.head, expr),
        _ => emititer(lcx, loop_, expr)
    }
}

fn emitvgetcheck(lcx: &mut Lcx, ctr: &mut InsId, vget: &VGET, fail: InsId) {
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    let var = vardata(&lcx.data.objs, vget.var);
    let tab = bump[var].tab;
    let target = &bump[tab];
    let sdim = bump[lcx.data.tab].axes.len();
    let tdim = target.axes.len();
    let prefix = prefixlen(sdim, tdim, vget.dim as _);
    let mut flat = idxtransfer(lcx, lcx.data.tab, tab, sdim, prefix, INS_FLATIDX);
    let call = emittabcall(&lcx.data.func, target.func);
    let base = lcx.tmp.end();
    pushflatidx(objs, sdim, tdim, vget.dim as _, &vget.idx, lcx.tmp.align_for());
    let mut i: BumpRef<IdxExpr> = base.cast_up();
    let end: BumpRef<IdxExpr> = lcx.tmp.end().cast();
    let mut loop_: Option<(
        /*current inner loop:*/ LoopState,
        /*inner loop body start:*/ InsId,
        /*inner loop tail start:*/ InsId,
        /*outer loop head start:*/ InsId,
        /*outer loop out:*/ InsId
    )> = None;
    while i < end {
        flat = match lcx.tmp[i] {
            IdxExpr { expr, axis, span, .. } if isscalarann(objs, expr.erase()) => {
                let j = emitvalue(lcx, ctr, expr);
                let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _, flat);
                lcx.data.func.code.push(Ins::ADD(IRT_IDX, baseflat, j))
            },
            IdxExpr { expr, axis, span, .. } => {
                let (newloop, outermost) = match &mut loop_ {
                    Some((state, body, tail, _, _)) => {
                        lcx.data.func.code.set(state.head, Ins::GOTO(*body));
                        lcx.data.func.code.set(state.tail, Ins::GOTO(*body));
                        state.head = state.body;
                        state.out = *tail;
                        [state.body, state.tail] = areserve(&lcx.data.func);
                        *body = state.body;
                        *tail = state.tail;
                        (state, false)
                    },
                    None => {
                        let [head, tail, body, out] = areserve(&lcx.data.func);
                        (&mut loop_.insert((LoopState { head, tail, body, out }, body, tail, head, out)).0,
                            true)
                    }
                };
                match expr.is_nil() {
                    true => emitsplatloop(lcx, newloop, target, flat, call, axis as _,
                        (axis+span) as _),
                    false => {
                        let j = match outermost {
                            true => emititer(lcx, newloop, expr),
                            false => {
                                let value = emitvalue(lcx, ctr, expr);
                                emittensorloop(lcx, newloop, &objs[objs[expr].ann.cast()], value)
                            }
                        };
                        let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _, flat);
                        lcx.data.func.code.push(Ins::ADD(IRT_IDX, baseflat, j))
                    }
                }
            }
        };
        i = i.add_size(1);
    }
    let inline = isdisjointidx(&bump[lcx.data.tab], &bump[bump[var].tab], &vget.idx);
    match loop_ {
        Some((mut state, body, tail, outer_head, outer_out)) => {
            emitvarcheck(lcx, &mut state.body, var, flat, inline, fail);
            lcx.data.func.code.set(state.head, Ins::GOTO(body));
            lcx.data.func.code.set(state.tail, Ins::GOTO(body));
            lcx.data.func.code.set(state.body, Ins::GOTO(tail));
            lcx.data.func.code.set(replace(ctr, outer_out), Ins::GOTO(outer_head));
        },
        None => emitvarcheck(lcx, ctr, var, flat, inline, fail)
    }
}

fn emitcheck(lcx: &mut Lcx, ctr: &mut InsId, expr: ObjRef, fail: InsId) {
    let objs = Access::borrow(&lcx.objs);
    let raw = objs.get_raw(expr.erase());
    for i in objs[expr.erase()].ref_params() {
        // only recurse into exprs, other objects are in their own chunks.
        let o: ObjRef = zerocopy::transmute!(raw[i+1]);
        if Operator::is_expr_raw(objs[o].op) {
            emitcheck(lcx, ctr, o, fail);
        }
    }
    if let ObjectRef::VGET(vget) = objs.get(expr.erase()) {
        emitvgetcheck(lcx, ctr, vget, fail);
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
    let mut ctr = INS_ENTRY;
    let mut len: IndexOption<InsId> = None.into();
    let bump = Access::borrow(&lcx.data.bump);
    let tab = &bump[tab];
    let zero = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    let ret = lcx.data.func.code.push(Ins::RET());
    let mut fail = lcx.data.func.code.push(Ins::JMP(zero, ret, 0.into()));
    // emit zeroing code for the case when any dimension fails to compute.
    // note that lookup tables have size 1 here so that one-past-last-index computations
    // return zero.
    for &Axis { rank, ret, .. } in &tab.axes {
        match rank {
            Axis::SCALAR => {
                fail = lcx.data.func.code.push(Ins::JMP(zero, fail, ret));
            },
            _ /* VECTOR */ => {
                let size = lcx.data.func.code.push(Ins::KINT(IRT_IDX, IRT_IDX.size() as _));
                let ptr = lcx.data.func.code.push(Ins::ALLOC(size, size, ctr));
                let store = lcx.data.func.code.push(Ins::STORE(ptr, zero));
                let ptr = lcx.data.func.code.push(Ins::MOVF(Type::PTR, ptr, store));
                fail = lcx.data.func.code.push(Ins::JMP(ptr, fail, ret));
                fail = lcx.data.func.code.push(Ins::JMP(ptr, fail, ret+1));
            }
        };
    }
    // emit checks for all dimensions, zero everything if any fails.
    let mut nils = 0;
    for &Axis { size, .. } in &tab.axes {
        if size.is_nil() {
            nils += 1;
        } else {
            emitcheck(lcx, &mut ctr, size.erase(), fail);
        }
    }
    let mut nils = reserve(&lcx.data.func, nils);
    // emit the actual dimensions.
    for (i, &Axis { rank, ret, size, .. }) in tab.axes.iter().enumerate() {
        match rank {
            Axis::SCALAR => {
                let n = match size.is_nil() {
                    true => {
                        // next vector axis will patch this
                        let n = nils;
                        nils += 1;
                        n
                    },
                    false => emitvalue(lcx, &mut ctr, size)
                };
                let [next] = areserve(&lcx.data.func);
                swapctr(&lcx.data.func, &mut ctr, Ins::JMP(n, next, ret), next);
                len = Some(match len.unpack() {
                    Some(len) => lcx.data.func.code.push(Ins::MUL(IRT_IDX, len, n)),
                    None      => n
                }).into();
            },
            _ /* VECTOR */ => {
                // pseudocode:
                //   F = alloc(len+1)
                //   F[0] = 0
                //   cursor = 0
                //   for i in 0..len:
                //     cursor = cursor + value[i]
                //     F[i+1] = cursor
                //   B = alloc(cursor)
                //   start = 0
                //   for i in 1..=len:
                //     end = F[i]
                //     for j in start..end:
                //       B[j] = i
                //     start = end
                // TODO: this only works when the vector axis is the first axis (not counting nil
                // axes). the general case needs an additional loop to broadcast the F table.
                // TODO: use an IR function for the second loop, so that it doesn't need to be
                // copied for every table that uses it, but can be inlined when it's only used in
                // one table etc.
                let xlen: InsId = zerocopy::transmute!(len);
                debug_assert!(xlen != InsId::INVALID.into()); // first axis cannot be vector.
                let dim = lcx.objs[lcx.objs[size].ann.cast::<TTEN>()].dim as usize;
                if dim != i { /* not first axis */ todo!() }
                let shape = emitshape(lcx, &mut ctr, size);
                for j in 0..dim as isize {
                    lcx.data.func.code.set((nils - dim as isize) + j, Ins::MOV(IRT_IDX, shape + j));
                }
                let idxsize = lcx.data.func.code.push(Ins::KINT(IRT_IDX, IRT_IDX.size() as _));
                // emit F loop
                let (f, n) = {
                    let one = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
                    let flen = lcx.data.func.code.push(Ins::ADD(IRT_IDX, xlen, one));
                    let fbytes = lcx.data.func.code.push(Ins::MUL(IRT_IDX, flen, idxsize));
                    let alloc = lcx.data.func.code.push(Ins::ALLOC(fbytes, idxsize, ctr));
                    let init = lcx.data.func.code.push(Ins::STORE(alloc, zero));
                    lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0)); // cursor init, must be here
                    let mut reduce = newreducety(&lcx.data.func, [Type::FX, IRT_IDX], init);
                    let p_phi = lcx.data.func.phis.push(Phi::new(Type::PTR));
                    let [head] = areserve(&lcx.data.func);
                    lcx.data.func.code.set(reduce.loop_.head, Ins::JMP(alloc, head, p_phi));
                    reduce.loop_.head = head;
                    let v = emititer(lcx, &mut reduce.loop_, size);
                    let ptr = lcx.data.func.code.push(Ins::PHI(Type::PTR, reduce.loop_.body, p_phi));
                    let [next_store, next_cursor] = areserve(&lcx.data.func);
                    lcx.data.func.code.set(next_cursor, Ins::ADD(IRT_IDX, reduce.value+1, v));
                    let next_ptr = lcx.data.func.code.push(Ins::ADDP(ptr, idxsize));
                    let store = lcx.data.func.code.push(Ins::STORE(next_ptr, next_cursor));
                    lcx.data.func.code.set(next_store, Ins::MOVF(Type::FX, reduce.value, store));
                    let [tail] = areserve(&lcx.data.func);
                    lcx.data.func.code.set(reduce.loop_.tail, Ins::JMP(next_ptr, tail, p_phi));
                    reduce.loop_.tail = tail;
                    let effect = closereduce(&lcx.data.func, &reduce, next_store);
                    swapctr(&lcx.data.func, &mut ctr, reduce.start, reduce.loop_.out);
                    let f = lcx.data.func.code.push(Ins::MOVF(Type::PTR, alloc, effect));
                    (f, effect+1)
                };
                // emit B loop
                let b = {
                    // skip first element of f (zero)
                    let f = lcx.data.func.code.push(Ins::ADDP(f, idxsize));
                    let bbytes = lcx.data.func.code.push(Ins::MUL(IRT_IDX, n, idxsize));
                    let alloc = lcx.data.func.code.push(Ins::ALLOC(bbytes, idxsize, ctr));
                    // alloc must become a phi here to prevent the scheduler from sinking it inside
                    // the loop (TODO: actually this is true for the above loop, too)
                    let mut reduce = newreducety(&lcx.data.func, [Type::PTR], alloc);
                    let start_phi = lcx.data.func.phis.push(Phi::new(IRT_IDX));
                    let [head] = areserve(&lcx.data.func);
                    lcx.data.func.code.set(reduce.loop_.head, Ins::JMP(zero, head, start_phi));
                    reduce.loop_.head = head;
                    let i = emitrangeloop(&lcx.data.func, &mut reduce.loop_, IRT_IDX, zero, xlen);
                    let fi = emitarrayptr(&lcx.data.func, f, i, IRT_IDX);
                    let end = lcx.data.func.code.push(Ins::LOAD(IRT_IDX, fi));
                    let start = lcx.data.func.code.push(
                        Ins::PHI(IRT_IDX, reduce.loop_.body, start_phi));
                    let mut inner = newreducety(&lcx.data.func, [Type::PTR], reduce.value);
                    let j = emitrangeloop(&lcx.data.func, &mut inner.loop_, IRT_IDX, start, end);
                    let bj = emitarrayptr(&lcx.data.func, inner.value, j, IRT_IDX);
                    let store = lcx.data.func.code.push(Ins::STORE(bj, i));
                    let next = lcx.data.func.code.push(Ins::MOVF(Type::PTR, inner.value, store));
                    let ptr = closereduce(&lcx.data.func, &inner, next);
                    swapctr(&lcx.data.func, &mut reduce.loop_.body, inner.start, inner.loop_.out);
                    let [tail] = areserve(&lcx.data.func);
                    lcx.data.func.code.set(reduce.loop_.tail, Ins::JMP(end, tail, start_phi));
                    reduce.loop_.tail = tail;
                    let result = closereduce(&lcx.data.func, &reduce, ptr);
                    swapctr(&lcx.data.func, &mut ctr, reduce.start, reduce.loop_.out);
                    result
                };
                let [next] = areserve(&lcx.data.func);
                let jump = lcx.data.func.code.push(Ins::JMP(f, next, ret));
                swapctr(&lcx.data.func, &mut ctr, Ins::JMP(b, jump, ret+1), next);
                len = Some(n).into();
            }
        };
    }
    let len = len.unpack().unwrap_or(zero);
    lcx.data.func.code.set(ctr, Ins::JMP(len, ret, 0.into()));
}

/* ---- Initializers -------------------------------------------------------- */

fn emitcinit(lcx: &mut Lcx, tab: BumpRef<Tab>, chunk: FuncId) {
    let tabcall = emittabcall(&lcx.data.func, lcx.data.bump[tab].func);
    let size = lcx.data.func.code.push(Ins::RES(IRT_IDX, tabcall, 0.into()));
    let cinit = lcx.data.func.code.push(Ins::CINIT(size, chunk));
    let ret = lcx.data.func.code.push(Ins::RET());
    lcx.data.func.code.set(INS_ENTRY, Ins::JMP(cinit, ret, 0.into()));
}

/* ---- Variables ----------------------------------------------------------- */

fn emitvararms(lcx: &mut Lcx, var: BumpRef<Var>) {
    let mut ctr = INS_ENTRY;
    let ret = lcx.data.func.code.push(Ins::RET());
    let bump = Access::borrow(&lcx.data.bump);
    for (i, &setter) in bump[var].value.iter().enumerate() {
        let vset = &bump[setter];
        let model = &bump[vset.model];
        let next = reserve(&lcx.data.func, 1);
        match vset.vst {
            VSet::SIMPLE => {
                if !model.guard.is_nil() {
                    emitcheck(lcx, &mut ctr, model.guard.erase(), next);
                    let cond = emitvalue(lcx, &mut ctr, model.guard);
                    emitjumpifnot(&lcx.data.func, &mut ctr, cond, next);
                }
                emitcheck(lcx, &mut ctr, lcx.objs[vset.obj].value.erase(), next);
            },
            VSet::PREFIX => {
                let var = &bump[vset.var];
                // SourcePrefix on VSET implies:
                debug_assert!(bump[model.tab].n <= bump[var.tab].n);
                let idx = idxtransfer(lcx, var.tab, model.tab, bump[var.tab].n as _,
                    bump[model.tab].n as _, INS_FLATIDX);
                let call = emitcallvm1(&lcx.data, idx, model.base + Mod::SUB_AVAIL);
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
    let mut ctr = INS_ENTRY;
    let bump = Access::borrow(&lcx.data.bump);
    let var = &bump[var];
    lcx.data.tmp_vty.clear();
    pushdeco__old(&lcx.objs, var.obj.erase(), &mut lcx.data.tmp_vty);
    let ds = decomposition_size(&lcx.objs, var.obj.erase());
    let vardim = bump[var.tab].n as usize;
    let armcall = emitcallvm1(&lcx.data, INS_FLATIDX, var.base + Var::SUB_ARM);
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
                let idx = idxtransfer(lcx, var.tab, model.tab, vardim, modeldim,
                    INS_FLATIDX);
                let call = emitcallvm1(&lcx.data, idx, model.base + Mod::SUB_VALUE);
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
                    let baseidx = idxtransfer(lcx, model.tab, var.tab, modeldim,
                        vardim, idx);
                    let ofs = lcx.data.func.code.push(Ins::SUB(IRT_IDX, INS_FLATIDX, baseidx));
                    let base = reserve(&lcx.data.func, ds);
                    for (j, &ty) in lcx.data.tmp_vty.iter().enumerate() {
                        let res = lcx.data.func.code.push(
                            Ins::RES(Type::PTR, call, vset.ret + j as isize));
                        let ptr = emitarrayptr(&lcx.data.func, res, ofs, ty);
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
    let call = emitcallvm(lower, idx, base + Var::SUB_VALUE, inline);
    lower.func.code.extend(
        decomposition__old(&lcx.objs, obj.erase(), &mut lower.tmp_ty)
        .iter()
        .enumerate()
        .map(|(i,&ty)| Ins::RES(ty, call, i.into()))
    )
}

fn emitvarloadshape(lcx: &mut Lcx, var: BumpRef<Var>, idx: InsId, inline: bool) -> InsId {
    let Var { base, obj, .. } = lcx.data.bump[var];
    debug_assert!(lcx.objs[lcx.objs[obj].ann].op == Obj::TTEN);
    let call = emitcallvm(&lcx.data, idx, base + Var::SUB_VALUE, inline);
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
    let call = emitcallvm(&lcx.data, idx, base + Var::SUB_ARM, inline);
    let arm = lcx.data.func.code.push(Ins::RES(IRT_ARM, call, 0.into()));
    let none = lcx.data.func.code.push(Ins::KINT(IRT_ARM, !0));
    let check = lcx.data.func.code.push(Ins::NE(arm, none));
    emitjumpifnot(&lcx.data.func, ctr, check, fail);
}

/* ---- Models -------------------------------------------------------------- */

// only non-simple models are handled here.
// simple models emit directly into the variable definition.

fn emitmodavail(lcx: &mut Lcx, model: BumpRef<Mod>) {
    let mut ctr = INS_ENTRY;
    let bump = Access::borrow(&lcx.data.bump);
    let model = &bump[model];
    let ret = lcx.data.func.code.push(Ins::RET());
    let kfal = lcx.data.func.code.push(Ins::KINT(Type::B1, 0));
    let jfal = lcx.data.func.code.push(Ins::JMP(kfal, ret, 0.into()));
    if !model.guard.is_nil() {
        emitcheck(lcx, &mut ctr, model.guard.erase(), jfal);
        let cond = emitvalue(lcx, &mut ctr, model.guard);
        emitjumpifnot(&lcx.data.func, &mut ctr, cond, jfal);
    }
    for setter in &model.value {
        emitcheck(lcx, &mut ctr, setter.obj.erase(), jfal);
    }
    let ktru = lcx.data.func.code.push(Ins::KINT(Type::B1, 1));
    lcx.data.func.code.set(ctr, Ins::JMP(ktru, ret, 0.into()));
}

fn emitmodvalue(lcx: &mut Lcx, model: BumpRef<Mod>) {
    let mut ctr = INS_ENTRY;
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
    let mut ctr = INS_ENTRY;
    let mut ret: PhiId = 0.into();
    let objs = Access::borrow(&lcx.objs);
    let fail = lcx.data.func.code.push(Ins::ABORT());
    for &value in &objs[query].value {
        emitcheck(lcx, &mut ctr, value.erase(), fail);
    }
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
    ChunkInit(BumpRef<Tab>, FuncId),
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
    lcx.data.func.entry = INS_ENTRY;
    reserve(&lcx.data.func, 1);
    // flatidx:
    match &lcx.data.func.kind {
        FuncKind::Chunk(chunk) => match chunk.scl {
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
            ChunkInit(tab, chunk) => emitcinit(lcx, tab, chunk),
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
                emittemplate(lcx, base+1, Template::ChunkInit(tab, base));
                emittemplate(lcx, base+2, Template::VarArm(bump.cast()));
                emittemplate(lcx, base+3, Template::ChunkInit(tab, base+2));
            },
            Obj::MOD => {
                if lcx.data.bump[bump.cast::<Mod>()].mt == Mod::COMPLEX {
                    let Mod { base, tab, .. } = lcx.data.bump[bump.cast::<Mod>()];
                    lcx.data.tab = tab;
                    emittemplate(lcx, base,   Template::ModVal(bump.cast()));
                    emittemplate(lcx, base+1, Template::ChunkInit(tab, base));
                    emittemplate(lcx, base+2, Template::ModAvail(bump.cast()));
                    emittemplate(lcx, base+3, Template::ChunkInit(tab, base+2));
                }
            },
            Obj::QUERY => {
                // TODO: make query take the dest as parameter and return only fxes
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
                    for &ty in decomposition__old(&lcx.objs, ann, &mut lcx.data.tmp_ty) {
                        debug_assert!(cursor & (ty.size() - 1) == 0);
                        putofs.push(cursor as Offset);
                        sig = sig.add_return(ty);
                        cursor += ty.size();
                    }
                }
                sig.finish_returns().add_arg(IRT_IDX).finish_args();
                let func = lcx.ir.funcs.push(func);
                trace!(LOWER "QUERY {:?} func: {:?}", obj, func);
                emittemplate(lcx, func, Template::Query(obj.cast()));
            },
            Obj::FUNC => todo!(),
            _ => unreachable!()
        }
    }
}

fn resetvm(mat: &mut BitMatrix<FuncId, ResetId>, value: FuncId, id: ResetId) {
    mat[value].set(id);
    mat[value+2].set(id); // reset arm (var) or availability (model)
}

// construct and solve the dataflow equations:
//   for each function F, let R(F) denote its reset set.
//   for each explicit reset r and func F:
//     (1) r ∈ R(F) if node(F) ∈ r,   where node(F) is the node F was generated from.
//   for each pair of functions F, G:
//     (2) R(G) ⊂ R(F) if F calls G
//     (3) R(G) = R(F) if F initializes G
fn computereset(ccx: &mut Ccx<Lower, R>) {
    let mut mat: BitMatrix<FuncId, ResetId> = Default::default();
    mat.resize(ccx.ir.funcs.end(), ResetId::MAXNUM.into());
    // mark explicit resets
    for (_, o) in ccx.objs.pairs() {
        if let ObjectRef::RESET(&RESET { id, ref objs, .. }) = o {
            let id: ResetId = zerocopy::transmute!(id);
            for &obj in objs {
                let ptr = ccx.data.objs[&obj];
                match ccx.objs[obj].op {
                    Obj::VAR => {
                        let var = &ccx.data.bump[ptr.cast::<Var>()];
                        resetvm(&mut mat, var.base, id);
                        for &vset in &var.value {
                            let vset = &ccx.data.bump[vset];
                            if vset.vst != VSet::SIMPLE {
                                resetvm(&mut mat, ccx.data.bump[vset.model].base, id);
                            }
                        }
                    },
                    _ /* MOD */ => {
                        let model = &ccx.data.bump[ccx.data.objs[&obj].cast::<Mod>()];
                        let base = match model.mt {
                            Mod::SIMPLE => {
                                // simple model: reset the variable
                                ccx.data.bump[model.value[0].var].base
                            },
                            _ /* COMPLEX */ => {
                                // complex model: reset the model
                                model.base
                            }
                        };
                        resetvm(&mut mat, base, id);
                    }
                }
            }
        }
    }
    // construct constraints
    #[repr(C)]
    #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
    struct Con { f: FuncId, g: FuncId } // R(G) ⊂ R(F)
    let base = ccx.tmp.end();
    let con = ccx.tmp.align_for::<Con>();
    for (f, func) in ccx.ir.funcs.pairs() {
        for (_, ins) in func.code.pairs() {
            match ins.opcode() {
                Opcode::CALLC|Opcode::CALLCI => {
                    let (_, _, g) = ins.decode_CALLC();
                    if f != g {
                        con.push(Con { f, g });
                    }
                },
                Opcode::CINIT => {
                    let (_, g) = ins.decode_CINIT();
                    con.push(Con { f, g });
                    con.push(Con { f:g, g:f });
                },
                _ => {}
            }
        }
    }
    // solve the system
    let con: &[Con] = &ccx.tmp[base.cast_up()..];
    loop {
        let mut fixpoint = true;
        for &Con {f, g} in con {
            let [fr, gr] = mat.get_rows_mut([f, g]);
            if !gr.is_subset(fr) {
                fixpoint = false;
                fr.union(gr);
            }
        }
        if fixpoint { break }
    }
    // update ir
    for (id, func) in ccx.ir.funcs.pairs_mut() {
        let reset: ResetSet = mat[id].try_into().unwrap();
        func.reset = reset | ResetId::GLOBAL;
    }
}

impl Stage for Lower {

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
            let mut tmp = Default::default();
            dump_ir(&mut tmp, &ccx.ir);
            trace!("{}", core::str::from_utf8(tmp.as_slice()).unwrap());
        }
        Ok(())
    }

}
