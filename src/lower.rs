//! Graph -> IR.

use core::cmp:: min;
use core::iter::{repeat_n, zip};
use core::mem::{replace, swap};

use alloc::vec::Vec;
use enumset::EnumSet;

use crate::bitmap::BitMatrix;
use crate::bump::{self, Bump, BumpRef};
use crate::compile::{self, Ccx, Stage};
use crate::dump::dump_ir;
use crate::hash::HashMap;
use crate::index::{IndexOption, IndexVec, InvalidValue};
use crate::ir::{self, Chunk, DebugFlag, DebugSource, Func, FuncId, FuncKind, Ins, InsId, Opcode, Phi, PhiId, Query, SignatureBuilder, Type, IR};
use crate::lang::Lang;
use crate::mem::{Offset, ResetId, ResetSet, SizeClass};
use crate::obj::{cast_args, BinOp, Intrinsic, LocalId, Obj, ObjRef, ObjectRef, Objects, Operator, BINOP, CALLX, CAT, DIM, EXPR, FLAT, GET, INTR, KFP64, KINT, KINT64, KSTR, LEN, LET, LGET, LOAD, MOD, NEW, QUERY, RESET, SPEC, SPLAT, TAB, TPRI, TTEN, TTUP, VAR, VGET, VSET};
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
        obj: ObjRef<MOD>,
        tab: BumpRef<Tab>,
        base: FuncId,
        n: u8,
        mt: u8
    } outputs: [VSet; |m| m.n as usize]
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct VSet {
    model: BumpRef<Mod>,
    var: BumpRef<Var>,
    ret: PhiId,
    vst: u8,
    idx: u8
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

fn elementtype(objs: &Objects, idx: ObjRef) -> Primitive {
    match objs.get(idx) {
        ObjectRef::TPRI(&TPRI { ty, .. }) => Primitive::from_u8(ty),
        ObjectRef::TTEN(&TTEN { elem, .. }) => elementtype(objs, elem),
        _ => unreachable!()
    }
}

fn vsettype(objs: &Objects, model: ObjRef<MOD>, idx: usize) -> ObjRef {
    let ann = objs[objs[model].value].ann;
    match objs[model].outputs.len() {
        1 => {
            debug_assert!(idx == 0);
            ann
        },
        _ => {
            debug_assert!(objs[ann].op == Obj::TTUP);
            objs[ann.cast::<TTUP>()].elems[idx]
        }
    }
}

struct LocalSlot {
    placeholder: IndexOption<InsId>,
    only_shape: bool
}

#[repr(C)] // need repr(C) for transmuting references
pub struct Lower<O=RW, F=RW> {
    bump: Access<Bump<u32>, O>,
    objs: Access<HashMap<ObjRef, BumpRef<()>>, O>,
    locals: IndexVec<LocalId, LocalSlot>,
    // TODO: remove the following tmp_* fields and use ccx.tmp instead:
    tmp_ins: Vec<InsId>,
    tmp_vty: Vec<Type>, // for emitvarvalue
    tmp_ty: Vec<Type>, // for expressions
    // current function:
    func: Access<Func, F>,
    tab: BumpRef<Tab>,
    check: IndexOption<InsId>
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
    let mut func = Func::new(FuncKind::Chunk(Chunk::new(SizeClass::GLOBAL)),
        DebugSource::new(idx, EnumSet::empty()));
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

fn makeinitfunc(ir: &mut IR, obj: ObjRef, flags: EnumSet<DebugFlag>) {
    let mut func = Func::new(FuncKind::Chunk(Chunk::new(SizeClass::GLOBAL)),
        DebugSource::new(obj, flags | DebugFlag::INIT));
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
        let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)),
            DebugSource::new(idx, DebugFlag::VALUE));
        let mut sig = func.build_signature();
        for &ty in decomposition__old(&ctx.objs, var.ann, &mut lower.tmp_ty) {
            sig = sig.add_return(ty);
        }
        maybeidxarg(sig.finish_returns(), scl).finish_args();
        ctx.ir.funcs.push(func);
    }
    // value.init:
    makeinitfunc(&mut ctx.ir, idx.erase(), DebugFlag::VALUE.into());
    // arm:
    {
        let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)),
            DebugSource::new(idx, EnumSet::empty()));
        maybeidxarg(func.build_signature().add_return(IRT_ARM).finish_returns(), scl).finish_args();
        ctx.ir.funcs.push(func);
    }
    // arm.init
    makeinitfunc(&mut ctx.ir, idx.erase(), EnumSet::empty());
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
    let &[vset] = &model.outputs else { return false };
    let vset = &objs[vset];
    if !vset.idx.is_empty() { return false };
    objs[vset.var].tab == model.tab
}

fn createmod(ctx: &mut Ccx<Lower, R>, idx: ObjRef<MOD>, obj: &MOD) {
    let lower = &mut *ctx.data;
    let mt = match issimplemod(&ctx.objs, obj) { true => Mod::SIMPLE, false => Mod::COMPLEX };
    let base = ctx.ir.funcs.end();
    let model: BumpRef<Mod> = lower.bump.push(Mod {
        obj: idx,
        tab: lower.objs[&obj.tab.erase()].cast(),
        base,
        n: obj.outputs.len() as _,
        mt,
        outputs: []
    }).cast();
    // create vsets
    let mut ret: PhiId = 0.into();
    for (i, &setter) in obj.outputs.iter().enumerate() {
        let vset = &ctx.objs[setter];
        let var = lower.objs[&vset.var.erase()].cast();
        let ann = vsettype(&ctx.objs, idx, i);
        let vst = if mt == Mod::SIMPLE {
            VSet::SIMPLE
        } else if isprefixidx(&ctx.objs, obj.tab, vset) && {
            // TODO: the current code assumes that the value is rectangular,
            // but the optimization itself doesn't necessarily require it, non-rectangular values
            // just require more logic when storing/loading.
            let vann = ctx.objs[vset.var].ann;
            ann == vann
                || (ctx.objs[ann].op == Obj::TTEN && ctx.objs[ann.cast::<TTEN>()].elem == vann)
        } {
            VSet::PREFIX
        } else {
            VSet::COMPLEX
        };
        let ptr = lower.bump.push(VSet { model, var, ret, vst, idx: i as _ });
        let vn = lower.bump[var].n;
        lower.bump[var].n = vn+1;
        lower.bump[
            var.cast::<Var<()>>()
                .offset(1)
                .cast::<BumpRef<VSet>>()
                .offset(vn as _)
        ] = ptr;
        // note: for var definitions we don't actually need the last dimension sizes (at least for
        // PREFIX models), but they are included here for simpler codegen when forwarding to the
        // model. the optimizer is going to delete them anyway.
        ret += decomposition_size(&ctx.objs, ann) as isize;
    }
    // create functions for complex models only
    if mt == Mod::COMPLEX {
        let scl = sizeclass(&ctx.objs, obj.tab);
        // value:
        {
            let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)),
                DebugSource::new(idx, DebugFlag::VALUE));
            let mut sig = func.build_signature();
            let base = ctx.tmp.end();
            for &mut ty in decomposition(&ctx.objs, ctx.objs[obj.value].ann, &mut ctx.tmp) {
                sig = sig.add_return(ty);
            }
            ctx.tmp.truncate(base);
            maybeidxarg(sig.finish_returns(), scl).finish_args();
            ctx.ir.funcs.push(func);
        }
        // value.init:
        makeinitfunc(&mut ctx.ir, idx.erase(), DebugFlag::VALUE.into());
        // avail
        {
            let mut func = Func::new(FuncKind::Chunk(Chunk::new(scl)),
                DebugSource::new(idx, EnumSet::empty()));
            maybeidxarg(func.build_signature().add_return(Type::B1).finish_returns(), scl)
                .finish_args();
            ctx.ir.funcs.push(func);
        }
        // avail.init:
        makeinitfunc(&mut ctx.ir, idx.erase(), EnumSet::empty());
        trace!(LOWER "MOD {:?} value: {:?}[{:?}] avail: {:?}[{:?}]",
            idx, base, base+1, base+2, base+3);
    }
}

fn collectobjs(ctx: &mut Ccx<Lower>) {
    // pass 1: count vsets in var.mark
    let mut idx = ObjRef::NIL;
    while let Some(i) = ctx.objs.next(idx) {
        idx = i;
        let obj = ctx.objs[idx];
        if obj.op == Obj::VSET {
            let var = ctx.objs[idx.cast::<VSET>()].var;
            ctx.objs[var].mark += 1;
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
    let [next] = areserve(func);
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

/* ---- Loops --------------------------------------------------------------- */

struct Loop {
    enter: Ins,         // dominates head, body_entry, body, tail_entry, tail, and exit
    head: InsId,        // dominates body_entry, body, tail_entry, tail, and exit
    body_entry: InsId,  // dominates body, tail_entry, and tail
    body: InsId,        // dominates tail_entry and tail
    tail_entry: InsId,  // dominates tail
    tail: InsId,        // jumps to either exit or body_entry
    exit: InsId,        // exits the loop
}

fn newloop(func: &Func) -> Loop {
    let [head, tail, body, exit] = areserve(func);
    Loop {
        enter: Ins::GOTO(head),
        head,
        body_entry: body,
        body,
        tail_entry: tail,
        tail,
        exit
    }
}

fn closeloop(func: &Func, loop_: Loop) -> (Ins, InsId) {
    func.code.set(loop_.head, Ins::GOTO(loop_.body_entry));
    func.code.set(loop_.body, Ins::GOTO(loop_.tail_entry));
    func.code.set(loop_.tail, Ins::GOTO(loop_.body_entry));
    (loop_.enter, loop_.exit)
}

fn ctrcloseloop(func: &Func, loop_: Loop, ctr: &mut InsId) {
    let (enter, exit) = closeloop(func, loop_);
    func.code.set(replace(ctr, exit), enter);
}

fn emitloopinit(func: &Func, loop_: &mut Loop, phi: PhiId, init: InsId) {
    let enter = func.code.push(loop_.enter);
    loop_.enter = Ins::JMP(init, enter, phi);
}

fn emitrangeloop(func: &Func, loop_: &mut Loop, ty: Type, start: InsId, end: InsId) -> InsId {
    let [head, tail] = areserve(func);
    let iphi = func.phis.push(Phi::new(ty));
    let init = func.code.push(Ins::JMP(start, head, iphi));
    let check = func.code.push(Ins::LT(start, end));
    func.code.set(replace(&mut loop_.head, head), Ins::IF(check, init, loop_.exit));
    let i = func.code.push(Ins::PHI(ty, loop_.body, iphi));
    let one = func.code.push(Ins::KINT(ty, 1));
    let inext = func.code.push(Ins::ADD(ty, i, one));
    let check = func.code.push(Ins::LT(inext, end));
    let jumptail = func.code.push(Ins::JMP(inext, tail, iphi));
    func.code.set(replace(&mut loop_.tail, tail), Ins::IF(check, jumptail, loop_.exit));
    i
}

fn emitcounter(func: &Func, loop_: &mut Loop, ty: Type) -> InsId {
    let phi = func.phis.push(Phi::new(ty));
    let zero = func.code.push(Ins::KINT(ty, 0));
    let one = func.code.push(Ins::KINT(ty, 1));
    emitloopinit(func, loop_, phi, zero);
    let value = func.code.push(Ins::PHI(IRT_IDX, loop_.body_entry, phi));
    let next = func.code.push(Ins::ADD(IRT_IDX, value, one));
    let [tail] = areserve(func);
    func.code.set(replace(&mut loop_.tail, tail), Ins::JMP(next, tail, phi));
    value
}

fn extractshape(objs: &Objects, value: InsId, ty: &TTEN) -> InsId {
    let ds = decomposition_size(objs, ty.elem);
    value + ds as isize
}

fn emittensordataloop(
    lcx: &mut Lcx,
    loop_: &mut Loop,
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
    loop_: &mut Loop,
    ty: &TTEN,
    value: InsId
) -> InsId {
    let shape = extractshape(&lcx.objs, value, ty);
    emittensordataloop(lcx, loop_, ty, value, shape)
}

fn emitreduce(
    func: &Func,
    loop_: &mut Loop,
    ty: Type,
    init: InsId,
    next: InsId,
    accumulator_placeholder: InsId,
    result_placeholder: InsId
) {
    let l_phi = func.phis.push(Phi::new(ty));
    let r_phi = func.phis.push(Phi::new(ty));
    let [head, tail, body] = areserve(func);
    emitloopinit(func, loop_, r_phi, init);
    func.code.set(accumulator_placeholder, Ins::PHI(ty, loop_.body_entry, l_phi));
    func.code.set(result_placeholder, Ins::PHI(ty, loop_.exit, r_phi));
    func.code.set(replace(&mut loop_.head, head), Ins::JMP(init, head, l_phi));
    func.code.set(replace(&mut loop_.body, body), Ins::JMP(next, body, r_phi));
    func.code.set(replace(&mut loop_.tail, tail), Ins::JMP(next, tail, l_phi));
}

fn emitloopstore(
    func: &Func,
    loop_: &mut Loop,
    element: InsId,
    size: InsId,
    ptr: InsId,
    ds: usize
) -> InsId {
    let store_accumulator = reserve(func, ds);
    let store_result = reserve(func, ds);
    let nop = func.code.push(Ins::NOP(Type::FX));
    let idx = emitcounter(func, loop_, IRT_IDX);
    for i in 0..ds as isize {
        let offset = func.code.push(Ins::MUL(IRT_IDX, idx, size+i));
        let ptr_offset = func.code.push(Ins::ADDP(ptr+i, offset));
        let store = func.code.push(Ins::STORE(ptr_offset, element+i));
        let next = func.code.push(Ins::MOVF(Type::FX, store, store_accumulator+i));
        emitreduce(func, loop_, Type::FX, nop, next, store_accumulator+i, store_result+i);
    }
    store_result
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
    loop_: &mut Loop,
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

struct ExprSlot {
    value: InsId,
    ctr: InsId
}

struct ExprIter<'a> {
    loop_: &'a mut Loop,
    element: InsId,
    shape: Option<ExprSlot>
}

enum Visit<'a, 'b> {
    Materialize(&'a mut ExprSlot),
    Shape(&'a mut ExprSlot),
    Iterate(&'a mut ExprIter<'b>),
    None(&'a mut InsId)
}

impl Visit<'_, '_> {

    fn is_materialize(&self) -> bool {
        matches!(self, Visit::Materialize(_))
    }

    fn is_shape(&self) -> bool {
        matches!(self, Visit::Shape(_))
    }

    fn is_iterate(&self) -> bool {
        matches!(self, Visit::Iterate(_))
    }

    fn is_none(&self) -> bool {
        matches!(self, Visit::None(_))
    }

    fn unwrap_materialize(&mut self) -> &mut ExprSlot {
        match self {
            Visit::Materialize(slot) => slot,
            _ => unreachable!()
        }
    }

    fn head(&mut self) -> &mut InsId {
        match self {
            Visit::Materialize(slot) | Visit::Shape(slot) => &mut slot.ctr,
            Visit::Iterate(iter) => &mut iter.loop_.head,
            Visit::None(ctr) => ctr
        }
    }

    fn ctr(&mut self) -> &mut InsId {
        match self {
            Visit::Materialize(slot) | Visit::Shape(slot) => &mut slot.ctr,
            Visit::Iterate(_) => unreachable!(),
            Visit::None(ctr) => ctr
        }
    }

}

impl<'b> Visit<'_, 'b> {

    fn reborrow_mut(&mut self) -> Visit<'_, 'b> {
        match self {
            Visit::Materialize(slot) => Visit::Materialize(slot),
            Visit::Shape(slot) => Visit::Shape(slot),
            Visit::Iterate(iter) => Visit::Iterate(iter),
            Visit::None(ctr) => Visit::None(ctr)
        }
    }

}

fn isnoniterable(op: u8) -> bool {
    // TODO: make LET/LGET iterable
    (Operator::CAT|Operator::LET|Operator::LGET|Operator::GET|Operator::LOAD|Operator::CALLX)
        .as_u64_truncated() & (1 << op) != 0
}

fn visitexpr(lcx: &mut Lcx, expr: ObjRef<EXPR>, mut visit: Visit) {
    if visit.is_none() && lcx.data.check.is_none() {
        // nothing to do
        return
    }
    if let Visit::Iterate(iter) = visit.reborrow_mut() && isnoniterable(lcx.objs[expr].op) {
        iter.element = emitexprmi(lcx, expr, &mut iter.loop_, iter.shape.as_mut());
        return
    }
    if let Visit::Shape(slot) = visit.reborrow_mut() && lcx.objs[lcx.objs[expr].ann].op != Obj::TTEN {
        slot.value = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
        visitexpr(lcx, expr, Visit::None(&mut slot.ctr));
        return
    }
    if let Visit::None(ctr) = visit.reborrow_mut()
        && (Operator::VGET|Operator::LET).as_u64_truncated() & (1 << lcx.objs[expr].op) == 0
    {
        let objs = Access::borrow(&lcx.objs);
        let raw = objs.get_raw(expr.erase());
        for i in objs[expr.erase()].ref_params() {
            // only recurse into exprs, other objects are in their own chunks.
            let o: ObjRef = zerocopy::transmute!(raw[i+1]);
            if Operator::is_expr_raw(objs[o].op) {
                visitexpr(lcx, o.cast(), Visit::None(ctr));
            }
        }
        return
    }
    match lcx.objs[expr].op {
        Obj::KINT|Obj::KINT64|Obj::KFP64|Obj::KSTR => {
            visit.unwrap_materialize().value = emitk(lcx, expr)
        },
        Obj::DIM => {
            visit.unwrap_materialize().value = emitdim(lcx, expr.cast())
        },
        Obj::LEN => {
            let slot = visit.unwrap_materialize();
            slot.value = emitlen(lcx, expr.cast(), &mut slot.ctr);
        },
        Obj::LET => visitlet(lcx, expr.cast(), visit),
        Obj::LGET => visitlget(lcx, expr.cast(), visit),
        Obj::VGET => visitvget(lcx, expr.cast(), visit),
        Obj::CAT => visitcat(lcx, expr.cast(), visit),
        Obj::IDX => todo!(),
        Obj::BINOP => visitbinop(lcx, expr.cast(), visit),
        Obj::INTR => visitintrinsic(lcx, expr.cast(), visit),
        Obj::LOAD => visitload(lcx, expr.cast(), visit),
        Obj::NEW => visitnew(lcx, expr.cast(), visit),
        Obj::GET => visitget(lcx, expr.cast(), visit),
        Obj::CALLX => visitcallx(lcx, expr.cast(), visit),
        _ => unreachable!()
    }
}

// iterate
fn emitexpri(
    lcx: &mut Lcx,
    expr: ObjRef<EXPR>,
    loop_: &mut Loop,
    shape: Option<&mut ExprSlot>
) -> InsId {
    let mut expri = ExprIter {
        loop_,
        element: InsId::INVALID.into(),
        shape: match &shape {
            &Some(&mut ExprSlot { ctr, .. }) => Some(ExprSlot {
                value: InsId::INVALID.into(),
                ctr
            }),
            None => None
        }
    };
    visitexpr(lcx, expr, Visit::Iterate(&mut expri));
    if let Some(shape) = shape {
        *shape = expri.shape.unwrap();
        debug_assert!(shape.value != InsId::INVALID.into());
    }
    debug_assert!(expri.element != InsId::INVALID.into());
    expri.element
}

// iterate and return shape
fn emitexpris(
    lcx: &mut Lcx,
    expr: ObjRef<EXPR>,
    loop_: &mut Loop,
    shapectr: &mut InsId
) -> (InsId, InsId) {
    let mut shape = ExprSlot {
        value: InsId::INVALID.into(),
        ctr: *shapectr
    };
    let element = emitexpri(lcx, expr, loop_, Some(&mut shape));
    *shapectr = shape.ctr;
    (element, shape.value)
}

// iterate then materialize
fn emitexprim(lcx: &mut Lcx, expr: ObjRef<EXPR>, ctr: &mut InsId) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    let cty: &TTEN = &objs[objs[expr].ann.cast()];
    let mut loop_ = newloop(&lcx.data.func);
    let (element, shape) = emitexpris(lcx, expr, &mut loop_, ctr);
    let (ptrs, esizes) = alloctensordata(lcx, *ctr, cty, shape);
    let eds = decomposition_size(objs, cty.elem);
    let stores = emitloopstore(&lcx.data.func, &mut loop_, element, esizes, ptrs, eds);
    ctrcloseloop(&lcx.data.func, loop_, ctr);
    let ret = lcx.data.func.code.extend(
        (0..eds as isize).map(|i| Ins::MOVF(Type::PTR, ptrs+i, stores+i)));
    lcx.data.func.code.extend((0..cty.dim as isize).map(|i| Ins::MOV(IRT_IDX, shape+i)));
    ret
}

// materialize then iterate
fn emitexprmi(
    lcx: &mut Lcx,
    expr: ObjRef<EXPR>,
    loop_: &mut Loop,
    mut want_shape: Option<&mut ExprSlot>
) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    let cty: &TTEN = &objs[objs[expr].ann.cast()];
    let ctr = match want_shape.as_deref_mut() {
        Some(slot) => &mut slot.ctr,
        None => &mut loop_.head
    };
    let value = emitexprv(lcx, expr, ctr);
    let shape = extractshape(objs, value, cty);
    if let Some(out) = want_shape {
        out.value = shape;
    }
    emittensordataloop(lcx, loop_, cty, value, shape)
}

fn emitexprvors(lcx: &mut Lcx, expr: ObjRef<EXPR>, ctr: &mut InsId, v: bool) -> InsId {
    let mut slot = ExprSlot {
        value: InsId::INVALID.into(),
        ctr: *ctr
    };
    let visit = match v {
        true => Visit::Materialize(&mut slot),
        false => Visit::Shape(&mut slot)
    };
    visitexpr(lcx, expr, visit);
    debug_assert!(slot.value != InsId::INVALID.into());
    *ctr = slot.ctr;
    slot.value
}

// materialize
fn emitexprv(lcx: &mut Lcx, expr: ObjRef<EXPR>, ctr: &mut InsId) -> InsId {
    emitexprvors(lcx, expr, ctr, true)
}

// shape
fn emitexprs(lcx: &mut Lcx, expr: ObjRef<EXPR>, ctr: &mut InsId) -> InsId {
    emitexprvors(lcx, expr, ctr, false)
}

// iterate if tensor, materialize if scalar
fn emitbroadcastv(
    lcx: &mut Lcx,
    expr: ObjRef<EXPR>,
    loop_: &mut Loop,
    shape: Option<&mut ExprSlot>
) -> InsId {
    match lcx.objs[lcx.objs[expr].ann].op {
        Obj::TTEN => {
            emitexpri(lcx, expr, loop_, shape)
        },
        _ => {
            if let Some(slot) = shape {
                slot.value = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
            }
            emitexprv(lcx, expr, &mut loop_.head)
        }
    }
}

// check
fn emitexprc(lcx: &mut Lcx, expr: ObjRef<EXPR>, ctr: &mut InsId, fail: InsId) {
    let prev = replace(&mut lcx.data.check, Some(fail).into());
    visitexpr(lcx, expr, Visit::None(ctr));
    lcx.data.check = prev;
}

// check and value
fn emitexprcv(lcx: &mut Lcx, expr: ObjRef<EXPR>, ctr: &mut InsId, fail: InsId) -> InsId {
    let prev = replace(&mut lcx.data.check, Some(fail).into());
    let value = emitexprv(lcx, expr, ctr);
    lcx.data.check = prev;
    value
}

fn emitk(lcx: &mut Lcx, expr: ObjRef<EXPR>) -> InsId {
    let ObjectRef::TPRI(&TPRI { ty, .. }) = lcx.objs.get(lcx.objs[expr].ann) else { unreachable!() };
    let ty = Primitive::from_u8(ty).to_ir();
    match lcx.objs.get(expr.erase()) {
        ObjectRef::KINT(&KINT { k, .. }) => lcx.data.func.code.push(Ins::KINT(ty, k as _)),
        ObjectRef::KINT64(&KINT64 { k, .. }) => lcx.data.func.code.push(Ins::KINT64(ty, zerocopy::transmute!(k))),
        ObjectRef::KFP64(&KFP64 { k, .. }) => lcx.data.func.code.push(Ins::KFP64(ty, zerocopy::transmute!(k))),
        ObjectRef::KSTR(&KSTR { k, .. }) => lcx.data.func.code.push(Ins::KSTR(ty, zerocopy::transmute!(k))),
        _ => unreachable!()
    }
}

fn emitdim(lcx: &mut Lcx, expr: ObjRef<DIM>) -> InsId {
    let source = lcx.data.bump[lcx.data.tab].axes.len();
    let axis = lcx.objs[expr].axis;
    axisidx(lcx, lcx.data.tab, source, (axis+1) as _, INS_FLATIDX)
}

fn emitlen(lcx: &mut Lcx, expr: ObjRef<LEN>, ctr: &mut InsId) -> InsId {
    let LEN { axis, value, .. } = lcx.objs[expr];
    emitexprs(lcx, value, ctr) + axis as isize
}

fn visitlet(lcx: &mut Lcx, let_: ObjRef<LET>, mut visit: Visit) {
    let LET { value, expr, .. } = lcx.objs[let_];
    lcx.data.locals.push(LocalSlot {
        placeholder: None.into(),
        only_shape: false
    });
    let [ctrnew] = areserve(&lcx.data.func);
    let mut ctr = replace(visit.ctr(), ctrnew);
    visitexpr(lcx, expr, visit);
    let slot = lcx.data.locals.raw.pop().unwrap();
    if let Some(placeholder) = slot.placeholder.unpack() {
        if slot.only_shape {
            let s = emitexprs(lcx, value, &mut ctr);
            for i in 0..lcx.objs[lcx.objs[value].ann.cast::<TTEN>()].dim as isize {
                lcx.data.func.code.set(placeholder+i, Ins::MOV(IRT_IDX, s+i));
            }
        } else {
            let v = emitexprv(lcx, value, &mut ctr);
            let base = lcx.tmp.end();
            for (i, &ty) in decomposition(&lcx.objs, lcx.objs[value].ann, &mut lcx.tmp)
                .iter()
                .enumerate()
            {
                lcx.data.func.code.set(placeholder + i as isize, Ins::MOV(ty, v + i as isize));
            }
            lcx.tmp.truncate(base);
        }
    } else {
        visitexpr(lcx, value, Visit::None(&mut ctr));
    }
    lcx.data.func.code.set(ctr, Ins::GOTO(ctrnew));
}

fn visitlget(lcx: &mut Lcx, expr: ObjRef<LGET>, visit: Visit) {
    let LGET { ann, slot, .. } = lcx.objs[expr];
    let lower = &mut *lcx.data;
    let slot = &mut lower.locals[slot];
    match visit {
        Visit::Materialize(s) => {
            s.value = if let Some(v) = slot.placeholder.unpack() && !slot.only_shape {
                v
            } else {
                let ds = decomposition_size(&lcx.objs, ann);
                let placeholder = reserve(&lower.func, ds);
                if let Some(v) = slot.placeholder.unpack() {
                    let dim = lcx.objs[ann.cast::<TTEN>()].dim;
                    for i in 0..dim as isize {
                        lower.func.code.set(v+i,
                            Ins::MOV(IRT_IDX, placeholder + ds as isize - dim as isize + i));
                    }
                    slot.only_shape = false;
                }
                slot.placeholder = Some(placeholder).into();
                placeholder
            };
        },
        Visit::Shape(s) => {
            s.value = if let Some(mut v) = slot.placeholder.unpack() {
                if !slot.only_shape {
                    v = extractshape(&lcx.objs, v, &lcx.objs[ann.cast()]);
                }
                v
            } else {
                let placeholder = reserve(&lower.func, lcx.objs[ann.cast::<TTEN>()].dim as _);
                slot.placeholder = Some(placeholder).into();
                slot.only_shape = true;
                placeholder
            };
        },
        Visit::None(_) => unreachable!(),
        Visit::Iterate(_) => todo!()
    }
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct VGETIdx {
    expr: ObjRef<EXPR>, // selected indices or NIL for splat
    value: IndexOption<InsId>, // value if non-nil; tensor for materialized, scalar for iterators
    shape: IndexOption<InsId>, // shape if computed (only for iterator)
    axis: u8, // axis in the table (first spanned axis)
    span: u8, // number of table axes spanned (slurped)
    nest: u8, // output nest level
    oaxis: u8, // axis in the output (for the nest level)
    scalar_expr: i8, // 1=>scalar, 0=>tensor, -1=>iterator (of scalars)
    scalar_axis: u8,
    _pad: [u8; 2]
}

fn vgetidx(lower: &Lower<R, R>, objs: &Objects, vget: &VGET, buf: &mut Bump<VGETIdx>) {
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
                        let top = buf.end().offset(-1);
                        buf[top].span += 1;
                        continue
                    }
                    nil = v.is_nil();
                    if (objs[v].op, objs[v].data) == (Obj::SPEC, SPEC::SLURP) {
                        span += 1;
                        continue
                    }
                    let (_, idx) = buf.reserve::<VGETIdx>();
                    idx.expr = v;
                    idx.value = None.into();
                    idx.shape = None.into();
                    idx.axis = (taxis + i) as _;
                    idx.span = span+1;
                    idx.oaxis = oaxis;
                    idx.scalar_expr = isscalarann(objs, v.erase()) as _;
                    span = 0;
                }
                taxis += fidx.len();
                oaxis += 1;
            },
            _ => {
                let is_scalar = isscalarann(objs, expr.erase());
                let (_, idx) = buf.reserve::<VGETIdx>();
                idx.expr = expr;
                idx.value = None.into();
                idx.shape = None.into();
                idx.axis = taxis as _;
                idx.span = span+1;
                idx.oaxis = oaxis;
                idx.scalar_expr = is_scalar as _;
                (taxis, span) = (taxis+1, 0);
                if !is_scalar { oaxis += 1 }
            }
        }
    }
    debug_assert!(span == 0);
    while taxis < target.axes.len() {
        let (_, idx) = buf.reserve::<VGETIdx>();
        idx.expr = ObjRef::NIL.cast();
        idx.value = None.into();
        idx.shape = None.into();
        idx.axis = taxis as _;
        idx.span = 1;
        idx.oaxis = oaxis;
        idx.scalar_expr = 0;
        taxis += 1;
        oaxis += 1;
    }
    if oaxis > 0 {
        let mut ann = &objs[vget.ann.cast::<TTEN>()];
        debug_assert!(ann.op == Obj::TTEN);
        let mut offset = 0;
        let mut onest = 0;
        debug_assert!(oaxis >= ann.dim as _);
        for i in &mut buf[base..] {
            let scalar = target.axes[i.axis as usize..(i.axis+i.span) as usize]
                .iter()
                .all(|a| a.rank == Axis::SCALAR);
            i.scalar_axis = scalar as _;
            if i.oaxis == offset+ann.dim {
                offset = i.oaxis;
                onest += 1;
                ann = &objs[ann.elem.cast::<TTEN>()];
                debug_assert!(ann.op == Obj::TTEN);
            }
            i.oaxis -= offset;
            i.nest = onest;
            debug_assert!(scalar || i.oaxis == 0);
        }
    }
}

fn emitvgetidx(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    start: BumpRef<VGETIdx>,
    end: BumpRef<VGETIdx>,
    outerloop: &mut Option<Loop>
) {
    let mut first_tensor = true;
    let first_nonrect = lcx.tmp[start..end]
        .iter()
        .find_map(|i| if let &VGETIdx { expr, oaxis, scalar_axis: 0, nest: 0, .. } = i
            && expr.is_nil()
        {
            Some(oaxis)
        } else {
            None
        })
        .unwrap_or(!0);
    let mut idx = start;
    while idx < end {
        match lcx.tmp[idx] {
            VGETIdx { value, .. } if value.is_some() => {
                // outer loop fused
                first_tensor = false;
            },
            VGETIdx { expr, oaxis, scalar_expr: 0, nest: 0, .. }
                if first_tensor && oaxis < first_nonrect && !expr.is_nil() =>
            {
                let loop_ = outerloop.insert(newloop(&lcx.data.func));
                let (element, shape) = emitexpris(lcx, expr, loop_, ctr);
                lcx.tmp[idx].value = Some(element).into();
                lcx.tmp[idx].shape = Some(shape).into();
                lcx.tmp[idx].scalar_expr = -1;
                first_tensor = false;
            },
            VGETIdx { expr, .. } if !expr.is_nil() => {
                let v = emitexprv(lcx, expr, ctr);
                lcx.tmp[idx].value = Some(v).into();
            },
            _ => {}
        }
        if first_tensor && lcx.tmp[idx].scalar_expr == 0 {
            first_tensor = false;
        }
        idx = idx.offset(1);
    }
}

fn emitvgets(
    lcx: &mut Lcx,
    ctr: &mut InsId,
    start: BumpRef<VGETIdx>,
    mut end: BumpRef<VGETIdx>,
    outshape: InsId, // must have reserved one slot per `oaxis`
    call: InsId,
    target: &Tab,
) -> IndexOption<InsId> {
    debug_assert!(start < end);
    debug_assert!(lcx.tmp[start..end].iter().all(|i| i.nest == lcx.tmp[start].nest));
    let objs = Access::borrow(&lcx.objs);
    let mut prefix: Option<(/*flat placeholder:*/InsId, /*accumulator:*/InsId)> = None;
    let mut innerloop: Option<(/*init:*/ InsId, /*start:*/ Ins, /*out:*/ InsId)> = None;
    while start < end {
        let mut e = end;
        end = end.offset(-1);
        while end > start && lcx.tmp[end].oaxis == lcx.tmp[end.offset(-1)].oaxis {
            end = end.offset(-1);
        }
        let mut len: IndexOption<InsId> = None.into();
        while e > end {
            e = e.offset(-1);
            let n = match (&mut prefix, &lcx.tmp[e]) {
                (None, &VGETIdx { scalar_expr: 1, .. }) => continue,
                (Some((flat, _)), &VGETIdx { value, axis, span, scalar_expr: 1, .. }) => {
                    let [nextflat] = areserve(&lcx.data.func);
                    let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _, nextflat);
                    lcx.data.func.code.set(replace(flat, nextflat),
                        Ins::ADD(IRT_IDX, baseflat, value.unwrap()));
                    continue
                },
                (None, &VGETIdx { shape, .. }) if shape.is_some() => shape.raw,
                (None, &VGETIdx { expr, value, .. }) if value.is_some() =>
                    extractshape(objs, value.raw, &objs[objs[expr].ann.cast()]),
                (None, &VGETIdx { axis, span, scalar_axis: 1, .. }) => {
                    let mut size = lcx.data.func.code.push(
                        Ins::RES(IRT_IDX, call, target.axes[axis as usize].ret));
                    for i in 1..span {
                        let s = lcx.data.func.code.push(
                            Ins::RES(IRT_IDX, call, target.axes[(axis+i) as usize].ret));
                        size = lcx.data.func.code.push(Ins::MUL(IRT_IDX, size, s));
                    }
                    size
                },
                (None, &VGETIdx { axis, span, oaxis, .. }) => {
                    debug_assert!(innerloop.is_none());
                    debug_assert!(oaxis == 0);
                    let [flat] = areserve(&lcx.data.func);
                    let (start, end) = emitsplatbounds(lcx, target, flat, call, axis as _,
                        (axis+span) as _);
                    let num = lcx.data.func.code.push(Ins::SUB(IRT_IDX, end, start));
                    prefix = Some((flat, num));
                    continue
                },
                (Some((flat, accumulator)), &VGETIdx { expr, value, shape, axis, span, .. }) => {
                    debug_assert!(shape.is_none()); // must materialize for nested loops
                    let [loop_init, loop_acc, loop_result, nextflat] = areserve(&lcx.data.func);
                    let mut loop_ = newloop(&lcx.data.func);
                    let j = match expr.is_nil() {
                        true => {
                            let j = emitsplatloop(lcx, &mut loop_, target, nextflat, call, axis as _,
                                (axis+span) as _);
                            Ins::MOV(IRT_IDX, j)
                        },
                        false => {
                            let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _,
                                nextflat);
                            let j = emittensorloop(lcx, &mut loop_, &objs[objs[expr].ann.cast()],
                                value.unwrap());
                            Ins::ADD(IRT_IDX, baseflat, j)
                        }
                    };
                    match innerloop {
                        Some((inner_init, start, out)) => {
                            lcx.data.func.code.set(inner_init, Ins::MOV(IRT_IDX, loop_acc));
                            lcx.data.func.code.set(replace(&mut loop_.body, out), start);
                        },
                        None => *accumulator = lcx.data.func.code.push(
                            Ins::ADD(IRT_IDX, loop_acc, *accumulator))
                    }
                    emitreduce(&lcx.data.func, &mut loop_, IRT_IDX, loop_init,
                        replace(accumulator, loop_result), loop_acc, loop_result);
                    let (enter, exit) = closeloop(&lcx.data.func, loop_);
                    innerloop = Some((loop_init, enter, exit));
                    lcx.data.func.code.set(replace(flat, nextflat), j);
                    continue
                }
            };
            len = Some(match len.unpack() {
                Some(len) => lcx.data.func.code.push(Ins::MUL(IRT_IDX, len, n)),
                None => n
            }).into();
        }
        if let Some((_, accumulator)) = prefix {
            len = Some(match len.unpack() {
                Some(len) => lcx.data.func.code.push(Ins::MUL(IRT_IDX, len, accumulator)),
                None => accumulator
            }).into();
            if let Some((init, start, out)) = innerloop {
                lcx.data.func.code.set(init, Ins::KINT(IRT_IDX, 0));
                lcx.data.func.code.set(replace(ctr, out), start);
            }
        }
        let len = match len.unpack() {
            Some(len) => Ins::MOV(IRT_IDX, len),
            None => Ins::KINT(IRT_IDX, 1)
        };
        lcx.data.func.code.set(outshape + lcx.tmp[end].oaxis as isize, len);
    }
    prefix.map(|(flat,_)| flat).into()
}

fn emitvgetvc(
    lcx: &mut Lcx,
    start: BumpRef<VGETIdx>,
    mut end: BumpRef<VGETIdx>,
    collect: Option<(/*out:*/InsId, /*in:*/InsId, /*anchor:*/InsId, /*type:*/&TTEN)>,
    outerloop: &mut Option<Loop>,
    cc: &mut IndexOption<InsId>,
    flat: &mut InsId,
    innerloop: &mut Option<(/*start:*/Ins, /*out:*/InsId)>,
    call: InsId,
    target: &Tab,
) {
    debug_assert!(start < end);
    let objs = Access::borrow(&lcx.objs);
    let (buf, esizes, eds) = match collect {
        Some((out, _, anchor, ty)) => {
            let eds = decomposition_size(objs, ty.elem);
            let (buf, esizes) = alloctensordata(lcx, anchor, ty, out + eds as isize);
            (buf, esizes, eds)
        },
        None => (InsId::INVALID.into(), InsId::INVALID.into(), 0)
    };
    let mut inner: Option<(/*init:*/ InsId, /*result:*/ InsId)> = None;
    while start < end {
        end = end.offset(-1);
        let [nextflat] = areserve(&lcx.data.func);
        let j = match lcx.tmp[end] {
            VGETIdx { value, axis, span, scalar_expr: 1, .. } => {
                let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _, nextflat);
                Ins::ADD(IRT_IDX, baseflat, value.unwrap())
            },
            VGETIdx { value, expr, scalar_expr, mut axis, mut span, .. } => {
                if expr.is_nil() {
                    while end > start && lcx.tmp[end.offset(-1)].expr.is_nil() {
                        end = end.offset(-1);
                        span += lcx.tmp[end].span;
                        axis = lcx.tmp[end].axis;
                    }
                }
                let (mut loop_, j) = match scalar_expr {
                    0 => {
                        let mut loop_ = newloop(&lcx.data.func);
                        let j = match expr.is_nil() {
                            true => {
                                let j = emitsplatloop(lcx, &mut loop_, target, nextflat, call, axis as _,
                                    (axis+span) as _);
                                Ins::MOV(IRT_IDX, j)
                            },
                            false => {
                                let baseflat = idxftrann(lcx, target, call, axis as _, (axis+span) as _,
                                nextflat);
                                let j = emittensorloop(lcx, &mut loop_, &objs[objs[expr].ann.cast()],
                                    value.raw);
                                Ins::ADD(IRT_IDX, baseflat, j)
                            }
                        };
                        (loop_, j)
                    },
                    _ => {
                        (outerloop.take().unwrap(), Ins::MOV(IRT_IDX, value.raw))
                    }
                };
                if let Some(cond) = cc.unpack() {
                    emitjumpifnot(&lcx.data.func, &mut loop_.body, cond, lcx.data.check.raw);
                    *cc = None.into();
                }
                if let &mut Some((start, out)) = innerloop {
                    lcx.data.func.code.set(replace(&mut loop_.body, out), start);
                }
                if let Some((_, invalue, _, _)) = collect {
                    let init = reserve(&lcx.data.func, 1+eds);
                    let accumulator = reserve(&lcx.data.func, 1+eds);
                    let result = reserve(&lcx.data.func, 1+eds);
                    let next = match inner {
                        Some((inner_init, inner_result)) => {
                            lcx.data.func.code.set(inner_init, Ins::MOV(IRT_IDX, accumulator));
                            for i in 1..(1+eds) as isize {
                                lcx.data.func.code.set(inner_init+i, Ins::MOV(Type::FX, accumulator+i));
                            }
                            inner_result
                        },
                        None => {
                            let stores = emitmultistore(&lcx.data.func, buf, esizes, accumulator,
                                invalue, eds);
                            let one = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
                            let next = lcx.data.func.code.push(Ins::ADD(IRT_IDX, accumulator, one));
                            lcx.data.func.code.extend(
                                (0..eds as isize)
                                .map(|i| Ins::MOVF(Type::FX, accumulator+1+i, stores+i))
                            );
                            next
                        }
                    };
                    emitreduce(&lcx.data.func, &mut loop_, IRT_IDX, init, next, accumulator, result);
                    for i in 1..(1+eds) as isize {
                        emitreduce(&lcx.data.func, &mut loop_, Type::FX, init+i, next+i,
                            accumulator+i, result+i);
                    }
                    inner = Some((init, result));
                }
                *innerloop = Some(closeloop(&lcx.data.func, loop_));
                j
            }
        };
        lcx.data.func.code.set(replace(flat, nextflat), j);
    }
    if let Some((out, in_, _, _)) = collect {
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
                lcx.data.func.code.extend((0..eds as isize) .map(|i| Ins::STORE(buf+i, in_+i)))
            }
        };
        for i in 0..eds as isize {
            lcx.data.func.code.set(out+i, Ins::MOVF(Type::PTR, buf+i, stores+1+i));
        }
    }
}

// if ALL of the following are true...
//   (1) the VGET variable has exactly one model,
//   (2) VGET and VSET tables match,
//   (3) VGET and VSET indices match,
//   (4) the model is COMPLEX
// then the VGET can be forwarded to load directly from the VSET
fn maybefwdvget(lcx: &Lcx, vget: &VGET) -> Option<BumpRef<VSet>> {
    let lower = &*lcx.data;
    let var = &lower.bump[vardata(&lower.objs, vget.var)];
    let [vv] = var.value else { return None };
    let vset = &lower.bump[vv];
    let model = &lower.bump[vset.model];
    if lower.bump[vset.model].mt != Mod::COMPLEX { return None };
    // TODO: this check can be relaxed, just need to translate index.
    if !sametab(&lcx.objs, &lower.bump[lower.tab], &lower.bump[model.tab])
        || !lcx.objs.allequal(cast_args(&vget.idx),
            cast_args(&lcx.objs[lcx.objs[model.obj].outputs[vset.idx as usize]].idx))
    {
        return None
    }
    Some(vv)
}

fn maybefusevget(idx: &[VGETIdx]) -> Option<usize> {
    let mut foundloop = None;
    for (j,i) in idx.iter().enumerate() {
        if i.nest > 0 { break }
        if i.scalar_expr == 0 {
            if foundloop.is_some() {
                // nested loop -> cannot fuse
                return None
            }
            foundloop = Some(j);
        }
    }
    foundloop
}

fn visitvgetinner(
    lcx: &mut Lcx,
    mut visit: Visit,
    start: BumpRef<VGETIdx>,
    end: BumpRef<VGETIdx>,
    ann: ObjRef,
    var: ObjRef<VAR>,
    inline: bool,
    fwdload: Option<BumpRef<VSet>> // TODO: deduce it here
) -> InsId {
    debug_assert!(!visit.is_iterate());
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    let vdata = vardata(&lcx.data.objs, var);
    let target = &bump[bump[vdata].tab];
    let isscalarload = ann == objs[var].ann;
    let mut outerloop = None;
    emitvgetidx(lcx, visit.head(), start, end, &mut outerloop);
    let [mut flat] = areserve(&lcx.data.func);
    let mut cc: IndexOption<InsId> = match (lcx.data.check.is_some(), fwdload) {
        (true, Some(vset)) => {
            let base = bump[bump[vset].model].base;
            let call = emitcallvm(&lcx.data, flat, base + Mod::SUB_AVAIL, inline);
            let cond = lcx.data.func.code.push(Ins::RES(Type::B1, call, 0.into()));
            Some(cond)
        },
        (true, None) => {
            let base = bump[vdata].base;
            let call = emitcallvm(&lcx.data, flat, base + Var::SUB_ARM, inline);
            let arm = lcx.data.func.code.push(Ins::RES(IRT_ARM, call, 0.into()));
            let none = lcx.data.func.code.push(Ins::KINT(IRT_ARM, !0));
            let cond = lcx.data.func.code.push(Ins::NE(arm, none));
            Some(cond)
        },
        (false, _) => None
    }.into();
    let eds = match objs.get(ann) {
        ObjectRef::TTEN(&TTEN { elem, .. }) => decomposition_size(objs, elem),
        _ => 0
    };
    let vload: IndexOption<InsId> = match visit.is_materialize()
        || (visit.is_shape() && isscalarload && eds > 0)
    {
        true => {
            let (func, ty, ret) = match fwdload {
                Some(vset) => {
                    let VSet { ret, idx, model, .. } = bump[vset];
                    (bump[model].base + Mod::SUB_VALUE, vsettype(objs, bump[model].obj, idx as _), ret)
                },
                None => {
                    let Var { base, obj, .. } = bump[vdata];
                    (base + Var::SUB_VALUE, obj.erase(), 0.into())
                }
            };
            let call = emitcallvm(&lcx.data, flat, func, inline);
            let base1 = lcx.tmp.end();
            let res = lcx.data.func.code.extend(
                decomposition(objs, ty, &mut lcx.tmp)
                .iter()
                .enumerate()
                .map(|(i,&ty)| Ins::RES(ty, call, ret + i as isize))
            );
            lcx.tmp.truncate(base1);
            Some(res)
        },
        false => None
    }.into();
    if isscalarload {
        match visit.reborrow_mut() {
            Visit::Materialize(slot) => slot.value = vload.unwrap(),
            Visit::Shape(slot) => slot.value = match vload.unpack() {
                Some(vload) => vload + eds as isize,
                None => lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1))
            },
            Visit::None(_) => {},
            Visit::Iterate(_) => unreachable!()
        }
        if (cc.is_some() || vload.is_some()) && start < end {
            let tcall = emittabcall(&lcx.data.func, target.func);
            emitvgetvc(lcx, start, end, None, &mut outerloop, &mut cc, &mut flat, &mut None, tcall,
                target);
        }
    } else {
        let mut innerloop: Option<(/*start:*/Ins, /*out:*/InsId)> = None;
        let tcall = emittabcall(&lcx.data.func, target.func);
        if let Visit::Materialize(slot) = visit.reborrow_mut() {
            let nest = lcx.tmp[start..].last().map(|i| i.nest+1).unwrap_or(0);
            let mut a = ann;
            for _ in 0..nest {
                debug_assert!(objs[a].op == Obj::TTEN);
                lcx.tmp.push(a);
                a = objs[a.cast::<TTEN>()].elem;
            }
            let mut end = end;
            let mut value = vload.unwrap();
            let mut anchor: IndexOption<InsId> = None.into();
            for level in (0..nest).rev() {
                let mut s = end;
                while s > start && lcx.tmp[s.offset(-1)].nest == level {
                    s = s.offset(-1);
                }
                let a: &TTEN = &objs[lcx.tmp.pop().unwrap()];
                let aeds = decomposition_size(objs, a.elem);
                let nextvalue = reserve(&lcx.data.func, a.dim as usize + aeds);
                let sprefix = emitvgets(lcx, &mut slot.ctr, s, end, nextvalue + aeds as isize,
                    tcall, target);
                if level > 0 && anchor.is_none() {
                    anchor = Some(reserve(&lcx.data.func, 1)).into();
                }
                let actr = anchor.unpack().unwrap_or(slot.ctr);
                emitvgetvc(lcx, s, end, Some((nextvalue, value, actr, a)), &mut outerloop, &mut cc,
                    &mut flat, &mut innerloop, tcall, target);
                if let Some(p) = sprefix.unpack() {
                    lcx.data.func.code.set(p, Ins::MOV(IRT_IDX, flat));
                }
                if let (Some(a), Some((start, _))) = (anchor.unpack(), &mut innerloop) {
                    lcx.data.func.code.set(a, replace(start, Ins::GOTO(a)));
                    anchor = None.into();
                }
                (value, end) = (nextvalue, s);
            }
            if let Some(anchor) = anchor.unpack() {
                lcx.data.func.code.set(replace(&mut slot.ctr, anchor), Ins::GOTO(anchor));
            }
            slot.value = value;
        } else {
            if cc.is_some() && start < end {
                emitvgetvc(lcx, start, end, None, &mut outerloop, &mut cc, &mut flat, &mut innerloop,
                    tcall, target);
            }
            if let Visit::Shape(slot) = visit.reborrow_mut() {
                if start < end {
                    slot.value = reserve(&lcx.data.func, objs[ann.cast::<TTEN>()].dim as _);
                    if let Some(p) = emitvgets(lcx, &mut slot.ctr, start, end, slot.value, tcall,
                        target).unpack()
                    {
                        lcx.data.func.code.set(p, Ins::MOV(IRT_IDX, flat));
                    }
                } else {
                    slot.value = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
                }
            }
        }
        if let Some((start, out)) = innerloop {
            lcx.data.func.code.set(replace(visit.ctr(), out), start);
        }
    }
    if let Some(cond) = cc.unpack() {
        // no loops
        emitjumpifnot(&lcx.data.func, visit.ctr(), cond, lcx.data.check.raw);
    }
    debug_assert!(outerloop.is_none());
    flat
}

fn emitvgetfuse(
    lcx: &mut Lcx,
    loop_: &mut Loop,
    want_shape: Option<&mut ExprSlot>,
    mut start: BumpRef<VGETIdx>,
    end: BumpRef<VGETIdx>,
    fuse: BumpRef<VGETIdx>,
    ann: ObjRef,
    var: ObjRef<VAR>,
    inline: bool,
    fwdload: Option<BumpRef<VSet>>,
    mut prefix: InsId
) -> InsId {
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    debug_assert!(objs[ann].op == Obj::TTEN);
    let vdata = vardata(&lcx.data.objs, var);
    let target = &bump[bump[vdata].tab];
    let tcall = emittabcall(&lcx.data.func, target.func);
    while start < fuse {
        let VGETIdx { value, scalar_expr, axis, span, .. } = lcx.tmp[start];
        debug_assert!(scalar_expr == 1);
        prefix = idxftrann(lcx, target, tcall, axis as _, (axis+span) as _, prefix);
        prefix = lcx.data.func.code.push(Ins::ADD(IRT_IDX, prefix, value.unwrap()));
        start = start.offset(1);
    }
    if let Some(outshape) = want_shape {
        outshape.value = reserve(&lcx.data.func, objs[ann.cast::<TTEN>()].dim as _);
        let outer_end = bump::iter_range(start..end)
            .find(|&i| lcx.tmp[i].nest > 0)
            .unwrap_or(end);
        if let Some(p) = emitvgets(lcx, &mut outshape.ctr, start, outer_end,
        outshape.value, tcall, target).unpack()
        {
            lcx.data.func.code.set(p, Ins::MOV(IRT_IDX, prefix));
        }
    }
    prefix = match lcx.tmp[fuse] {
        VGETIdx { expr, axis, span, .. } if expr.is_nil() => emitsplatloop(lcx, loop_, target,
            prefix, tcall, axis as _, (axis+span) as _),
        VGETIdx { expr, .. } => emitexpri(lcx, expr, loop_, None)
    };
    let mut slot = ExprSlot { value: InsId::INVALID.into(), ctr: loop_.body };
    let flat = visitvgetinner(
        lcx,
        Visit::Materialize(&mut slot),
        fuse.add(1),
        end,
        objs[ann.cast::<TTEN>()].elem,
        var,
        inline,
        fwdload
    );
    lcx.data.func.code.set(flat, Ins::MOV(IRT_IDX, prefix));
    loop_.body = slot.ctr;
    slot.value
}

fn visitvget(lcx: &mut Lcx, expr: ObjRef<VGET>, mut visit: Visit) {
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    let vget = &objs[expr];
    let base = lcx.tmp.end();
    let fwdload = maybefwdvget(lcx, vget);
    if fwdload.is_none() {
        // TODO: the forwarding logic could be more general, e.g. consider
        //   table a[...]
        //   table b[:,...]
        //   model a b.xs = ...
        //   model global y = b.xs
        // this could be lowered as an outer loop + forwarded tail part instead of an inner loop
        vgetidx(&lcx.data, objs, vget, lcx.tmp.align_for());
    }
    let idx_start: BumpRef<VGETIdx> = base.cast_up();
    let idx_end: BumpRef<VGETIdx> = lcx.tmp.end().cast();
    let var = vardata(&lcx.data.objs, vget.var);
    let target = &bump[bump[var].tab];
    let source = &bump[lcx.data.tab];
    let nprefix = prefixlen(source.axes.len(), target.axes.len(), vget.dim as _);
    let prefix = idxtransfer(lcx, lcx.data.tab, bump[var].tab, source.axes.len(), nprefix, INS_FLATIDX);
    let inline = isdisjointidx(&bump[lcx.data.tab], target, &vget.idx);
    if let Visit::Iterate(iter) = visit.reborrow_mut() {
        if let Some(fuseidx) = maybefusevget(&lcx.tmp[base.cast()..idx_end]) {
            iter.element = emitvgetfuse(
                lcx,
                &mut iter.loop_,
                iter.shape.as_mut(),
                idx_start,
                idx_end,
                idx_start.add(fuseidx),
                vget.ann,
                vget.var,
                inline,
                fwdload,
                prefix
            );
        } else {
            iter.element = emitexprmi(lcx, expr.cast(), &mut iter.loop_, iter.shape.as_mut());
        }
    } else {
        let flat = visitvgetinner(lcx, visit, idx_start, idx_end, vget.ann, vget.var, inline, fwdload);
        lcx.data.func.code.set(flat, Ins::MOV(IRT_IDX, prefix));
    };
    lcx.tmp.truncate(base);
}

fn emitcat(lcx: &mut Lcx, expr: ObjRef<CAT>, ctr: &mut InsId) -> InsId {
    let objs = Access::borrow(&lcx.objs);
    let &CAT { ann, ref elems, .. } = &objs[expr];
    debug_assert!(objs[ann].op == Obj::TTEN);
    let cty: &TTEN = &objs[ann.cast()];
    if cty.dim != 1 { todo!() }
    let eds = decomposition_size(objs, cty.elem);
    let ptrs = reserve(&lcx.data.func, eds);
    let esizes = reserve(&lcx.data.func, eds);
    let mut idx: InsId = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    let mut fx: IndexOption<InsId> = None.into();
    let mut eloop: Option<(/*enter:*/Ins, /*exit:*/InsId)> = None;
    for &e in elems {
        let (stores, shape) = match objs[e].op {
            Obj::SPLAT => {
                let mut loop_ = newloop(&lcx.data.func);
                let e = objs[e.cast::<SPLAT>()].value;
                let (element, shape) = emitexpris(lcx, e, &mut loop_, ctr);
                let dest = reserve(&lcx.data.func, eds);
                for i in 0..eds as isize {
                    let ofs = lcx.data.func.code.push(Ins::MUL(IRT_IDX, idx, esizes+i));
                    lcx.data.func.code.set(dest+i, Ins::ADDP(ptrs+i, ofs));
                }
                let stores = emitloopstore(&lcx.data.func, &mut loop_, element, esizes, dest, eds);
                let (enter, exit) = closeloop(&lcx.data.func, loop_);
                match &mut eloop {
                    Some((_, prev_exit)) => lcx.data.func.code.set(replace(prev_exit, exit), enter),
                    None => eloop = Some((enter, exit))
                }
                (stores, shape)
            },
            _ => {
                let value = emitexprv(lcx, e, ctr);
                let stores = emitmultistore(&lcx.data.func, ptrs, esizes, idx, value, eds);
                let shape = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
                (stores, shape)
            }
        };
        idx = lcx.data.func.code.push(Ins::ADD(IRT_IDX, idx, shape));
        fx = Some(match fx.unpack() {
            Some(fx) => lcx.data.func.code.extend(
                (0..eds as isize).map(|j| Ins::MOVF(Type::FX, fx+j, stores+j))),
            None => stores
        }).into();
    }
    let base = lcx.tmp.end();
    for (i, ty) in decomposition(&lcx.objs, cty.elem, &mut lcx.tmp).iter().enumerate() {
        lcx.data.func.code.set(esizes + i as isize, Ins::KINT(IRT_IDX, ty.size() as _));
        let size = lcx.data.func.code.push(Ins::MUL(IRT_IDX, idx, esizes + i as isize));
        lcx.data.func.code.set(ptrs + i as isize, Ins::ALLOC(size, esizes + i as isize, *ctr));
    }
    if let Some((enter, exit)) = eloop {
        lcx.data.func.code.set(replace(ctr, exit), enter);
    }
    lcx.tmp.truncate(base);
    let ret = match fx.unpack() {
        Some(fx) => lcx.data.func.code.extend(
            (0..eds as isize).map(|i| Ins::MOVF(Type::PTR, ptrs+i, fx+i))),
        None => lcx.data.func.code.extend((0..eds as isize).map(|i| Ins::MOV(Type::PTR, ptrs+i)))
    };
    lcx.data.func.code.push(Ins::MOV(IRT_IDX, idx));
    ret
}

fn visitcat(lcx: &mut Lcx, expr: ObjRef<CAT>, visit: Visit) {
    match visit {
        Visit::Materialize(slot) => {
            slot.value = emitcat(lcx, expr, &mut slot.ctr);
        },
        Visit::Shape(slot) => {
            let objs = Access::borrow(&lcx.objs);
            let mut len = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
            for &e in &objs[expr].elems {
                let s = emitexprs(lcx, e, &mut slot.ctr);
                len = lcx.data.func.code.push(Ins::ADD(IRT_IDX, len, s));
            }
            slot.value = len;
        },
        _ => unreachable!()
    }
}

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
    func.code.set(replace(ctr, merge), Ins::IF(left, ri, other));
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

fn visitbinop(lcx: &mut Lcx, expr: ObjRef<BINOP>, visit: Visit) {
    let objs = Access::borrow(&lcx.objs);
    let BINOP { binop, ann, left, right, .. } = objs[expr];
    match visit {
        Visit::Materialize(slot) if objs[ann].op == Obj::TTEN => {
            slot.value = emitexprim(lcx, expr.cast(), &mut slot.ctr);
        },
        Visit::Materialize(slot) => {
            let l = emitexprv(lcx, left, &mut slot.ctr);
            let r = emitexprv(lcx, right, &mut slot.ctr);
            slot.value = emitscalarbinop(lcx, &mut slot.ctr, BinOp::from_u8(binop),
                Primitive::from_u8(objs[ann.cast::<TPRI>()].ty), l, r);
        },
        Visit::Shape(slot) => {
            let (a, b) = if objs[objs[right].ann].op == Obj::TPRI { (left, right) } else { (right, left) };
            visitexpr(lcx, b, Visit::None(&mut slot.ctr));
            slot.value = emitexprs(lcx, a, &mut slot.ctr);
        },
        Visit::Iterate(iter) => {
            let (ls, rs) = match objs[objs[right].ann].op {
                Obj::TPRI => (iter.shape.as_mut(), None),
                _ => (None, iter.shape.as_mut())
            };
            let l = emitbroadcastv(lcx, left, &mut iter.loop_, ls);
            let r = emitbroadcastv(lcx, right, &mut iter.loop_, rs);
            iter.element = emitscalarbinop(lcx, &mut iter.loop_.body, BinOp::from_u8(binop),
                elementtype(objs, ann), l, r);
        },
        Visit::None(ctr) => {
            visitexpr(lcx, left, Visit::None(ctr));
            visitexpr(lcx, right, Visit::None(ctr));
        }
    }
}

fn emitscalarintrinsic(lcx: &mut Lcx, intr: Intrinsic, arg: InsId, ty: Type) -> InsId {
    use Intrinsic::*;
    match intr {
        UNM|NOT => lcx.data.func.code.push(Ins::NEG(ty, arg)),
        EXP     => todo!(),
        LOG     => todo!(),
        _       => unreachable!()
    }
}

fn visitbroadcastintrinsic(lcx: &mut Lcx, expr: ObjRef<INTR>, mut visit: Visit) {
    let INTR { ann, func, args: [arg], .. } = lcx.objs[expr] else { unreachable!() };
    match visit.reborrow_mut() {
        Visit::Materialize(slot) if lcx.objs[ann].op == Obj::TTEN => {
            slot.value = emitexprim(lcx, expr.cast(), &mut slot.ctr);
        },
        Visit::Materialize(slot) => {
            let v = emitexprv(lcx, arg, &mut slot.ctr);
            slot.value = emitscalarintrinsic(lcx, Intrinsic::from_u8(func), v,
                Primitive::from_u8(lcx.objs[ann.cast::<TPRI>()].ty).to_ir());
        },
        Visit::Iterate(iter) => {
            let v = emitexpri(lcx, arg, &mut iter.loop_, iter.shape.as_mut());
            iter.element = emitscalarintrinsic(lcx, Intrinsic::from_u8(func), v,
                elementtype(&lcx.objs, ann).to_ir());
        },
        Visit::Shape(_) | Visit::None(_) => {
            visitexpr(lcx, arg, visit);
        }
    }
}

fn emitsum(func: &Func, loop_: &mut Loop, element: InsId, ty: Type) -> InsId {
    let [accumulator, result] = areserve(func);
    let init = func.code.push(Ins::KINT(ty, 0));
    let next = func.code.push(Ins::ADD(ty, accumulator, element));
    emitreduce(func, loop_, ty, init, next, accumulator, result);
    result
}

fn emitanyall(func: &Func, loop_: &mut Loop, element: InsId, f: Intrinsic) -> InsId {
    let resphi = func.phis.push(Phi::new(Type::B1));
    let default = func.code.push(Ins::KINT(Type::B1, (f == Intrinsic::ALL) as _));
    let notdefault = func.code.push(Ins::KINT(Type::B1, (f == Intrinsic::ANY) as _));
    emitloopinit(func, loop_, resphi, default);
    let found = func.code.push(Ins::JMP(notdefault, loop_.exit, resphi));
    let [body] = areserve(func);
    func.code.set(replace(&mut loop_.body, body), if f == Intrinsic::ALL {
        Ins::IF(element, body, found)
    } else {
        Ins::IF(element, found, body)
    });
    func.code.push(Ins::PHI(Type::B1, loop_.exit, resphi))
}

fn visitreduceintrinsic(
    lcx: &mut Lcx,
    intr: Intrinsic,
    ty: Type,
    arg: ObjRef<EXPR>,
    mut visit: Visit
) {
    match visit.reborrow_mut() {
        Visit::Materialize(slot) if lcx.objs[lcx.objs[arg].ann].op == Obj::TTEN => {
            let mut loop_ = newloop(&lcx.data.func);
            let element = emitexpri(lcx, arg, &mut loop_, None);
            slot.value = match intr {
                Intrinsic::SUM => emitsum(&lcx.data.func, &mut loop_, element, ty),
                Intrinsic::ANY | Intrinsic::ALL => emitanyall(&lcx.data.func, &mut loop_, element, intr),
                _ => unreachable!()
            };
            ctrcloseloop(&lcx.data.func, loop_, &mut slot.ctr);
        },
        Visit::Materialize(_) | Visit::None(_) => {
            visitexpr(lcx, arg, visit);
        },
        Visit::Iterate(_) | Visit::Shape(_) => unreachable!(),
    }
}

fn emitwhich(
    func: &Func,
    loop_: &mut Loop,
    arg_element: InsId,
    want_value: Option<(/*out:*/&mut InsId, /*shape:*/InsId, /*anchor:*/InsId)>,
    want_shape: Option<&mut InsId>
) {
    debug_assert!(want_value.is_some() || want_shape.is_some());
    let [merge, idx_accumulator] = areserve(func);
    let body = replace(&mut loop_.body, merge);
    let buf_result = match want_value { Some(_) => reserve(func, 1), None => InsId::INVALID.into() };
    let [idx_result] = areserve(func); // must come right after buf_result
    let next_idxphi = func.phis.push(Phi::new(IRT_IDX));
    let zero = func.code.push(Ins::KINT(IRT_IDX, 0));
    let one = func.code.push(Ins::KINT(IRT_IDX, 1));
    let next_idx_true = func.code.push(Ins::ADD(IRT_IDX, idx_accumulator, one));
    let mut branch_true = func.code.push(Ins::JMP(next_idx_true, merge, next_idxphi));
    let mut branch_false = func.code.push(Ins::JMP(idx_accumulator, merge, next_idxphi));
    if let Some(out) = want_shape {
        *out = idx_result;
    }
    if let Some((out, arg_shape, anchor)) = want_value {
        *out = buf_result;
        let idxsize = func.code.push(Ins::KINT(IRT_IDX, IRT_IDX.size() as _));
        let size = func.code.push(Ins::MUL(IRT_IDX, arg_shape, idxsize));
        let buf = func.code.push(Ins::ALLOC(size, idxsize, anchor));
        let [store_accumulator, store_result] = areserve(func);
        func.code.set(buf_result, Ins::MOVF(Type::PTR, buf, store_result));
        let nop = func.code.push(Ins::NOP(Type::FX));
        let offset = func.code.push(Ins::MUL(IRT_IDX, idx_accumulator, idxsize));
        let ptr = func.code.push(Ins::ADDP(buf, offset));
        let j = emitcounter(func, loop_, IRT_IDX);
        let store = func.code.push(Ins::STORE(ptr, j));
        let store = func.code.push(Ins::MOVF(Type::FX, store, store_accumulator));
        let storephi = func.phis.push(Phi::new(Type::FX));
        branch_true = func.code.push(Ins::JMP(store, branch_true, storephi));
        branch_false = func.code.push(Ins::JMP(store_accumulator, branch_false, storephi));
        let next_store = func.code.push(Ins::PHI(Type::FX, merge, storephi));
        emitreduce(func, loop_, Type::FX, nop, next_store, store_accumulator, store_result);
    }
    func.code.set(body, Ins::IF(arg_element, branch_true, branch_false));
    let next_idx = func.code.push(Ins::PHI(IRT_IDX, merge, next_idxphi));
    emitreduce(func, loop_, IRT_IDX, zero, next_idx, idx_accumulator, idx_result);
}

fn visitwhich(lcx: &mut Lcx, expr: ObjRef<INTR>, visit: Visit) {
    let objs = Access::borrow(&lcx.objs);
    let &INTR { args: [arg], .. } = &objs[expr] else { unreachable!() };
    let is_materialize = visit.is_materialize();
    match visit {
        Visit::Materialize(slot) | Visit::Shape(slot) => {
            let mut loop_ = newloop(&lcx.data.func);
            if is_materialize {
                let (element, shape) = emitexpris(lcx, arg, &mut loop_, &mut slot.ctr);
                emitwhich(&lcx.data.func, &mut loop_, element,
                    Some((&mut slot.value, shape, slot.ctr)), None);
            } else {
                let element = emitexpri(lcx, arg, &mut loop_, None);
                emitwhich(&lcx.data.func, &mut loop_, element, None, Some(&mut slot.value));
            };
            ctrcloseloop(&lcx.data.func, loop_, &mut slot.ctr);
        },
        Visit::Iterate(iter) => {
            iter.element = emitexprmi(lcx, expr.cast(), &mut iter.loop_, iter.shape.as_mut());
        },
        Visit::None(ctr) => {
            visitexpr(lcx, arg, Visit::None(ctr));
        }
    }
}

// TODO: split these into their own nodes?
fn visitintrinsic(lcx: &mut Lcx, expr: ObjRef<INTR>, visit: Visit) {
    let objs = Access::borrow(&lcx.objs);
    let &INTR { ann, func, ref args, .. } = &objs[expr];
    let func = Intrinsic::from_u8(func);
    match func {
        Intrinsic::UNM | Intrinsic::NOT | Intrinsic::EXP | Intrinsic::LOG => {
            visitbroadcastintrinsic(lcx, expr, visit);
        },
        Intrinsic::SUM | Intrinsic::ANY | Intrinsic::ALL => {
            let &[arg] = args else { unreachable!() };
            let ObjectRef::TPRI(&TPRI { ty, .. }) = objs.get(ann) else { unreachable!() };
            visitreduceintrinsic(lcx, func, Primitive::from_u8(ty).to_ir(), arg, visit);
        },
        Intrinsic::WHICH => visitwhich(lcx, expr, visit),
        Intrinsic::CONV => todo!(),
        Intrinsic::REP => todo!()
    }
}

fn visitload(lcx: &mut Lcx, expr: ObjRef<LOAD>, visit: Visit) {
    let objs = Access::borrow(&lcx.objs);
    let &LOAD { ann, addr, ref shape, .. } = &objs[expr];
    let is_materialize = visit.is_materialize();
    match visit {
        Visit::Materialize(slot) if shape.is_empty() => {
            debug_assert!(objs[ann].op == Obj::TPRI);
            let value = emitexprv(lcx, addr, &mut slot.ctr);
            let ty = Primitive::from_u8(objs[ann.cast::<TPRI>()].ty).to_ir();
            slot.value = lcx.data.func.code.push(Ins::LOAD(ty, value));
        },
        Visit::Materialize(slot) | Visit::Shape(slot) => {
            debug_assert!(!shape.is_empty());
            debug_assert!(objs[ann].op == Obj::TTEN);
            let buf = reserve(&lcx.data.func, is_materialize as _);
            let nums = reserve(&lcx.data.func, shape.len()); // must come right after buf
            if is_materialize {
                slot.value = buf;
                let v = emitexprv(lcx, addr, &mut slot.ctr);
                lcx.data.func.code.set(buf, Ins::MOV(Type::PTR, v));
            } else {
                slot.value = nums;
                visitexpr(lcx, addr, Visit::None(&mut slot.ctr));
            }
            for (i, &e) in shape.iter().enumerate() {
                let ev = emitexprv(lcx, e, &mut slot.ctr);
                lcx.data.func.code.set(nums + i as isize, Ins::MOV(IRT_IDX, ev));
            }
        },
        _ => unreachable!() // short-circuited in emitexpr
    }
}

fn visitnew(lcx: &mut Lcx, expr: ObjRef<NEW>, visit: Visit) {
    let objs = Access::borrow(&lcx.objs);
    let &NEW { ann, ref shape, .. } = &objs[expr];
    debug_assert!(objs[ann].op == Obj::TTEN);
    let is_materialize = visit.is_materialize();
    match visit {
        Visit::Materialize(slot) | Visit::Shape(slot) => {
            let eds = match is_materialize {
                true => decomposition_size(objs, objs[ann.cast::<TTEN>()].elem),
                false => 0
            };
            let res = reserve(&lcx.data.func, eds + shape.len());
            slot.value = res;
            for (i, &e) in shape.iter().enumerate() {
                let ev = emitexprv(lcx, e, &mut slot.ctr);
                lcx.data.func.code.set(res + (eds + i) as isize, Ins::MOV(IRT_IDX, ev));
            }
            if is_materialize {
                let base = lcx.tmp.end();
                let deco = decomposition(&lcx.objs, lcx.objs[ann.cast::<TTEN>()].elem, &mut lcx.tmp);
                let len = emitshapelen(&lcx.data.func, res + eds as isize, shape.len());
                for (i,&ty) in deco.iter().enumerate() {
                    let size = lcx.data.func.code.push(Ins::KINT(IRT_IDX, ty.size() as _));
                    let num = lcx.data.func.code.push(Ins::MUL(IRT_IDX, len, size));
                    lcx.data.func.code.set(res + i as isize, Ins::ALLOC(num, size, slot.ctr));
                }
                lcx.tmp.truncate(base);
            }
        },
        _ => unreachable!()
    }
}

fn visitget(lcx: &mut Lcx, expr: ObjRef<GET>, visit: Visit) {
    let GET { ann, value, idx, .. } = lcx.objs[expr];
    debug_assert!(lcx.objs[lcx.objs[value].ann].op == Obj::TTUP);
    let is_materialize = visit.is_materialize();
    match visit {
        Visit::Materialize(slot) | Visit::Shape(slot) => {
            let mut v = emitexprv(lcx, value, &mut slot.ctr);
            let offset: usize = lcx.objs[lcx.objs[value].ann.cast::<TTUP>()].elems[..idx as usize]
                .iter()
                .map(|&e| decomposition_size(&lcx.objs, e))
                .sum();
            v += offset as isize;
            if !is_materialize {
                v = extractshape(&lcx.objs, v, &lcx.objs[ann.cast()]);
            }
            slot.value = v;
        },
        _ => unreachable!()
    }
}

fn visitcallx(lcx: &mut Lcx, expr: ObjRef<CALLX>, visit: Visit) {
    let objs = Access::borrow(&lcx.objs);
    let &CALLX { ann, lang, ref inputs, .. } = &objs[expr];
    let is_materialize = visit.is_materialize();
    match visit {
        Visit::Materialize(slot) | Visit::Shape(slot) => {
            let base = lcx.data.tmp_ins.len();
            for &input in inputs {
                let value = emitexprv(lcx, input, &mut slot.ctr);
                lcx.data.tmp_ins.push(value);
            }
            let lang = Lang::from_u8(lang);
            let mut value = {
                // safety: this casts (ignoring newtype wrappers):
                //   &mut Ccx<Lower> -> &mut Ccx<UnsafeCell<Lower>>
                let lcx: &mut CLcx = unsafe { core::mem::transmute(&mut *lcx) };
                let lower = Access::borrow(&lcx.data);
                lang.lower(lcx, slot.ctr, expr, &lower.func, &lower.tmp_ins[base..])
            };
            lcx.data.tmp_ins.truncate(base);
            if !is_materialize {
                value = extractshape(objs, value, &objs[ann.cast()]);
            }
            slot.value = value;
        },
        _ => unreachable!()
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
            emitexprc(lcx, size, &mut ctr, fail);
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
                    false => emitexprv(lcx, size, &mut ctr)
                };
                let [next] = areserve(&lcx.data.func);
                lcx.data.func.code.set(replace(&mut ctr, next), Ins::JMP(n, next, ret));
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
                let idxsize = lcx.data.func.code.push(Ins::KINT(IRT_IDX, IRT_IDX.size() as _));
                // emit F loop
                let (f, n) = {
                    let mut loop_ = newloop(&lcx.data.func);
                    let (element, shape) = emitexpris(lcx, size, &mut loop_, &mut ctr);
                    for j in 0..dim as isize {
                        lcx.data.func.code.set((nils-dim as isize)+j, Ins::MOV(IRT_IDX, shape+j));
                    }
                    let one = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
                    let flen = lcx.data.func.code.push(Ins::ADD(IRT_IDX, xlen, one));
                    let fbytes = lcx.data.func.code.push(Ins::MUL(IRT_IDX, flen, idxsize));
                    let alloc = lcx.data.func.code.push(Ins::ALLOC(fbytes, idxsize, ctr));
                    let alloc1 = lcx.data.func.code.push(Ins::ADDP(alloc, idxsize));
                    let [cursor_accumulator, cursor_result] = areserve(&lcx.data.func);
                    let cursor_init = lcx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
                    let cursor_next = lcx.data.func.code.push(
                        Ins::ADD(IRT_IDX, cursor_accumulator, element));
                    emitreduce(&lcx.data.func, &mut loop_, IRT_IDX, cursor_init, cursor_next,
                        cursor_accumulator, cursor_result);
                    let store_result = emitloopstore(&lcx.data.func, &mut loop_, cursor_next,
                        idxsize, alloc1, 1);
                    let store_first = lcx.data.func.code.push(Ins::STORE(alloc, zero));
                    let store_result = lcx.data.func.code.push(Ins::MOVF(Type::FX, store_result,
                            store_first));
                    let buf_result = lcx.data.func.code.push(Ins::MOVF(Type::PTR, alloc, store_result));
                    ctrcloseloop(&lcx.data.func, loop_, &mut ctr);
                    (buf_result, cursor_result)
                };
                // emit B loop
                let b = {
                    let mut outerloop = newloop(&lcx.data.func);
                    let mut innerloop = newloop(&lcx.data.func);
                    // skip first element of f (zero)
                    let f = lcx.data.func.code.push(Ins::ADDP(f, idxsize));
                    let bbytes = lcx.data.func.code.push(Ins::MUL(IRT_IDX, n, idxsize));
                    let alloc = lcx.data.func.code.push(Ins::ALLOC(bbytes, idxsize, ctr));
                    let start_phi = lcx.data.func.phis.push(Phi::new(IRT_IDX));
                    emitloopinit(&lcx.data.func, &mut outerloop, start_phi, zero);
                    let i = emitrangeloop(&lcx.data.func, &mut outerloop, IRT_IDX, zero, xlen);
                    let fi = emitarrayptr(&lcx.data.func, f, i, IRT_IDX);
                    let end = lcx.data.func.code.push(Ins::LOAD(IRT_IDX, fi));
                    let start = lcx.data.func.code.push(
                        Ins::PHI(IRT_IDX, outerloop.body_entry, start_phi));
                    let j = emitrangeloop(&lcx.data.func, &mut innerloop, IRT_IDX, start, end);
                    let bj = emitarrayptr(&lcx.data.func, alloc, j, IRT_IDX);
                    let inner_store = lcx.data.func.code.push(Ins::STORE(bj, i));
                    let [
                        inner_store_accumulator,
                        inner_store_result,
                        outer_store_accumulator,
                        outer_store_result,
                        outer_tail
                    ] = areserve(&lcx.data.func);
                    let store_init = lcx.data.func.code.push(Ins::NOP(Type::FX));
                    let inner_store_next = lcx.data.func.code.push(
                        Ins::MOVF(Type::FX, inner_store, inner_store_accumulator));
                    emitreduce(&lcx.data.func, &mut innerloop, Type::FX, store_init, inner_store_next,
                        inner_store_accumulator, inner_store_result);
                    ctrcloseloop(&lcx.data.func, innerloop, &mut outerloop.body);
                    lcx.data.func.code.set(replace(&mut outerloop.tail, outer_tail),
                        Ins::JMP(end, outer_tail, start_phi));
                    let outer_store_next = lcx.data.func.code.push(
                        Ins::MOVF(Type::FX, outer_store_accumulator, inner_store_result));
                    emitreduce(&lcx.data.func, &mut outerloop, Type::FX, store_init,
                        outer_store_next, outer_store_accumulator, outer_store_result);
                    ctrcloseloop(&lcx.data.func, outerloop, &mut ctr);
                    lcx.data.func.code.push(Ins::MOVF(Type::PTR, alloc, outer_store_result))
                };
                let [next] = areserve(&lcx.data.func);
                let jump = lcx.data.func.code.push(Ins::JMP(f, next, ret));
                lcx.data.func.code.set(replace(&mut ctr, next), Ins::JMP(b, jump, ret+1));
                len = Some(n).into();
            }
        };
    }
    let len = len.unpack().unwrap_or(zero);
    lcx.data.func.code.set(ctr, Ins::JMP(len, ret, 0.into()));
}

/* ---- Initializers -------------------------------------------------------- */

fn emitcinit(lcx: &mut Lcx, tab: BumpRef<Tab>, chunk: FuncId) {
    let cinit = match lcx.data.bump[tab].axes.is_empty() {
        true => lcx.data.func.code.push(Ins::NOP(Type::FX)),
        false => {
            let tabcall = emittabcall(&lcx.data.func, lcx.data.bump[tab].func);
            let size = lcx.data.func.code.push(Ins::RES(IRT_IDX, tabcall, 0.into()));
            lcx.data.func.code.push(Ins::CINIT(size, chunk))
        }
    };
    let ret = lcx.data.func.code.push(Ins::RET());
    lcx.data.func.code.set(INS_ENTRY, Ins::JMP(cinit, ret, 0.into()));
}

/* ---- Variables ----------------------------------------------------------- */

fn emitvararms(lcx: &mut Lcx, var: BumpRef<Var>) {
    let mut ctr = INS_ENTRY;
    let ret = lcx.data.func.code.push(Ins::RET());
    let bump = Access::borrow(&lcx.data.bump);
    let objs = Access::borrow(&lcx.objs);
    for (i, &setter) in bump[var].value.iter().enumerate() {
        let vset = &bump[setter];
        let model = &bump[vset.model];
        let [next] = areserve(&lcx.data.func);
        match vset.vst {
            VSet::SIMPLE => {
                let mobj = &objs[model.obj];
                if !mobj.guard.is_nil() {
                    let cond = emitexprcv(lcx, mobj.guard, &mut ctr, next);
                    emitjumpifnot(&lcx.data.func, &mut ctr, cond, next);
                }
                emitexprc(lcx, mobj.value, &mut ctr, next);
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
    let objs = Access::borrow(&lcx.objs);
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
        let model = &bump[vset.model];
        let value = match vset.vst {
            VSet::SIMPLE => emitexprv(lcx, objs[model.obj].value, &mut ctr),
            VSet::PREFIX => {
                let modeldim = bump[model.tab].n as usize;
                let idx = idxtransfer(lcx, var.tab, model.tab, vardim, modeldim, INS_FLATIDX);
                let call = emitcallvm1(&lcx.data, idx, model.base + Mod::SUB_VALUE);
                if vsettype(objs, model.obj, vset.idx as _) == lcx.objs[var.obj].ann {
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

/* ---- Models -------------------------------------------------------------- */

// only non-simple models are handled here.
// simple models emit directly into the variable definition.

fn emitmodavail(lcx: &mut Lcx, model: BumpRef<Mod>) {
    let mut ctr = INS_ENTRY;
    let objs = Access::borrow(&lcx.objs);
    let mobj = &objs[lcx.data.bump[model].obj];
    let ret = lcx.data.func.code.push(Ins::RET());
    let kfal = lcx.data.func.code.push(Ins::KINT(Type::B1, 0));
    let jfal = lcx.data.func.code.push(Ins::JMP(kfal, ret, 0.into()));
    if !mobj.guard.is_nil() {
        let cond = emitexprcv(lcx, mobj.guard, &mut ctr, jfal);
        emitjumpifnot(&lcx.data.func, &mut ctr, cond, jfal);
    }
    emitexprc(lcx, mobj.value, &mut ctr, jfal);
    for &setter in &mobj.outputs {
        for &e in &objs[setter].idx {
            emitexprc(lcx, e, &mut ctr, jfal);
        }
    }
    let ktru = lcx.data.func.code.push(Ins::KINT(Type::B1, 1));
    lcx.data.func.code.set(ctr, Ins::JMP(ktru, ret, 0.into()));
}

fn emitmodvalue(lcx: &mut Lcx, model: BumpRef<Mod>) {
    let mut ctr = INS_ENTRY;
    let objs = Access::borrow(&lcx.objs);
    let mobj = &objs[lcx.data.bump[model].obj];
    // TODO: optimization: for full table VSET (ie. empty idx) return only the pointer,
    // and on use load the shape from the tab instead
    let value = emitexprv(lcx, mobj.value, &mut ctr);
    for i in 0..decomposition_size(objs, mobj.value.erase()) {
        let [next] = areserve(&lcx.data.func);
        lcx.data.func.code.set(ctr, Ins::JMP(value + i as isize, next, i.into()));
        ctr = next;
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
        let mut v = emitexprcv(lcx, value, &mut ctr, fail);
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
                let mut func = Func::new(FuncKind::Query(query),
                    DebugSource::new(obj, EnumSet::empty()));
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
                                ccx.data.bump[model.outputs[0].var].base
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
            locals: Default::default(),
            tmp_ins: Default::default(),
            tmp_vty: Default::default(),
            tmp_ty: Default::default(),
            func: Access::new(Func::new(FuncKind::User(),
                DebugSource::new(ObjRef::NIL, EnumSet::empty()))),
            tab: BumpRef::zero(),
            check: None.into()
        })
    }

    fn run(ccx: &mut Ccx<Lower>) -> compile::Result {
        collectobjs(ccx);
        emitobjs(unsafe { core::mem::transmute(&mut *ccx) });
        if trace!(LOWER) {
            let mut tmp = Default::default();
            dump_ir(&mut tmp, &ccx.ir, &ccx.intern, &ccx.objs);
            trace!("{}", core::str::from_utf8(tmp.as_slice()).unwrap());
        }
        ccx.freeze_graph(computereset);
        Ok(())
    }

}
