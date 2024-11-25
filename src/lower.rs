//! Graph -> IR.

use core::cmp::{max, min};
use core::iter::zip;
use core::mem::take;

use enumset::{EnumSet, EnumSetType};

use crate::bump::{self, Bump, BumpRef};
use crate::compile::{self, Ccx, Phase};
use crate::dump::dump_ir;
use crate::hash::{HashMap, ValueHashMap};
use crate::index::{IndexOption, IndexValueVec, InvalidValue, ValueVec};
use crate::intrinsics::Intrinsic;
use crate::ir::{self, Bundle, Code, Func, FuncId, FuncKind, Ins, InsId, Opcode, Phi, PhiId, Query, SignatureBuilder, Type, IR};
use crate::mem::{Offset, SizeClass};
use crate::obj::{cast_args, Obj, ObjRef, ObjectRef, Objects, Operator, CALLN, DIM, EXPR, KINT, MOD, QUERY, TAB, TCON, TDIM, TPRI, VAR, VGET, VSET};
use crate::trace::trace;
use crate::typestate::{Absent, Access, R, RW};
use crate::typing::{Constructor, Primitive};

macro_rules! define_objs {
    (
        $(
            $name:ident
            { $($field:ident : $type:ty),* }
            $( $vla:ident : [$vty:ty] )?
            ;
        )*
    ) => {
        $(
            #[repr(C, align(4))]
            struct $name $(<T: ?Sized = [$vty]>)? {
                $($field:$type,)*
                $( $vla: T )?
            }
            unsafe impl bump::ReadBytes for $name {}
            unsafe impl bump::WriteBytes for $name {}
            $(
                unsafe impl bump::ReadBytes for $name<()> {}
                unsafe impl bump::WriteBytes for $name<()> {}
                unsafe impl bump::Aligned for $name<[$vty]> { const ALIGN: usize = 4; }
                unsafe impl bump::Read for $name<[$vty]> {
                    fn read(base: *const u8, ptr: usize, len: usize) -> *const Self {
                        if ptr + core::mem::size_of::<$name<()>>() < len {
                            let n = unsafe { (*(base.add(ptr) as *const $name<()>)).n } as usize;
                            let p = unsafe {
                                bump::trailing_vla_ptr::<$name<()>, $vty>(base, ptr, len, n)
                            };
                            p as _
                        } else {
                            (&[]) as *const [u8] as *const _
                        }
                    }
                }
            )?
        )*
    };
}

// safety:
//   * all types below must not have padding bytes (with repr(C, align(4)))
//     (sort fields in descending size order so this is easier to check)
//   * all field types must have alignment at most 4
//   * all field types must be castable to/from raw bytes
//   * all structs with a trailing vla must contain an `n: u8`
define_objs! {

    Tab {
        func: FuncId,
        n: u8,
        _pad: u8
    } axes: [Axis];

    Axis {
        size: ObjRef<EXPR>,
        ret: PhiId,
        rank: u8,
        _pad: u8
    };

    Var {
        obj: ObjRef<VAR>,
        tab: BumpRef<Tab>,
        vty: VType,
        base: FuncId,
        n: u8,
        _pad: u8
    } def: [BumpRef<VSet>];

    Mod {
        tab: BumpRef<Tab>,
        guard: ObjRef<EXPR>,
        base: FuncId,
        n: u8,
        mt: u8
    } value: [VSet];

    VSet {
        obj: ObjRef<VSET>,
        model: BumpRef<Mod>,
        var: BumpRef<Var>,
        vty: VType,
        ret: PhiId,
        vst: u8,
        _pad: u8
    };

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

// type of a value: n[K-1]-rank tensor of n[K-2] rank tensor of ... of n[0]-rank tensor of pri.
// a rank-0 vtype (scalar) is represented as one IR value: `pri`.
// a rank-K vtype is represented as 1+n[0]+...+n[K-1] IR values, where:
//   irt(K,i) = ptr[irt(K-1,i)]  where 0 <= i < 1+n[0]+...+n[K-2],
//   irt(K,i) = idx where 1+n[0]+...+n[K-2] <= i <= 1+n[0]...+n[K-1]
// this struct allows max 3 levels of nesting, which should be enough for any realistic program.
#[derive(Clone, Copy)]
#[repr(align(4))]
struct VType {
    pri: Primitive,
    dim: [u8; 3]
}

impl VType {

    fn scalar(pri: Primitive) -> Self {
        Self { pri, dim: Default::default() }
    }

    fn is_scalar(self) -> bool {
        self.dim[0] == 0
    }

    fn k(self) -> usize {
        self.dim.into_iter().position(|n| n == 0).unwrap_or(self.dim.len())
    }

    fn wrap(self, n: u8) -> Self {
        debug_assert!(n > 0);
        let mut ns = self.dim;
        // TODO: return a compiler error if k is too high
        ns[self.k()] = n;
        Self { pri: self.pri, dim: ns }
    }

    fn peel(self) -> Self {
        debug_assert!(self.k() > 0);
        let mut ns = self.dim;
        ns[self.k()-1] = 0;
        Self { pri: self.pri, dim: ns }
    }

    fn iter_decomposition(self) -> impl Iterator<Item=Type> {
        let mut k = 0;
        let mut nptr = 0;
        let mut nidx = 0;
        for ni in self.dim.into_iter() {
            if ni == 0 { break; }
            nptr += nidx;
            k += 1;
            nidx = ni;
        }
        core::iter::once(match k { 0 => self.pri.to_ir(), _ => Type::PTR })
            .chain((0..nptr).map(|_| Type::PTR))
            .chain((0..nidx).map(|_| IRT_IDX))
    }

    fn decomposition_size(self) -> usize {
        1 + self.dim.into_iter().map(|n| n as usize).sum::<usize>()
    }

    fn dim(self) -> u8 {
        self.dim.into_iter().rev().find(|n| *n > 0).unwrap_or(0)
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

struct FuncBuilder {
    code: Code,
    phis: IndexValueVec<PhiId, Phi>,
    ret: PhiId,
    cur: FuncId
}

impl Default for FuncBuilder {
    fn default() -> Self {
        Self {
            code: Default::default(),
            phis: Default::default(),
            ret: 0.into(),
            cur: FuncId::INVALID.into()
        }
    }
}

#[repr(C)] // need repr(C) for transmuting references
pub struct Lower<O=RW> {
    bump: Bump<u32>,
    objs: Access<HashMap<ObjRef, BumpRef<()>>, O>,
    expr: ValueHashMap<ObjRef<EXPR>, (FuncId, InsId)>,
    tmp_ins: ValueVec<InsId>,
    // current function:
    func: FuncBuilder,
    tab: BumpRef<Tab>,
}

type Ctx<'a> = Ccx<Lower<R<'a>>>;

// integer type used for indexing
const IRT_IDX: Type = Type::I32;
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

fn vtypeann(objs: &Objects, ann: ObjRef) -> VType {
    match objs.get(toann(objs, ann)) {
        ObjectRef::TPRI(&TPRI { ty, .. }) => VType::scalar(Primitive::from_u8(ty)),
        ObjectRef::TCON(&TCON { con: Constructor::TENSOR, args: [ty, dim], .. }) => {
            debug_assert!(objs[dim].op == Obj::TDIM);
            vtypeann(objs, ty).wrap(objs[dim.cast::<TDIM>()].dim)
        },
        _ => unreachable!()
    }
}

fn isscalarann(objs: &Objects, ann: ObjRef) -> bool {
    objs[toann(objs, ann)].op == Obj::TPRI
}

fn createtab(ctx: &mut Ccx<Lower, R>, idx: ObjRef<TAB>, obj: &TAB) {
    let axes = &ctx.objs[obj.shape].fields;
    ctx.data.bump.push(&Tab {
        func: ctx.ir.funcs.end(),
        n: axes.len() as _,
        _pad: 0,
        axes: ()
    });
    let mut ret: PhiId = 1.into();
    let mut func = Func::new(FuncKind::Bundle(Bundle::new(SizeClass::GLOBAL)));
    let mut sig = func.build_signature().add_return(IRT_IDX);
    for &size in axes {
        let rank = min(vtypeann(&ctx.objs, size.erase()).k() as u8, 1);
        ctx.data.bump.push(&Axis { size, ret, rank, _pad: 0 });
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
    let vty = vtypeann(&ctx.objs, var.ann);
    let base = ctx.ir.funcs.end();
    lower.bump.push(&Var {
        obj: idx.cast(),
        tab: lower.objs[&var.tab.erase()].cast(),
        vty,
        base,
        n: 0, // will be used as a counter for vsets
        _pad: 0,
        def: ()
    });
    lower.bump.push_zeroed_slice::<BumpRef<VSet>>(var.mark as _);
    let scl = sizeclass(&ctx.objs, var.tab);
    // value:
    {
        let mut func = Func::new(FuncKind::Bundle(Bundle::new(scl)));
        let mut sig = func.build_signature();
        for ty in vty.iter_decomposition() {
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
    let model: BumpRef<Mod> = lower.bump.push(&Mod {
        tab: lower.objs[&obj.tab.erase()].cast(),
        guard: obj.guard,
        base,
        n: obj.value.len() as _,
        mt,
        value: ()
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
        let vty = vtypeann(&ctx.objs, vset.value.erase());
        let ptr = lower.bump.push(&VSet { obj: setter, model, var, vty, ret, vst, _pad: 0 });
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
        ret += vty.decomposition_size() as isize;
    }
    // create functions for complex models only
    if mt == Mod::COMPLEX {
        let scl = sizeclass(&ctx.objs, obj.tab);
        // value:
        {
            let mut func = Func::new(FuncKind::Bundle(Bundle::new(scl)));
            let mut sig = func.build_signature();
            for vset in &lower.bump[model].value {
                for ty in vset.vty.iter_decomposition() {
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
            let bp = ctx.data.bump.next();
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

fn emitarg(func: &FuncBuilder, idx: usize) -> InsId {
    let phi = func.ret + idx as isize;
    func.code.push(Ins::PHI(func.phis.at(phi).type_, InsId::START, phi))
}

fn reserve(func: &FuncBuilder, num: usize) -> InsId {
    // FIXME repeat_n stabilizes in 1.82.0
    func.code.extend((0..num).map(|_| Ins::NOP_FX))
}

fn emitjumpifnot(func: &FuncBuilder, ctr: &mut InsId, cond: InsId, target: InsId) -> InsId {
    let next = reserve(func, 1);
    func.code.set(*ctr, Ins::IF(cond, next, target));
    *ctr = next;
    next
}

fn emitcallvm(func: &FuncBuilder, idx: InsId, node: FuncId, inline: bool) -> InsId {
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

fn emitcallvm1(func: &FuncBuilder, idx: InsId, node: FuncId) -> InsId {
    emitcallvm(func, idx, node, idx == INS_FLATIDX)
}

fn unpackattr(attrs: u8) -> EnumSet<IdxAttr> {
    EnumSet::from_u8_truncated(attrs)
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

fn emitrangeloop(func: &FuncBuilder, loop_: &mut LoopState, ty: Type, start: InsId, end: InsId) -> InsId {
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
    func: &FuncBuilder,
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

fn closereduce(func: &FuncBuilder, reduce: Reduce, next: InsId) -> InsId {
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
    ctx: &Ctx,
    tab: BumpRef<Tab>, // *target* table being indexed
    call: InsId,       // CALLB(I) of tab
    axis: usize,       // current axis (N)
    flat: InsId        // flat index for current axis (N)
) -> InsId {
    // note: if axis=0, then flat is either zero (the only valid index), or one (one past the last
    // valid index)
    let Axis { rank, ret, .. } = ctx.data.bump[tab].axes[axis];
    match rank {
        Axis::SCALAR => {
            let size = ctx.data.func.code.push(Ins::RES(IRT_IDX, call, ret));
            ctx.data.func.code.push(Ins::MUL(IRT_IDX, flat, size))
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
    ctx: &Ctx,
    tab: BumpRef<Tab>, // *target* table being indexed
    call: InsId,       // CALLB(I) of tab
    axis: usize,       // current axis (N+1)
    flat: InsId        // flat index for current axis (N+1)
) -> InsId {
    debug_assert!(axis > 0);
    if axis == 1 {
        // the only valid flat index for the zeroth axis is zero,
        // therefore back transforming anything to the zeroth axis yields zero.
        return ctx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    }
    let Axis { rank, ret, .. } = ctx.data.bump[tab].axes[axis-1];
    match rank {
        Axis::SCALAR => {
            let size = ctx.data.func.code.push(Ins::RES(IRT_IDX, call, ret));
            ctx.data.func.code.push(Ins::DIV(IRT_IDX, flat, size))
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
fn commonprefix(ctx: &Ctx, a: BumpRef<Tab>, b: BumpRef<Tab>) -> usize {
    if a == b { return ctx.data.bump[a].axes.len() }
    zip(ctx.data.bump[a].axes.iter(), ctx.data.bump[b].axes.iter())
        .take_while(|(a, b)| ctx.objs.equal(a.size.erase(), b.size.erase()))
        .count()
}

// do A and B have the exact same shape?
fn sametab(ctx: &Ctx, a: BumpRef<Tab>, b: BumpRef<Tab>) -> bool {
    commonprefix(ctx, a, b) == max(ctx.data.bump[a].n, ctx.data.bump[b].n) as usize
}

fn emittabcall(func: &FuncBuilder, tabf: FuncId) -> InsId {
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
    ctx: &Ctx,
    source: BumpRef<Tab>,
    target: BumpRef<Tab>,
    mut source_axis: usize,
    target_axis: usize,
    mut flat: InsId
) -> InsId {
    if target_axis == 0 {
        return ctx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
    }
    let prefix = commonprefix(ctx, source, target);
    let sourcecall = match source_axis > min(target_axis, prefix) {
        true  => emittabcall(&ctx.data.func, ctx.data.bump[source].func),
        false => InsId::INVALID.into()
    };
    let targetcall = match target_axis > min(source_axis, prefix) {
        true  => emittabcall(&ctx.data.func, ctx.data.bump[target].func),
        false => InsId::INVALID.into()
    };
    while source_axis > target_axis {
        flat = idxbtran(ctx, source, sourcecall, source_axis, flat);
        source_axis -= 1;
    }
    if source_axis > prefix {
        // here we have target_axis >= source_axis > prefix, due to the previous loop.
        // this necessarily implies source != target.
        // we must now transfer source_axis in `source` to source_axis in `target`.
        // base+i will hold the prefix+1+i'th NON-flat index.
        let source_axis0 = source_axis;
        let mut base = reserve(&ctx.data.func, source_axis-prefix);
        while source_axis > prefix {
            flat = idxbtran(ctx, source, sourcecall, source_axis, flat);
            source_axis -= 1;
            let start = idxftran(ctx, source, sourcecall, source_axis, flat);
            ctx.data.func.code.set(
                base + (source_axis-prefix) as isize,
                Ins::SUB(IRT_IDX, flat, start)
            );
        }
        while source_axis < source_axis0 {
            flat = idxftran(ctx, target, targetcall, source_axis, flat);
            flat = ctx.data.func.code.push(Ins::ADD(IRT_IDX, flat, base));
            base += 1;
            source_axis += 1;
        }
    }
    while source_axis < target_axis {
        flat = idxftran(ctx, target, targetcall, source_axis, flat);
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
    ctx: &Ctx,
    mut ctr: ControlFlow,
    tab: BumpRef<Tab>,
    idx: &[ObjRef<EXPR>],
    mut axis: usize,
    mut flat: InsId
) -> InsId {
    let dim = ctx.data.bump[tab].n as usize;
    debug_assert!(dim >= axis + idx.len());
    if axis == dim {
        // nothing to do here (skip emitting the tabcall).
        return flat;
    }
    let call = emittabcall(&ctx.data.func, ctx.data.bump[tab].func);
    let splat = dim - axis - idx.len();
    let mut inloop = false;
    for &i in idx {
        let j = match isscalarann(&ctx.objs, i.erase()) {
            true  => {
                let c = match &mut ctr {
                    ControlFlow::Straight(ctr) => ctr,
                    ControlFlow::Loop(loop_) => loop_.ctr(inloop)
                };
                emitvalue(ctx, c, i)
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
                emititer(ctx, loop_, i)
            }
        };
        flat = idxftran(ctx, tab, call, axis, flat);
        flat = ctx.data.func.code.push(Ins::ADD(IRT_IDX, flat, j));
        axis += 1;
    }
    if splat > 0 {
        let one = ctx.data.func.code.push(Ins::KINT(IRT_IDX, 1));
        let mut start = flat;
        let mut end = ctx.data.func.code.push(Ins::ADD(IRT_IDX, start, one));
        while axis < dim {
            start = idxftran(ctx, tab, call, axis, start);
            end = idxftran(ctx, tab, call, axis, end);
            axis += 1;
        }
        let ControlFlow::Loop(loop_) = ctr else { unreachable!() };
        emitrangeloop(&ctx.data.func, loop_, IRT_IDX, start, end)
    } else {
        flat
    }
}

// given a target table and an index expression
//   tab[i1, ..., iM],
// emit the (full) flat index
//   tab[p1, ..., pN, i1, ..., iM, :, ..., :],
// where
//   N = min(dim(ctx.data.tab, dim(tab)-M))
// and p1, ..., pN is a flat (prefix) index for the current table.
fn emitidx(ctx: &Ctx, ctr: ControlFlow, tab: BumpRef<Tab>, idx: &[ObjRef<EXPR>]) -> InsId {
    let sdim = ctx.data.bump[ctx.data.tab].n as usize;
    let tdim = ctx.data.bump[tab].n as usize;
    if idx.len() == tdim || sdim == 0 {
        idxsuffix(ctx, ctr, tab, idx, 0, ctx.data.func.code.push(Ins::KINT(IRT_IDX, 0)))
    } else {
        let n = min(sdim, tdim-idx.len());
        let prefix = idxtransfer(ctx, ctx.data.tab, tab, sdim, n, INS_FLATIDX);
        idxsuffix(ctx, ctr, tab, idx, n, prefix)
    }
}

// given a target table and an index expression
//   tab[i1, ..., iN]
// emit the shape of the resulting tensor
fn emitidxshape(
    ctx: &Ctx,
    ctr: &mut InsId,
    target: BumpRef<Tab>,
    idx: &[ObjRef<EXPR>],
    ann: ObjRef
) -> InsId {
    let dim = vtypeann(&ctx.objs, ann).dim() as usize;
    let base = reserve(&ctx.data.func, dim);
    let mut axis = 0;
    for &i in idx {
        if !isscalarann(&ctx.objs, i.erase()) {
            // TODO: this only works for int arrays, not explicit splats, ranges, or bool arrays
            let ilen = emitlen(ctx, ctr, i);
            ctx.data.func.code.set(base + axis as isize, Ins::MOV(IRT_IDX, ilen));
            axis += 1;
        }
    }
    if axis < dim {
        let call = emittabcall(&ctx.data.func, ctx.data.bump[target].func);
        for &Axis { rank, ret, .. }
            in &ctx.data.bump[target].axes[ctx.data.bump[ctx.data.tab].n as usize + idx.len()..]
        {
            // vector axis here is a compiler error and should probably be detected earlier
            // (it doesn't make sense to collect dynamically shaped axes into a tensor because
            //  tensors are rectangular)
            debug_assert!(rank == Axis::SCALAR);
            ctx.data.func.code.set(base + axis as isize, Ins::RES(IRT_IDX, call, ret));
            axis += 1;
        }
    }
    debug_assert!(axis == dim);
    base
}

fn emitshapelen(func: &FuncBuilder, base: InsId, dim: usize) -> InsId {
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
    ctx: &Ctx,
    target: BumpRef<Tab>,
    source_axis: usize,
    idx: &[ObjRef<EXPR>],
    mut attrs: EnumSet<IdxAttr>
) -> EnumSet<IdxAttr> {
    if attrs.contains(IdxAttr::Disjoint) {
        // TODO: analyze explicit indices
        if !idx.is_empty() || source_axis > ctx.data.bump[target].n as usize {
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
fn emitlogic(func: &FuncBuilder, ctr: &mut InsId, left: InsId, right: InsId, op: Intrinsic) -> InsId {
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

// args passed in ctx.data.tmp_ins
fn emitscalarintrinsic(ctx: &Ctx, ctr: &mut InsId, f: Intrinsic, ty: Type) -> InsId {
    use Intrinsic::*;
    let args = &ctx.data.tmp_ins;
    match f {
        OR|AND => emitlogic(&ctx.data.func, ctr, args.at(0), args.at(1), f),
        ADD   => ctx.data.func.code.push(Ins::ADD(ty, args.at(0), args.at(1))),
        SUB   => ctx.data.func.code.push(Ins::SUB(ty, args.at(0), args.at(1))),
        MUL   => ctx.data.func.code.push(Ins::MUL(ty, args.at(0), args.at(1))),
        DIV   => todo!(), // handle signedness
        POW   => ctx.data.func.code.push(Ins::POW(ty, args.at(0), args.at(1))),
        EQ    => ctx.data.func.code.push(Ins::EQ(args.at(0), args.at(1))),
        NE    => ctx.data.func.code.push(Ins::NE(args.at(0), args.at(1))),
        LT    => todo!(), // handle signedness
        LE    => todo!(), // handle signedness
        UNM   => todo!(), // name it consistently UNM? NEG?
        EXP   => todo!(), // ir intrinsic call?
        LOG   => todo!(), // ir intrinsic call?
        NOT   => todo!(),
        CONV  => todo!(),
        _     => unreachable!() // non-scalar
    }
}

fn emitsum(ctx: &Ctx, ctr: &mut InsId, arg: ObjRef<EXPR>, ty: Type) -> InsId {
    if isscalarann(&ctx.objs, arg.erase()) {
        return emitvalue(ctx, ctr, arg);
    }
    let zero = ctx.data.func.code.push(Ins::KINT(ty, 0));
    let l_phi = ctx.data.func.phis.push(Phi::new(ty));
    let r_phi = ctx.data.func.phis.push(Phi::new(ty));
    let mut reduce = newreduce(&ctx.data.func, *ctr, l_phi, r_phi, zero, 1);
    let elem = emititer(ctx, &mut reduce.loop_, arg);
    let next = ctx.data.func.code.push(Ins::ADD(ty, reduce.value, elem));
    *ctr = reduce.loop_.out;
    closereduce(&ctx.data.func, reduce, next)
    // let out = reserve(&ctx.data.func, 5);
    // let tail = out+1;
    // let head = out+2;
    // let body0 = out+3;
    // let body = out+4;
    // let lphi = ctx.data.func.phis.push(Phi::new(ty)); // for body
    // let resphi = ctx.data.func.phis.push(Phi::new(ty)); // for out
    // let vbody = ctx.data.func.code.push(Ins::PHI(ty, body0, lphi));
    // ctx.data.func.code.set(body0, Ins::JMP(vbody, body, resphi));
    // ctx.data.func.code.set(*ctr, Ins::JMP(zero, head, resphi));
    // let mut loop_ = LoopState { head, tail, body, out };
    // let vadd = emititer(ctx, &mut loop_, arg);
    // let vnext = ctx.data.func.code.push(Ins::ADD(ty, vbody, vadd));
    // // crate::trace::trace!("emit sum merge={merge:?} body={body:?} tail={tail:?} out_head={out_head:?} out_loop={out_loop:?} vbody={vbody:?} loop_.head={:?} loop_.tail={:?} loop_.body={:?} lphi={lphi:?} resphi={resphi:?}", loop_.head, loop_.tail, loop_.body);
    // ctx.data.func.code.set(loop_.head, Ins::JMP(zero, body0, lphi));
    // ctx.data.func.code.set(loop_.tail, Ins::JMP(vnext, body0, lphi));
    // ctx.data.func.code.set(loop_.body, Ins::JMP(vnext, tail, resphi));
    // *ctr = out;
    // ctx.data.func.code.push(Ins::PHI(ty, out, resphi))
}

fn scalarintrinsic(
    ctx: &Ctx,
    ctr: &mut InsId,
    f: Intrinsic,
    args: &[ObjRef<EXPR>],
    ty: Type
) -> InsId {
    match f {
        Intrinsic::SUM => emitsum(ctx, ctr, args[0], ty),
        _ => {
            ctx.data.tmp_ins.clear();
            for &arg in args {
                ctx.data.tmp_ins.push(emitvalue(ctx, ctr, arg));
            }
            emitscalarintrinsic(ctx, ctr, f, ty)
        }
    }
}

fn broadcastintrinsic(
    ctx: &Ctx,
    loop_: &mut LoopState,
    f: Intrinsic,
    args: &[ObjRef<EXPR>],
    vty: VType
) -> InsId {
    ctx.data.tmp_ins.clear();
    for &arg in args {
        ctx.data.tmp_ins.push(emititer(ctx, loop_, arg));
    }
    if !vty.is_scalar() {
        // TODO: this *can* be implemented by materializing it here.
        // whether that's even useful is another question.
        // but it makes sense from the type system perspective
        // (+ :: (T,T) -> T regardless of whether T is scalar or tensor[U,N] or
        // tensor[tensor[U,N],M] or ... you get the idea)
        todo!()
    }
    emitscalarintrinsic(ctx, &mut loop_.body, f, vty.pri.to_ir())
}

fn emitvget1(ctx: &Ctx, ctr: &mut InsId, vget: &VGET) -> InsId {
    debug_assert!(vget.ann == ctx.objs[vget.var].ann);
    let var = vardata(&ctx.data.objs, vget.var);
    let i = emitidx(ctx, ControlFlow::Straight(ctr), ctx.data.bump[var].tab, &vget.idx);
    emitvarload(ctx, var, i, !idxanalyze(ctx, ctx.data.bump[var].tab,
            ctx.data.bump[ctx.data.tab].n as _, &vget.idx, IdxAttr::Disjoint.into()).is_empty())
}

fn materializescalar(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>, ty: Type) -> InsId {
    match ctx.objs.get(expr.erase()) {
        ObjectRef::KINT(&KINT { k, .. }) => ctx.data.func.code.push(Ins::KINT(ty, k as _)),
        ObjectRef::KREF(_) => todo!(),
        ObjectRef::DIM(&DIM { axis, .. }) => {
            debug_assert!(ty == IRT_IDX);
            idxtransfer(ctx, ctx.data.tab, ctx.data.tab, ctx.data.bump[ctx.data.tab].n as _,
                (axis+1) as _, INS_FLATIDX)
        },
        ObjectRef::VGET(vget) => emitvget1(ctx, ctr, vget),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(_) => todo!(),
        ObjectRef::GET(_) => todo!(),
        ObjectRef::FREF(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { func, ref args, .. }) =>
            scalarintrinsic(ctx, ctr, Intrinsic::from_u8(func), args, ty),
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn computeshape(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    match ctx.objs.get(expr.erase()) {
        ObjectRef::VGET(&VGET { var, ann, ref idx, .. }) => {
            let v = vardata(&ctx.data.objs, var);
            let tab = ctx.data.bump[v].tab;
            if ann == ctx.objs[var].ann {
                // scalar load of a vector variable
                let i = emitidx(ctx, ControlFlow::Straight(ctr), tab, idx);
                emitvarloadshape(ctx, v, i, i == INS_FLATIDX)
            } else {
                // vector load of a scalar variable
                emitidxshape(ctx, ctr, tab, idx, ann)
            }
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(_) => todo!(),
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { func, ref args, .. }) => {
            debug_assert!(Intrinsic::from_u8(func).is_broadcast());
            // TODO: in the case of multiple args, what SHOULD be done here is to compute the
            // shape for all args, and trap if they don't match.
            computeshape(ctx, ctr, args[0])
        },
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn materializecollect(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>, vt: VType) -> InsId {
    let shape = computeshape(ctx, ctr, expr);
    let len = emitshapelen(&ctx.data.func, shape, vt.dim() as _);
    let ety = vt.peel();
    let ds = ety.decomposition_size();
    // TODO: this needs some thinking because "hardcoding" the element size will make type
    // narrowing impossible in the future.
    let ptrs = reserve(&ctx.data.func, ds);
    let esizes = reserve(&ctx.data.func, ds);
    for (i, ty) in ety.iter_decomposition().enumerate() {
        ctx.data.func.code.set(esizes + i as isize, Ins::KINT(IRT_IDX, ty.size() as _));
        let size = ctx.data.func.code.push(Ins::MUL(IRT_IDX, len, esizes + i as isize));
        ctx.data.func.code.set(ptrs + i as isize, Ins::ALLOC(size, esizes + i as isize));
    }
    // FIXME repeat_n stabilizes in 1.82.0
    let l_phis = ctx.data.func.phis.extend((0..ds).map(|_| Phi::new(Type::FX)));
    let r_phis = ctx.data.func.phis.extend((0..ds).map(|_| Phi::new(Type::FX)));
    let inits = ctx.data.func.code.extend((0..ds).map(|_| Ins::KNOP()));
    let p_phis = ctx.data.func.phis.extend((0..ds).map(|_| Phi::new(Type::PTR)));
    let mut reduce = newreduce(&ctx.data.func, *ctr, l_phis, r_phis, inits, ds as _);
    for i in 0..ds as isize {
        let head = reserve(&ctx.data.func, 1);
        ctx.data.func.code.set(reduce.loop_.head, Ins::JMP(ptrs + i, head, p_phis + i));
        reduce.loop_.head = head;
    }
    let body = reduce.loop_.body;
    let v = emititer(ctx, &mut reduce.loop_, expr);
    let effects = reserve(&ctx.data.func, ds);
    for i in 0..ds as isize {
        let ptr = ctx.data.func.code.push(Ins::PHI(Type::PTR, body, p_phis + i));
        let store = ctx.data.func.code.push(Ins::STORE(ptr, v + i));
        ctx.data.func.code.set(effects+i, Ins::JOIN(reduce.value+i, store));
        let next_ptr = ctx.data.func.code.push(Ins::ADDP(ptr, esizes + i));
        let tail = reserve(&ctx.data.func, 1);
        ctx.data.func.code.set(reduce.loop_.tail, Ins::JMP(next_ptr, tail, p_phis+i));
        reduce.loop_.tail = tail;
    }
    *ctr = reduce.loop_.out;
    let stores = closereduce(&ctx.data.func, reduce, effects);
    let ret = ctx.data.func.code.extend(
        (0..ds as isize)
        .map(|i| Ins::MOVF(Type::PTR, ptrs+i, stores+i))
    );
    ctx.data.func.code.extend((0..vt.dim() as isize).map(|i| Ins::MOV(IRT_IDX, shape+i)));
    ret
}

// if ALL of the following are true...
//   (1) the VGET variable has exactly one model,
//   (2) VGET and VSET tables match,
//   (3) VGET and VSET indices match,
// then emit a direct load from the model
fn emitfwdvget(ctx: &Ctx, vget: &VGET) -> IndexOption<InsId> {
    let var = &ctx.data.bump[vardata(&ctx.data.objs, vget.var)];
    let [vset] = var.def else { return None.into() };
    let vset = &ctx.data.bump[vset];
    let model = &ctx.data.bump[vset.model];
    // TODO: this check can be relaxed, just need to translate index.
    if !sametab(ctx, ctx.data.tab, model.tab) { return None.into() }
    if !ctx.objs.allequal(cast_args(&vget.idx), cast_args(&ctx.objs[vset.obj].idx)) {
        return None.into();
    }
    let call = emitcallvm1(&ctx.data.func, INS_FLATIDX, model.base + Mod::SUB_VALUE);
    let base = ctx.data.func.code.end();
    // scalar load of vector variable is handled separately:
    debug_assert!(vget.ann != ctx.objs[vget.var].ann);
    for (i,ty) in vset.vty.iter_decomposition().enumerate() {
        ctx.data.func.code.push(Ins::RES(ty, call, vset.ret + i as isize));
    }
    Some(base).into()
}

fn materializevec(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>, vt: VType) -> InsId {
    match ctx.objs.get(expr.erase()) {
        ObjectRef::VGET(vget) => {
            // special case: scalar load of a vector variable is already materialized.
            if vget.ann == ctx.objs[vget.var].ann {
                return emitvget1(ctx, ctr, vget);
            }
            // special case: ref idx matches complex return
            if let Some(ins) = emitfwdvget(ctx, vget).unpack() {
                return ins;
            }
            // TODO: special case vector load over a contiguous range, and return a direct
            //       reference to the buffer
            // else: fallthrough to general case
        }
        // TODO: handle CALLX/GET+CALLX with out-parameters
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALLX(_) => todo!(),
        _ => {}
    }
    // else: collect iterator into array.
    materializecollect(ctx, ctr, expr, vt)
}

fn computevalue(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    let vt = vtypeann(&ctx.objs, expr.erase());
    match vt.is_scalar() {
        true  => materializescalar(ctx, ctr, expr, vt.pri.to_ir()),
        false => materializevec(ctx, ctr, expr, vt)
    }
}

fn itervalue(ctx: &Ctx, loop_: &mut LoopState, expr: ObjRef<EXPR>) -> InsId {
    match ctx.objs.get(expr.erase()) {
        ObjectRef::VGET(&VGET { var, ref idx, .. }) => {
            let var = vardata(&ctx.data.objs, var);
            let i = emitidx(ctx, ControlFlow::Loop(loop_), ctx.data.bump[var].tab, idx);
            emitvarload(ctx, var, i, !idxanalyze(ctx, ctx.data.bump[var].tab,
                    ctx.data.bump[ctx.data.tab].n as _, idx, IdxAttr::Disjoint.into()).is_empty())
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(_) => todo!(),
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { ann, func, ref args, .. })
            => broadcastintrinsic(ctx, loop_, Intrinsic::from_u8(func), args,
                vtypeann(&ctx.objs, ann.erase()).peel()),
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn emitvalue(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    match ctx.objs[expr].mark {
        EXPR_ONE => computevalue(ctx, ctr, expr),
        _ => {
            debug_assert!(ctx.objs[expr].mark == EXPR_MANY);
            if let Some((fid, ins)) = ctx.data.expr.get(expr) {
                if fid == ctx.data.func.cur {
                    return ins;
                }
            }
            let ins = computevalue(ctx, ctr, expr);
            let fid = ctx.data.func.cur;
            ctx.data.expr.insert(expr, (fid, ins));
            ins
        }
    }
}

fn emitshape(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    match ctx.objs[expr].mark {
        EXPR_ONE => computeshape(ctx, ctr, expr),
        _        => emitvalue(ctx, ctr, expr)+1
    }
}

fn emitlen(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>) -> InsId {
    emitshapelen(
        &ctx.data.func,
        emitshape(ctx, ctr, expr),
        vtypeann(&ctx.objs, expr.erase()).dim() as _
    )
}

fn emititer(ctx: &Ctx, loop_: &mut LoopState, expr: ObjRef<EXPR>) -> InsId {
    match ctx.objs[expr].mark {
        EXPR_ONE => itervalue(ctx, loop_, expr),
        _ => {
            // TODO: emitvalue + iterate
            todo!()
        }
    }
}

fn emitcheckvgetloop(
    ctx: &Ctx,
    ctr: &mut InsId,
    var: BumpRef<Var>,
    idx: &[ObjRef<EXPR>],
    inline: bool,
    fail: InsId
) {
    let out = reserve(&ctx.data.func, 3);
    let body = out+1;
    let tail = out+2;
    let mut loop_ = LoopState { head: *ctr, tail, body, out };
    let i = emitidx(ctx, ControlFlow::Loop(&mut loop_), ctx.data.bump[var].tab, idx);
    emitvarcheck(ctx, &mut loop_.body, var, i, inline, fail);
    ctx.data.func.code.set(loop_.head, Ins::GOTO(body));
    ctx.data.func.code.set(loop_.tail, Ins::GOTO(body));
    ctx.data.func.code.set(loop_.body, Ins::GOTO(tail));
    *ctr = out;
}

fn emitcheck(ctx: &Ctx, ctr: &mut InsId, expr: ObjRef<EXPR>, fail: InsId) {
    match ctx.objs.get(expr.erase()) {
        ObjectRef::KINT(_) | ObjectRef::KREF(_) | ObjectRef::DIM(_) | ObjectRef::FREF(_) => {},
        ObjectRef::VGET(&VGET { var, ann, ref idx, .. }) => {
            emitcheckall(ctx, ctr, idx, fail);
            let v = vardata(&ctx.data.objs, var);
            let tab = ctx.data.bump[v].tab;
            let inline = !idxanalyze(ctx, tab, ctx.data.bump[ctx.data.tab].n as _, idx,
                IdxAttr::Disjoint.into()).is_empty();
            if ann == ctx.objs[var].ann {
                let i = emitidx(ctx, ControlFlow::Straight(ctr), tab, idx);
                emitvarcheck(ctx, ctr, v, i, inline, fail);
            } else {
                emitcheckvgetloop(ctx, ctr, v, idx, inline, fail);
            }
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(_) => todo!(),
        ObjectRef::GET(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { ref args, .. }) => emitcheckall(ctx, ctr, args, fail),
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    };
}

fn emitcheckall(ctx: &Ctx, ctr: &mut InsId, objs: &[ObjRef<EXPR>], fail: InsId) {
    for &idx in objs {
        emitcheck(ctx, ctr, idx, fail);
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
fn emittab(ctx: &Ctx, tab: BumpRef<Tab>) {
    let mut ctr = InsId::START;
    let mut len: IndexOption<InsId> = None.into();
    for &Axis { rank, ret, size, .. } in &ctx.data.bump[tab].axes {
        match rank {
            Axis::SCALAR => {
                // asize = check(axis) ? value(axis) : 0
                let asize = ctx.data.func.phis.push(Phi::new(IRT_IDX));
                let merge = reserve(&ctx.data.func, 1);
                let zero = ctx.data.func.code.push(Ins::KINT(IRT_IDX, 0));
                let fail = ctx.data.func.code.push(Ins::JMP(zero, merge, asize));
                emitcheck(ctx, &mut ctr, size, fail);
                let value = emitvalue(ctx, &mut ctr, size);
                let asizev = ctx.data.func.code.push(Ins::PHI(IRT_IDX, merge, asize));
                len = Some(match len.unpack() {
                    Some(len) => ctx.data.func.code.push(Ins::MUL(IRT_IDX, len, asizev)),
                    None      => asizev
                }).into();
                ctx.data.func.code.set(ctr, Ins::JMP(value, merge, asize));
                ctr = reserve(&ctx.data.func, 1);
                ctx.data.func.code.set(merge, Ins::JMP(asizev, ctr, ret));
            },
            _ /* VECTOR */ => {
                // TODO: see above comment
                todo!()
            }
        }
    }
    let len = len.unpack().unwrap_or_else(|| ctx.data.func.code.push(Ins::KINT(IRT_IDX, 0)));
    let ret = ctx.data.func.code.push(Ins::RET());
    ctx.data.func.code.set(ctr, Ins::JMP(len, ret, 0.into()));
}

/* ---- Initializers -------------------------------------------------------- */

fn emitbinit(ctx: &Ctx, tab: BumpRef<Tab>, bundle: FuncId) {
    let tabcall = emittabcall(&ctx.data.func, ctx.data.bump[tab].func);
    let size = ctx.data.func.code.push(Ins::RES(IRT_IDX, tabcall, 0.into()));
    let binit = ctx.data.func.code.push(Ins::BINIT(size, bundle));
    let ret = ctx.data.func.code.push(Ins::RET());
    ctx.data.func.code.set(InsId::START, Ins::JMP(binit, ret, 0.into()));
}

/* ---- Variables ----------------------------------------------------------- */

fn emitvararms(ctx: &Ctx, var: BumpRef<Var>) {
    let mut ctr = InsId::START;
    let ret = ctx.data.func.code.push(Ins::RET());
    for (i, &setter) in ctx.data.bump[var].def.iter().enumerate() {
        let vset = &ctx.data.bump[setter];
        let model = &ctx.data.bump[vset.model];
        let next = reserve(&ctx.data.func, 1);
        match vset.vst {
            VSet::SIMPLE => {
                if !model.guard.is_nil() {
                    emitcheck(ctx, &mut ctr, model.guard, next);
                    let cond = emitvalue(ctx, &mut ctr, model.guard);
                    emitjumpifnot(&ctx.data.func, &mut ctr, cond, next);
                }
                emitcheck(ctx, &mut ctr, ctx.objs[vset.obj].value, next);
            },
            VSet::PREFIX => {
                let var = &ctx.data.bump[vset.var];
                // SourcePrefix on VSET implies:
                debug_assert!(ctx.data.bump[model.tab].n <= ctx.data.bump[var.tab].n);
                let idx = idxtransfer(ctx, var.tab, model.tab, ctx.data.bump[var.tab].n as _,
                    ctx.data.bump[model.tab].n as _, INS_FLATIDX);
                let call = emitcallvm1(&ctx.data.func, idx, model.base + Mod::SUB_AVAIL);
                let check = ctx.data.func.code.push(Ins::RES(Type::B1, call, 0.into()));
                emitjumpifnot(&ctx.data.func, &mut ctr, check, next);
            },
            _ /* COMPLEX */ => {
                todo!()
            }
        }
        let karm = ctx.data.func.code.push(Ins::KINT(IRT_ARM, i as _));
        ctx.data.func.code.set(ctr, Ins::JMP(karm, ret, 0.into()));
        ctr = next;
    }
    let knone = ctx.data.func.code.push(Ins::KINT(IRT_ARM, !0));
    ctx.data.func.code.set(ctr, Ins::JMP(knone, ret, 0.into()));
}

fn emitvarvalue(ctx: &Ctx, var: BumpRef<Var>) {
    let mut ctr = InsId::START;
    let var = &ctx.data.bump[var];
    let ds = var.vty.decomposition_size();
    let vardim = ctx.data.bump[var.tab].n as usize;
    let armcall = emitcallvm1(&ctx.data.func, INS_FLATIDX, var.base + Var::SUB_ARM);
    let arm = ctx.data.func.code.push(Ins::RES(IRT_ARM, armcall, 0.into()));
    let out = ctx.data.func.code.push(Ins::RET());
    for (i, &setter) in var.def.iter().enumerate() {
        let karm = ctx.data.func.code.push(Ins::KINT(IRT_ARM, i as _));
        let check = ctx.data.func.code.push(Ins::EQ(arm, karm));
        let tru = reserve(&ctx.data.func, 2);
        let fal = tru+1;
        ctx.data.func.code.set(ctr, Ins::IF(check, tru, fal));
        ctr = tru;
        let vset = &ctx.data.bump[setter];
        let value = match vset.vst {
            VSet::SIMPLE => emitvalue(ctx, &mut ctr, ctx.objs[vset.obj].value),
            VSet::PREFIX => {
                let model = &ctx.data.bump[vset.model];
                let modeldim = ctx.data.bump[model.tab].n as usize;
                let idx = idxtransfer(ctx, var.tab, model.tab, vardim, modeldim, INS_FLATIDX);
                let call = emitcallvm1(&ctx.data.func, idx, model.base + Mod::SUB_VALUE);
                if ctx.objs[ctx.objs[vset.obj].value].ann == ctx.objs[var.obj].ann {
                    // model returns scalar of var type -> we just forward the value
                    debug_assert!(modeldim == vardim);
                    ctx.data.func.code.extend(
                        var.vty.iter_decomposition()
                        .enumerate()
                        .map(|(j, ty)| Ins::RES(ty, call, vset.ret + j as isize))
                    )
                } else {
                    // model returns rank-k tensor of var type, where k = number of implicit
                    // dimensions, ie. the dim(var.tab) - dim(mod.tab)
                    // -> we "peel off" one layer by loading the flat index on each return slot.
                    debug_assert!(modeldim < vardim);
                    let baseidx = idxtransfer(ctx, model.tab, var.tab, modeldim, vardim, idx);
                    let ofs = ctx.data.func.code.push(Ins::SUB(IRT_IDX, INS_FLATIDX, baseidx));
                    let base = reserve(&ctx.data.func, ds);
                    for (j, ty) in var.vty.iter_decomposition().enumerate() {
                        let res = ctx.data.func.code.push(
                            Ins::RES(Type::PTR, call, vset.ret + j as isize));
                        // TODO: think of something smarter for indexing in general.
                        // doing it this way prevents type narrowing.
                        let size = ctx.data.func.code.push(Ins::KINT(IRT_IDX, ty.size() as _));
                        let offset = ctx.data.func.code.push(Ins::MUL(IRT_IDX, ofs, size));
                        let ptr = ctx.data.func.code.push(Ins::ADDP(res + j as isize, offset));
                        ctx.data.func.code.set(base + j as isize, Ins::LOAD(ty, ptr));
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
            let r = ctx.data.func.code.push(ret);
            ret = Ins::JMP(value + j as isize, r, j.into());
        }
        ctx.data.func.code.set(ctr, ret);
        ctr = fal;
    }
    ctx.data.func.code.set(ctr, Ins::UB());
}

fn emitvarload(ctx: &Ctx, var: BumpRef<Var>, idx: InsId, inline: bool) -> InsId {
    let Var { base, vty, .. } = ctx.data.bump[var];
    let call = emitcallvm(&ctx.data.func, idx, base + Var::SUB_VALUE, inline);
    ctx.data.func.code.extend(
        vty.iter_decomposition()
        .enumerate()
        .map(|(i,ty)| Ins::RES(ty, call, i.into()))
    )
}

fn emitvarloadshape(ctx: &Ctx, var: BumpRef<Var>, idx: InsId, inline: bool) -> InsId {
    let Var { base, vty, .. } = ctx.data.bump[var];
    debug_assert!(!vty.is_scalar());
    let call = emitcallvm(&ctx.data.func, idx, base + Var::SUB_VALUE, inline);
    ctx.data.func.code.extend(
        (vty.peel().decomposition_size()..vty.decomposition_size())
        .map(|i| Ins::RES(IRT_IDX, call, i.into()))
    )
}

fn emitvarcheck(
    ctx: &Ctx,
    ctr: &mut InsId,
    var: BumpRef<Var>,
    idx: InsId,
    inline: bool,
    fail: InsId
) {
    let base = ctx.data.bump[var].base;
    let call = emitcallvm(&ctx.data.func, idx, base + Var::SUB_ARM, inline);
    let arm = ctx.data.func.code.push(Ins::RES(IRT_ARM, call, 0.into()));
    let none = ctx.data.func.code.push(Ins::KINT(IRT_ARM, !0));
    let check = ctx.data.func.code.push(Ins::NE(arm, none));
    emitjumpifnot(&ctx.data.func, ctr, check, fail);
}

/* ---- Models -------------------------------------------------------------- */

// only non-simple models are handled here.
// simple models emit directly into the variable definition.

fn emitmodavail(ctx: &Ctx, model: BumpRef<Mod>) {
    let mut ctr = InsId::START;
    let model = &ctx.data.bump[model];
    let kfal = ctx.data.func.code.push(Ins::KINT(Type::B1, 0));
    let jfal = ctx.data.func.code.push(Ins::JMP(kfal, ctr, 0.into()));
    if !model.guard.is_nil() {
        emitcheck(ctx, &mut ctr, model.guard, jfal);
        let cond = emitvalue(ctx, &mut ctr, model.guard);
        emitjumpifnot(&ctx.data.func, &mut ctr, cond, jfal);
    }
    for setter in &model.value {
        let vset = &ctx.objs[setter.obj];
        emitcheck(ctx, &mut ctr, vset.value, jfal);
        emitcheckall(ctx, &mut ctr, &vset.idx, jfal);
    }
    let ret = ctx.data.func.code.push(Ins::RET());
    let ktru = ctx.data.func.code.push(Ins::KINT(Type::B1, 1));
    ctx.data.func.code.set(ctr, Ins::JMP(ktru, ret, 0.into()));
}

fn emitmodvalue(ctx: &Ctx, model: BumpRef<Mod>) {
    let mut ctr = InsId::START;
    let model = &ctx.data.bump[model];
    for vset in &model.value {
        let value = ctx.objs[vset.obj].value;
        let v = emitvalue(ctx, &mut ctr, value);
        for i in 0..vtypeann(&ctx.objs, value.erase()).decomposition_size() {
            let next = reserve(&ctx.data.func, 1);
            ctx.data.func.code.set(ctr, Ins::JMP(v + i as isize, next, vset.ret + i as isize));
            ctr = next;
        }
    }
    ctx.data.func.code.set(ctr, Ins::RET());
}

/* ---- Queries ------------------------------------------------------------- */

fn emitquery(ctx: &Ctx, query: ObjRef<QUERY>) {
    let mut ctr = InsId::START;
    let mut ret: PhiId = 0.into();
    for &value in &ctx.objs[query].value {
        let mut v = emitvalue(ctx, &mut ctr, value);
        for _ in 0..vtypeann(&ctx.objs, value.erase()).decomposition_size() {
            let next = reserve(&ctx.data.func, 1);
            ctx.data.func.code.set(ctr, Ins::JMP(v, next, ret.into()));
            ctr = next;
            v += 1;
            ret += 1;
        }
    }
    ctx.data.func.code.set(ctr, Ins::RET());
}

/* -------------------------------------------------------------------------- */

fn begin(func: &mut FuncBuilder, ir: &mut IR, id: FuncId) {
    if func.cur != FuncId::INVALID.into() {
        let irf = &mut ir.funcs[func.cur];
        irf.code = take(&mut func.code);
        irf.phis = take(&mut func.phis);
    }
    if id != FuncId::INVALID.into() {
        let irf = &mut ir.funcs[id];
        func.ret = irf.ret;
        func.phis = take(&mut irf.phis);
        // start:
        reserve(func, 1);
        // flatidx:
        match &irf.kind {
            FuncKind::Bundle(bundle) => match bundle.scl {
                SizeClass::GLOBAL => { func.code.push(Ins::KINT(IRT_IDX, 0)); },
                _ => { emitarg(func, 0); }
            },
            FuncKind::Query(_) => { emitarg(func, 0); },
            FuncKind::User() => todo!() // no flatidx (?)
        }
    }
    func.cur = id;
}

fn emitobjs(ccx: &mut Ctx) {
    let objs = Access::borrow(&ccx.data.objs);
    for (&obj, &bump) in objs {
        match ccx.objs[obj].op {
            Obj::TAB => {
                ccx.data.tab = Tab::GLOBAL;
                let func = ccx.data.bump[bump.cast::<Tab>()].func;
                begin(&mut ccx.data.func, &mut ccx.ir, func);
                emittab(ccx, bump.cast());
            },
            Obj::VAR => {
                let Var { base, tab, .. } = ccx.data.bump[bump.cast::<Var>()];
                ccx.data.tab = tab;
                begin(&mut ccx.data.func, &mut ccx.ir, base);
                emitvarvalue(ccx, bump.cast());
                begin(&mut ccx.data.func, &mut ccx.ir, base+1);
                emitbinit(ccx, tab, base);
                begin(&mut ccx.data.func, &mut ccx.ir, base+2);
                emitvararms(ccx, bump.cast());
                begin(&mut ccx.data.func, &mut ccx.ir, base+3);
                emitbinit(ccx, tab, base+2);
            },
            Obj::MOD => {
                if ccx.data.bump[bump.cast::<Mod>()].mt == Mod::COMPLEX {
                    let Mod { base, tab, .. } = ccx.data.bump[bump.cast::<Mod>()];
                    ccx.data.tab = tab;
                    begin(&mut ccx.data.func, &mut ccx.ir, base);
                    emitmodvalue(ccx, bump.cast());
                    begin(&mut ccx.data.func, &mut ccx.ir, base+1);
                    emitbinit(ccx, tab, base);
                    begin(&mut ccx.data.func, &mut ccx.ir, base+2);
                    emitmodavail(ccx, bump.cast());
                    begin(&mut ccx.data.func, &mut ccx.ir, base+3);
                    emitbinit(ccx, tab, base+2);
                }
            },
            Obj::QUERY => {
                let &QUERY { tab, ref value , .. } = &ccx.objs[obj.cast::<QUERY>()];
                ccx.data.tab = objs[&tab.erase()].cast();
                let mut query = Query::new(obj.cast());
                let putofs = ccx.bump.align_for::<Offset>();
                query.offsets = putofs.end();
                let mut func = Func::new(FuncKind::Query(query));
                let mut sig = func.build_signature();
                let mut cursor = 0;
                for &v in value {
                    let ann = vtypeann(&ccx.objs, v.erase());
                    let align = match ann.is_scalar() {
                        true => ann.pri.to_ir(),
                        false => Type::PTR
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
                    for ty in ann.iter_decomposition() {
                        debug_assert!(cursor & (ty.size() - 1) == 0);
                        putofs.push(&(cursor as Offset));
                        sig = sig.add_return(ty);
                        cursor += ty.size();
                    }
                }
                sig.finish_returns().add_arg(IRT_IDX).finish_args();
                let func = ccx.ir.funcs.push(func);
                begin(&mut ccx.data.func, &mut ccx.ir, func);
                emitquery(ccx, obj.cast());

            },
            Obj::FUNC => todo!(),
            _ => unreachable!()
        }
        // TODO: compute resets for each bundle based on IR:
        // * initialize based on CALLN and LOAD
        // * propagate based on CALLB(I) until fixpoint
    }
    begin(&mut ccx.data.func, &mut ccx.ir, FuncId::INVALID.into());
}

impl Phase for Lower {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Lower {
            bump: Default::default(),
            objs: Default::default(),
            expr: Default::default(),
            tmp_ins: Default::default(),
            func: Default::default(),
            tab: BumpRef::zero()
        })
    }

    fn run(ccx: &mut Ccx<Lower>) -> compile::Result {
        collectobjs(ccx);
        emitobjs(unsafe { core::mem::transmute(&mut *ccx) });
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
