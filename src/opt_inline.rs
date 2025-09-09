//! Inlining and dead function elimination.

use core::iter::zip;
use core::ops::Range;

use alloc::vec::Vec;

use crate::bump::BumpRef;
use crate::compile::Ccx;
use crate::controlflow::{dom, BlockId, ControlFlow, InstanceMap};
use crate::index::{self, IndexOption, IndexSet, IndexSlice, IndexVec, InvalidValue};
use crate::ir::{FuncId, FuncKind, Ins, InsId, Opcode, PhiId, IR};
use crate::optimize::{Ocx, Pass};
use crate::trace::trace;
use crate::typestate::Absent;

macro_rules! define_costs {
    ($($cost:tt)*) =>{
        const OP_COST: &'static [u8] = &{
            // FIXME replace with core::mem::variant_count when it stabilizes
            const NUM: usize = <Opcode as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _;
            let mut cost = [0; NUM];
            let mut i = 0;
            while i < NUM {
                use Opcode::*;
                cost[i] = match unsafe { core::mem::transmute::<u8,Opcode>(i as u8) } {
                    $($cost)*
                };
                i += 1;
            }
            cost
        };
    };
}

// NOTE: this is for *execution* cost, for CALLC(I).
// regular CALL should consider code size cost instead.
define_costs! {
    NOP | JMP | GOTO | UB | ABORT | PHI | KINT | KINT64 | KFP64 | KSTR | KREF
       | MOV | MOVB | MOVF | CONV | ABOX | BREF | CARG | RES | RET  => 0,
    ADD | SUB | MUL | DIV | UDIV | NEG | ADDP | EQ | NE | LT | LE | ULT | ULE
        | STORE | LOAD | QLOAD | BOX | IF => 1,
    POW | ALLOC | CALLC | CALLCI => 5,
    CALL | CINIT | LO | LOV | LOVV | LOVX | LOX | LOXX => 255
}

const LOOP_COST: u32 = 255;

// TODO: this should be configurable.
// note: this cannot be higher than L* costs.
const FUNC_COST: u32 = 100;
const USE_COST: u32 = 50;

fn execcost(op: Opcode) -> u32 {
    OP_COST[op as usize] as _
}

const CALLER_CALLX: u32 = 0x80000000;

#[derive(Default, Clone, Copy)]
enum InlineState {
    #[default]
    Undetermined, // do not know if this function will be inlined or not
    Yes,          // function will be inlined
    No,           // function will not be inlined because the cost is too high
    Working,      // working on this function right now
}

#[derive(Default, Clone)] // for resize
struct FuncData {
    cost: u32,
    callers: u32,
    state: InlineState
}

enum Action {
    Fixup(/*pos in new code:*/ InsId, /*replace:*/ InsId, /*with:*/ InsId),
    Inline(/*pos in new code:*/ InsId, /*jump target in new code:*/ InsId),
    Phi(/*pos in new code:*/InsId),
    PinEntry(/*pos in new code:*/InsId)
}

#[derive(Default)]
pub struct Inline {
    func: IndexVec<FuncId, FuncData>,
    control: ControlFlow,
    inst: InstanceMap,
    actions: Vec<Action>
}

// mark 1: visited
// mark 2: inside
fn hasloop(
    code: &IndexSlice<InsId, Ins>,
    visited: &mut IndexSet<InsId>,
    inside: &mut IndexSet<InsId>,
    id: InsId
) -> bool {
    if visited.test_and_set(id) {
        return inside.contains(id);
    }
    inside.insert(id);
    for &c in code[id].controls() {
        if hasloop(code, visited, inside, c) {
            return true;
        }
    }
    inside.remove(id);
    false
}

fn visitcallers(ir: &IR, inline: &mut Inline, fid: FuncId) {
    for (_, ins) in ir.funcs[fid].code.pairs() {
        let op = ins.opcode();
        if op.is_call() {
            let f = ins.decode_F();
            let fd = &mut inline.func[f];
            let callers = fd.callers;
            if op != Opcode::CALLCI || ir.funcs[f].reset != ir.funcs[fid].reset {
                fd.callers |= CALLER_CALLX;
            } else {
                fd.callers += 1;
            }
            if callers == 0 {
                visitcallers(ir, inline, f);
            }
        }
    }
}

fn visitins(
    actions: &mut Vec<Action>,
    inst: &mut InstanceMap,
    ctr: &ControlFlow,
    cursor: &mut InsId,
    bb: &mut IndexSlice<BlockId, InsId>,
    iselim: &IndexSet<InsId>,
    arg: PhiId,
    id: InsId
) {
    if inst.is_placed(id) {
        return;
    }
    for &user in &ctr.dfg_users[id] {
        visitins(actions, inst, ctr, cursor, bb, iselim, arg, user);
    }
    let ins = ctr.code[id];
    let new = inst.get_mut(id);
    if let Some(blocks) = ctr.get_blocks(id) {
        debug_assert!(blocks.len() == new.len());
        for (j, &block) in blocks.iter().enumerate() {
            if ins.opcode() == Opcode::PHI && ins.decode_PHI().1 < arg {
                // entry may move but we want arg phis to stay attached to the new entry
                // for control flow optimizations
                actions.push(Action::PinEntry(*cursor));
            } else if ins.opcode().is_pinned() {
                actions.push(Action::Fixup(*cursor, zerocopy::transmute!(block), bb[block]));
            } else if iselim.contains(id) {
                actions.push(Action::Inline(*cursor, bb[block]));
                actions.extend(
                    ctr.dfg_users[id]
                    .iter()
                    .flat_map(|&i| zip(ctr.get_blocks(i).unwrap(), inst.get(i)))
                    .filter_map(|(&b,&i)| dom(&ctr.idom, block, b).then(|| Action::Phi(i)))
                );
                bb[block] = *cursor;
            }
            inst.get_mut(id)[j] = *cursor;
            *cursor += 1;
        }
    } else {
        debug_assert!(new.len() == 1);
        new[0] = *cursor;
        *cursor += 1;
    }
}

// mark1: iselim
fn inlinecalls(ccx: &mut Ocx, fid: FuncId, calls: Range<BumpRef<InsId>>, cost: &mut u32) {
    let inl = &mut ccx.data.inline;
    let func = &mut ccx.ir.funcs[fid];
    inl.control.set_func(func, &mut ccx.mark1);
    ccx.mark1.clear();
    for &call in &ccx.tmp[calls.clone()] {
        inl.control.queue(call);
        ccx.mark1.insert(call);
    }
    inl.control.place_all();
    inl.inst.reset(&inl.control);
    inl.actions.clear();
    let nblock = inl.control.blocks.raw.len();
    let (_, bb_ctr): (_, &mut IndexSlice<BlockId, InsId>) = ccx.tmp.reserve_dst(nblock);
    let mut cursor: InsId = 0.into();
    for (bb, &ctr) in inl.control.blocks.pairs() {
        bb_ctr[bb] = cursor;
        inl.inst.get_mut(ctr)[0] = cursor;
        cursor += 1;
    }
    for id in index::iter_span(inl.control.code.end()) {
        visitins(&mut inl.actions, &mut inl.inst, &inl.control, &mut cursor, bb_ctr, &ccx.mark1,
            func.arg, id);
    }
    for (bb, &ctr) in inl.control.blocks.pairs() {
        for &c in inl.control.code[ctr].controls() {
            let Some(&[dest]) = inl.control.get_blocks(c) else { unreachable!() };
            let bb_max: InsId = inl.control.blocks.raw.len().into();
            if bb_ctr[dest] >= bb_max {
                inl.actions.push(Action::Fixup(zerocopy::transmute!(bb),
                    zerocopy::transmute!(dest), bb_ctr[dest]));
            }
        }
    }
    let Some(&[entry]) = inl.control.get_blocks(func.entry) else { unreachable!() };
    func.entry = bb_ctr[entry];
    let func = &ccx.ir.funcs[fid];
    let mut code = func.code.take_inner();
    inl.control.map_all(&mut code, &inl.inst);
    let mut phi_base = !0usize;
    let mut dest: InsId = InsId::INVALID.into();
    for action in &inl.actions {
        match action {
            &Action::Fixup(at, old, new) => {
                for v in code[at].inputs_and_controls_mut() {
                    if *v == old {
                        *v = new;
                    }
                }
            },
            &Action::Inline(at, dest_) => {
                let op = code[at].opcode();
                let fu = code[at].decode_F();
                *cost -= execcost(op);
                *cost += inl.func[fu].cost;
                dest = dest_;
                phi_base = func.phis.end().into();
                let other = &ccx.ir.funcs[fu];
                let mut ins_base: usize = code.end().into();
                if op == Opcode::CALL {
                    ins_base += (other.arg-other.ret) as usize; // make space for JMPs. hacky but oh well.
                    let entry = other.entry + ins_base as isize;
                    let mut args = code[at].decode_V();
                    let mut enter = Ins::GOTO(entry);
                    let mut phi = other.params().start + phi_base as isize;
                    while code[args].opcode() == Opcode::CARG {
                        let (next, value) = code[args].decode_CARG();
                        enter = Ins::JMP(value, code.push(enter), phi);
                        args = next;
                        phi += 1;
                    }
                    code[at] = enter;
                } else {
                    let entry = other.entry + ins_base as isize;
                    code[at] = match other.params() {
                        r if r.is_empty() => Ins::GOTO(entry),
                        Range { start, end } => {
                            debug_assert!(end == start+1);
                            let idx = code[at].decode_V();
                            Ins::JMP(idx, entry, start + phi_base as isize)
                        }
                    };
                }
                func.phis.extend(other.phis.pairs().map(|(_,p)|p));
                for (_, mut ins) in other.code.pairs() {
                    if ins.opcode() == Opcode::RET {
                        ins = Ins::GOTO(dest);
                    } else {
                        for v in ins.inputs_and_controls_mut() {
                            *v += ins_base as isize;
                        }
                        if ins.opcode() != Opcode::RES {
                            if let Some(p) = ins.phi_mut() {
                                *p += phi_base as isize;
                            }
                        }
                    }
                    code.push(ins);
                }
            },
            &Action::Phi(at) => {
                if code[at].opcode() == Opcode::RES {
                    let (call, mut phi) = code[at].decode_RES();
                    debug_assert!((Opcode::GOTO|Opcode::JMP).contains(code[call].opcode()));
                    phi += phi_base as isize;
                    code[at] = Ins::PHI(code[at].type_(), dest, phi);
                } else {
                    // one RES may be dominated by multiple placements of the same call.
                    // in that case this action is emitted multiple times.
                    // it doesn't matter which call we patch it to, because all of them
                    // dominate it.
                    debug_assert!(code[at].opcode() == Opcode::PHI);
                }
            },
            &Action::PinEntry(at) => {
                debug_assert!(code[at].decode_PHI().1 < func.arg);
                code[at] = code[at].set_a(zerocopy::transmute!(func.entry));
            }
        }
    }
    func.code.replace_inner(code);
}

fn visitinline(ccx: &mut Ocx, fid: FuncId) -> InlineState {
    let fd = &mut ccx.data.inline.func[fid];
    match fd.state {
        InlineState::Undetermined => {
            fd.state = InlineState::Working;
        },
        InlineState::Yes | InlineState::No => return fd.state,
        InlineState::Working => {
            // no inlining for recursive functions.
            // (TODO?: there's room here for a heuristic to decide which function to disable
            //         inlining for in a recursive call chain)
            fd.state = InlineState::No;
            return InlineState::No;
        }
    }
    let base = ccx.tmp.end();
    let calls = ccx.tmp.align_for::<InsId>();
    let mut cost = 0;
    for (id, ins) in ccx.ir.funcs[fid].code.pairs() {
        let op = ins.opcode();
        cost += execcost(op);
        if op.is_call() {
            calls.push(id);
        }
    }
    // collect calls to inline
    let mut end = calls.end().cast::<InsId>();
    let mut call = base.cast_up::<InsId>();
    while call < end {
        let f = ccx.ir.funcs[fid].code.at(ccx.tmp[call]).decode_F();
        match visitinline(ccx, f) {
            InlineState::Yes => {
                call = call.offset(1);
            },
            InlineState::No => {
                end = end.offset(-1);
                ccx.tmp[call] = ccx.tmp[end];
            },
            _ => unreachable!()
        }
    }
    let (start, end) = (base.cast_up::<InsId>(), call);
    // perform inline
    if end > start {
        inlinecalls(ccx, fid, start..end, &mut cost);
    }
    ccx.tmp.truncate(base);
    let fd = &mut ccx.data.inline.func[fid];
    match fd.state {
        InlineState::Working => {
            let func = &mut ccx.ir.funcs[fid];
            if let FuncKind::Chunk(_)|FuncKind::User = func.kind {
                ccx.mark1.clear();
                ccx.mark2.clear();
                // queries are always leaf functions, so don't bother checking this for queries.
                if hasloop(func.code.inner_mut(), &mut ccx.mark1, &mut ccx.mark2, func.entry) {
                    cost += LOOP_COST;
                }
            }
            // if all callers are CALLCI:
            //   old cost: cost * callers
            //   new cost: USE_COST * callers + (cost + FUNC_COST) * 1
            // if some callers are CALLC:
            //   callers = huge,
            // and this effectively reduces to
            //   cost <= USE_COST
            let total = (cost as u64)*(fd.callers as u64);
            let thres = (USE_COST as u64)*(fd.callers as u64) + (cost as u64) + (FUNC_COST as u64);
            trace!(OPTIMIZE "inline: {:?} cost={} thres={} inline={}", fid, total, thres, total<=thres);
            fd.state = match total <= thres {
                true => InlineState::Yes,
                false => InlineState::No
            };
        },
        InlineState::No => {
            trace!(OPTIMIZE "inline: {:?} blacklisted recursive function", fid);
        },
        _ => unreachable!()
    }
    fd.cost = cost;
    fd.state
}

fn sweepdead(
    ir: &mut IR,
    fda: &IndexSlice<FuncId, FuncData>,
    work: &mut IndexSlice<FuncId, IndexOption<FuncId>>
) {
    for (f,(fd,w)) in zip(&ir.funcs.raw, zip(&fda.raw, &mut work.raw)) {
        *w = (!matches!((&f.kind, fd), (
                    FuncKind::Chunk(_)|FuncKind::User,
                    FuncData {state:InlineState::Yes|InlineState::Undetermined,..}
        ))).then_some(0.into()).into();
    }
    let mut left = 0.into();
    let mut right = ir.funcs.end();
    while left < right {
        while left < right && work[left].is_some() {
            work[left] = Some(left).into();
            left += 1;
        }
        while left < right && work[right-1].is_none() {
            ir.funcs.raw.pop();
            right -= 1;
        }
        if left < right {
            debug_assert!(work[left].is_none() && work[right-1].is_some());
            ir.funcs.raw.swap_remove(left.into());
            work[right-1] = Some(left).into();
            right -= 1;
            left += 1;
        }
    }
    if right < work.end() {
        for func in &mut ir.funcs.raw {
            for ins in &mut func.code.inner_mut().raw {
                match ins.opcode() {
                    Opcode::CALL => {
                        // at this point all ir functions are live, and live functions do
                        // not call dead functions.
                        debug_assert!(work[zerocopy::transmute!(ins.b())].is_some());
                        *ins = ins.set_b(zerocopy::transmute!(work[zerocopy::transmute!(ins.b())]));
                    }
                    Opcode::CALLC|Opcode::CALLCI => {
                        debug_assert!(work[zerocopy::transmute!(ins.c())].is_some());
                        *ins = ins.set_c(zerocopy::transmute!(work[zerocopy::transmute!(ins.c())]));
                    },
                    Opcode::CINIT => match work[zerocopy::transmute!(ins.b())].unpack() {
                        Some(f) => *ins = ins.set_b(zerocopy::transmute!(f)),
                        None => *ins = Ins::NOP_FX
                    },
                    _ => {}
                }
            }
        }
    }
}

impl Pass for Inline {

    fn new(_: &mut Ccx<Absent>) -> Self {
        Default::default()
    }

    fn run(ccx: &mut Ocx) {
        debug_assert!(!ccx.ir.funcs.is_empty());
        ccx.data.inline.func.clear();
        ccx.data.inline.func.raw.resize(ccx.ir.funcs.raw.len(), FuncData::default());
        for id in index::iter_span(ccx.ir.funcs.end()) {
            if let FuncKind::Query(_) = ccx.ir.funcs[id].kind {
                visitcallers(&ccx.ir, &mut ccx.data.inline, id);
            }
        }
        for id in index::iter_span(ccx.ir.funcs.end()) {
            if let FuncKind::Query(_) = ccx.ir.funcs[id].kind {
                visitinline(ccx, id);
            }
        }
        let base = ccx.tmp.end();
        let (_, work) = ccx.tmp.reserve_dst(ccx.ir.funcs.raw.len());
        sweepdead(&mut ccx.ir, &ccx.data.inline.func, work);
        ccx.tmp.truncate(base);
    }

}
