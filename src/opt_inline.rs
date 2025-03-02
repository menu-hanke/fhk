//! Inlining.

use core::iter::zip;
use core::ops::Range;

use alloc::vec::Vec;

use crate::bump::BumpRef;
use crate::compile::{self, Ccx};
use crate::controlflow::{dom, BlockId, ControlFlow, InstanceMap};
use crate::index::{self, IndexSlice, IndexVec};
use crate::ir::{FuncId, FuncKind, Ins, InsId, Mark, Opcode, IR};
use crate::optimize::{Ocx, Pass};
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
       | MOV | MOVB | MOVF | CONV | ABOX | BREF | CARG | RES | RET | TRET => 0,
    ADD | SUB | MUL | DIV | UDIV | NEG | ADDP | EQ | NE | LT | LE | ULT | ULE
        | STORE | LOAD | BOX | IF => 1,
    // TODO: CALL cost should depend on called function
    POW | ALLOC | CALL | CALLC | CALLCI | CINIT => 5,
    LO | LOV | LOVV | LOVX | LOX | LOXX => 255
}

const LOOP_COST: u32 = 255;

// TODO: this should be configurable.
// note: this cannot be higher than L* costs.
const FUNC_COST: u32 = 100;
const USE_COST: u32 = 50;

fn execcost(op: Opcode) -> u32 {
    OP_COST[op as usize] as _
}

const CALLER_CALLC: u32 = 0x80000000;

#[derive(Default, Clone)] // for resize
struct FuncData {
    cost: u32,
    callers: u32,
    inline: Option<bool>,
}

enum Action {
    Fixup(/*pos in new code:*/ InsId, /*replace:*/ InsId, /*with:*/ InsId),
    Inline(/*pos in new code:*/ InsId, /*jump target in new code:*/ InsId),
    Phi(/*pos in new code:*/InsId)
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
fn hasloop(code: &mut IndexSlice<InsId, Ins>, id: InsId) -> bool {
    let ins = code[id];
    let mark = ins.get_mark(Mark::Mark1 | Mark::Mark2);
    if mark.is_empty() {
        code[id] = ins.set_mark(Mark::Mark1 | Mark::Mark2);
        for &c in ins.controls() {
            if hasloop(code, c) {
                return true;
            }
        }
        code[id] = ins.set_mark(Mark::Mark1);
        false
    } else {
        mark.contains(Mark::Mark2)
    }
}

fn visitcallers(ir: &IR, inline: &mut Inline, fid: FuncId) {
    for (_, ins) in ir.funcs[fid].code.pairs() {
        let op = ins.opcode();
        if (Opcode::CALLC|Opcode::CALLCI).contains(op) {
            let (_, _, f) = ins.decode_CALLC();
            let fd = &mut inline.func[f];
            debug_assert!(ir.funcs[f].reset.is_subset(&ir.funcs[fid].reset));
            if op == Opcode::CALLC || ir.funcs[f].reset != ir.funcs[fid].reset {
                fd.callers |= CALLER_CALLC;
            } else {
                fd.callers += 1;
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
    id: InsId
) {
    if inst.is_placed(id) {
        return;
    }
    for &user in ctr.dfg.uses(id) {
        visitins(actions, inst, ctr, cursor, bb, user);
    }
    let ins = ctr.code[id];
    let new = inst.get_mut(id);
    if let Some(blocks) = ctr.get_blocks(id) {
        debug_assert!(blocks.len() == new.len());
        for (j, &block) in blocks.iter().enumerate() {
            if ins.opcode().is_pinned() {
                actions.push(Action::Fixup(*cursor, zerocopy::transmute!(block), bb[block]));
            } else if ins.is_marked(Mark::Mark1) {
                actions.push(Action::Inline(*cursor, bb[block]));
                actions.extend(
                    ctr.dfg.uses(id)
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

fn inlinecalls(ccx: &mut Ocx, fid: FuncId, calls: Range<BumpRef<InsId>>, cost: &mut u32) {
    let inl = &mut ccx.data.inline;
    let func = &mut ccx.ir.funcs[fid];
    inl.control.set_func(func);
    for &call in &ccx.tmp[calls.clone()] {
        inl.control.queue(call);
        inl.control.code[call] = inl.control.code[call].set_mark(Mark::Mark1);
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
        visitins(&mut inl.actions, &mut inl.inst, &inl.control, &mut cursor, bb_ctr, id);
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
    let mut phi_base = 0usize;
    let mut dest: InsId = 0.into();
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
                let (idx, _, fu) = code[at].decode_CALLC();
                *cost += inl.func[fu].cost;
                dest = dest_;
                phi_base = func.phis.end().into();
                let ins_base: usize = code.end().into();
                let other = &ccx.ir.funcs[fu];
                let entry = other.entry + ins_base as isize;
                func.phis.extend(other.phis.pairs().map(|(_,p)|p));
                code[at] = match other.params() {
                    r if r.is_empty() => Ins::GOTO(entry),
                    Range { start, end } => {
                        debug_assert!(end == start+1);
                        Ins::JMP(idx, entry, start + phi_base as isize)
                    }
                };
                for (_, mut ins) in other.code.pairs() {
                    if ins.opcode() == Opcode::RET {
                        ins = Ins::GOTO(dest);
                    } else {
                        for v in ins.inputs_and_controls_mut() {
                            *v += ins_base as isize;
                        }
                        if ins.opcode() != Opcode::RES {
                            for p in ins.phis_mut() {
                                *p += phi_base as isize;
                            }
                        }
                    }
                    code.push(ins);
                }
            },
            &Action::Phi(at) => {
                let (call, mut phi) = code[at].decode_RES();
                debug_assert!((Opcode::GOTO|Opcode::JMP).contains(code[call].opcode()));
                phi += phi_base as isize;
                code[at] = Ins::PHI(code[at].type_(), dest, phi);
            }
        }
    }
    func.code.replace_inner(code);
}

fn visitinline(ccx: &mut Ocx, fid: FuncId) {
    let fd = &mut ccx.data.inline.func[fid];
    if !fd.inline.is_none() {
        // already visited
        return;
    }
    fd.inline = Some(false); // stop recursion
    let base = ccx.tmp.end();
    let calls = ccx.tmp.align_for::<InsId>();
    let mut cost = 0;
    for (id, ins) in ccx.ir.funcs[fid].code.pairs() {
        let op = ins.opcode();
        cost += execcost(op);
        if (Opcode::CALLC|Opcode::CALLCI).contains(op) {
            calls.push(id);
        }
    }
    // collect calls to inline
    let mut end = calls.end().cast::<InsId>();
    let mut call = base.cast_up::<InsId>();
    while call < end {
        let (_, _, f) = ccx.ir.funcs[fid].code.at(ccx.tmp[call]).decode_CALLC();
        visitinline(ccx, f);
        match ccx.data.inline.func[f].inline {
            Some(true) => {
                call = call.add_size(1);
            },
            _ => {
                end = end.add_size(-1);
                ccx.tmp[call] = ccx.tmp[end];
            }
        }
    }
    let (start, end) = (base.cast_up::<InsId>(), call);
    // perform inline
    if end > start {
        cost -= (end.size_index()-start.size_index()) as u32 * execcost(Opcode::CALLC);
        inlinecalls(ccx, fid, start..end, &mut cost);
    }
    ccx.tmp.truncate(base);
    let func = &mut ccx.ir.funcs[fid];
    if let FuncKind::Chunk(_) = func.kind {
        // queries are always leaf functions, so don't bother checking this for queries.
        if hasloop(func.code.inner_mut(), func.entry) {
            cost += LOOP_COST;
        }
    }
    let fd = &mut ccx.data.inline.func[fid];
    fd.cost = cost;
    // if all callers are CALLCI:
    //   old cost: cost * callers
    //   new cost: USE_COST * callers + (cost + FUNC_COST) * 1
    // if some callers are CALLC:
    //   callers = huge,
    // and this effectively reduces to
    //   cost <= USE_COST
    fd.inline = Some((cost as u64)*(fd.callers as u64) <= (USE_COST as u64)*(fd.callers as u64)
        + (cost as u64) + (FUNC_COST as u64));
}

impl Pass for Inline {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Default::default())
    }

    fn run(ccx: &mut Ocx) -> compile::Result {
        ccx.data.inline.func.clear();
        ccx.data.inline.func.raw.resize(ccx.ir.funcs.raw.len(), FuncData::default());
        for id in index::iter_span(ccx.ir.funcs.end()) {
            visitcallers(&ccx.ir, &mut ccx.data.inline, id);
        }
        for id in index::iter_span(ccx.ir.funcs.end()) {
            if let FuncKind::Query(_) = ccx.ir.funcs[id].kind {
                visitinline(ccx, id);
            }
        }
        Ok(())
    }

}
