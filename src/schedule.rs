//! Global code motion instruction scheduling.

// TODO: remove this file and merge stuff into controlflow.rs

use crate::bitmap::{BitMatrix, Bitmap};
use crate::controlflow::{BlockId, ControlFlow, DataflowSystem, Schedule};
use crate::emit::InsValue;
use crate::index::{self, IndexSet, IndexVec};
use crate::ir::{Func, Ins, InsId, Opcode, PhiId, Type};

#[derive(Default)]
pub struct Gcm {
    control: ControlFlow,
    schedule: Schedule,
    solver: DataflowSystem<BlockId>
}

// a block i must take the phi j as a blockparam if either of the following is true:
//
//   * ctr(i) = ctr(j),  [ie. the phi names this block]
//   * ctr(i) ≠ ctr(j)
//       AND any successor of i takes j as a blockparam
//       AND i is not a JMP setting j
//
// this leads to the dataflow system:
//
//    P(i) = { j : ctr(j) = i } ∪  {∪  P(k) \ JMP(i) : k ∈ succ(i) }
//
// where
//
//    JMP(i) = {j}  if i is a JMP setting j
//    JMP(i) = ∅    otherwise
fn compute_blockparams(gcm: &mut Gcm, func: &Func, phis: &mut BitMatrix<BlockId, PhiId>) {
    phis.resize(gcm.control.blocks.end(), func.phis.end());
    phis.clear_all();
    if func.phis.is_empty() { return }
    // init dataflow system
    for (_, ins) in func.code.pairs() {
        match ins.opcode() {
            Opcode::PHI => {
                let (ctr, phi) = ins.decode_PHI();
                let Some(&[block]) = gcm.control.get_blocks(ctr) else { unreachable!() };
                phis[block].set(phi);
            },
            // TODO: this should be done for user funcs because they return values in RET, but not
            // for chunks and queries
            // Opcode::RET => {
            //     let block = values[id].block();
            //     for r in index::iter_range(func.returns()) {
            //         phis[block].set(r);
            //     }
            // },
            _ => {}
        }
    }
    let solver = &mut gcm.solver;
    let blocks = &gcm.control.blocks;
    solver.resize(blocks.end());
    solver.queue_all(blocks.end());
    for arg in index::iter_range(func.params()) {
        phis[BlockId::START].set(arg);
    }
    // mask out FX phis
    gcm.control.work_bitmap.resize(func.phis.end().into());
    let work: &mut Bitmap<PhiId> = gcm.control.work_bitmap.cast_mut();
    work.set_all();
    for (id, phi) in func.phis.pairs() {
        if phi.type_ == Type::FX {
            work.clear(id);
        }
    }
    for row in index::iter_span(phis.rows()) {
        phis[row].intersect(work);
    }
    // solve dataflow system
    let cfg = &gcm.control.cfg;
    while let Some(id) = solver.poll() {
        let pop = phis[id].popcount();
        for &succ in cfg.inputs(id) {
            // note: id=succ implies either an infinite loop or an unreachable edge.
            // * JMP/GOTO to own block can never get out
            // * IF to own block cant set phis so cond is always true or always false
            if id != succ {
                let [a, b] = phis.get_rows_mut([id, succ]);
                a.union(b);
            }
        }
        let ins = func.code.at(blocks[id]);
        if ins.opcode() == Opcode::JMP {
            let (_, _, phi) = ins.decode_JMP();
            phis[id].clear(phi);
        }
        if phis[id].popcount() != pop {
            solver.queue_nodes(cfg.uses(id));
        }
    }
}

fn visitorder(ctr: &ControlFlow, schedule: &mut Schedule, id: InsId) {
    if schedule.inst.is_placed(id) {
        return
    }
    for &input in ctr.code[id].inputs() {
        visitorder(ctr, schedule, input);
    }
    schedule.place_all(id, ctr);
}

pub fn compute_schedule(
    gcm: &mut Gcm,
    func: &Func,
    code: &mut IndexVec<InsId, Ins>,
    values: &mut IndexVec<InsId, InsValue>,
    blockparams: &mut BitMatrix<BlockId, PhiId>,
    mark: &mut IndexSet<InsId>
) {
    gcm.control.set_func(func, mark);
    // TODO: use next() and:
    // * lift up loop invariants
    // * de-duplicate instructions that *don't* depend on CALLC(I) or L* instructions (lift up to lca)
    //   (or do that in schedule_next)
    gcm.control.queue_all();
    gcm.control.place_all();
    gcm.schedule.reset(&gcm.control);
    values.raw.resize(gcm.schedule.inst.new_len(), Default::default());
    for (block, &ctr) in gcm.control.blocks.pairs() {
        values[gcm.schedule.inst.get(ctr)[0]] = InsValue::from_block(block);
    }
    // TODO: apply some smart ordering heuristics here, like put CALLC(I) first etc. to minimize
    // register pressure
    for id in index::iter_span(gcm.control.code.end()) {
        visitorder(&gcm.control, &mut gcm.schedule, id);
    }
    gcm.control.map_all(code, &gcm.schedule.inst);
    func.code.swap_inner(&mut gcm.control.code);
    compute_blockparams(gcm, func, blockparams);
}
