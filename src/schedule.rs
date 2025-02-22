//! Global code motion instruction scheduling.

// the gcm algorithm is adapted from "Global code motion global value numbering" by Cliff Click
// [https://courses.cs.washington.edu/courses/cse501/04wi/papers/click-pldi95.pdf]
// the domtree algorithm is "A Simple, Fast Dominance Algorithm" by KD Cooper
// [https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf]

use core::cmp::{max, Ordering};
use core::ops::Range;

use alloc::vec::Vec;

use crate::bitmap::{BitMatrix, Bitmap, BitmapVec};
use crate::controlflow::{compute_controlflow, compute_dataflow, ControlMatrix};
use crate::dataflow::{Dataflow, DataflowSystem};
use crate::emit::InsValue;
use crate::index::{self, index, IndexOption, IndexSlice, IndexVec, InvalidValue};
use crate::ir::{Code, Func, Ins, InsId, Opcode, PhiId, Type};

index!(pub struct BlockId(u16) invalid(!0));
index!(struct InsIdP(u16) invalid(!0));

impl BlockId {
    pub const START: Self = Self(0);
}

struct InsData {
    early: BlockId, // earliest block possible (exact block for controls and phis)
    pos: InsIdP,    // start of placements of this instruction
    n: u16,         // number of copies of this instruction placed
}

// basic block
struct Block {
    // immediate dominator
    idom: BlockId,
    // the control instruction (terminator) this block was generated from.
    // points to original code before collect, output code after collect.
    ctr: InsId,
    // temporary data
    tmp: u16,
}

#[derive(Default)]
pub struct Gcm {
    // inputs:
    ins: IndexVec<InsId, InsData>,
    dfg: Dataflow<InsId>,
    cfg: Dataflow<BlockId>, // inputs = successors, uses = predecessors
    cmat: ControlMatrix,
    // outputs:
    blocks: IndexVec<BlockId, Block>,
    place: IndexVec<InsIdP, BlockId>,
    // work arrays:
    work_u16: Vec<u16>,
    work_bitmap: BitmapVec,
    solver_block: DataflowSystem<BlockId>,
    solver_ins: DataflowSystem<InsId>
}

// NOTE: for correctness we only need to ensure that block(func.entry) = BlockId::START.
// visiting in preorder guarantees that the domtree algorithm terminates reasonably fast
// (but it is correct for any ordering).
fn placeblock(gcm: &mut Gcm, code: &Code, id: InsId) -> BlockId {
    let gins = &mut gcm.ins[id];
    if gins.early != BlockId::INVALID.into() {
        return zerocopy::transmute!(gins.early)
    }
    let block = gcm.blocks.push(Block { tmp: 0, idom: BlockId::INVALID.into(), ctr: id, });
    gcm.cfg.push();
    gins.early = block;
    let ins = code.at(id);
    let controls = ins.controls();
    let inputs = gcm.cfg.raw_inputs();
    let base = inputs.len();
    // place successors
    inputs.extend(controls.iter().map(|_| IndexOption::<BlockId>::default().raw));
    for (i, &c) in controls.iter().enumerate() {
        let b = placeblock(gcm, code, c);
        gcm.cfg.raw_inputs()[base+i] = b;
    }
    gcm.ins[id].pos = gcm.place.push(block);
    block
}

fn lca(blocks: &IndexSlice<BlockId, Block>, mut a: BlockId, mut b: BlockId) -> BlockId {
    loop {
        match a.cmp(&b) {
            Ordering::Less    => b = blocks[b].idom,
            Ordering::Greater => a = blocks[a].idom,
            Ordering::Equal   => return a
        }
    }
}

fn domtree(gcm: &mut Gcm) {
    gcm.blocks[BlockId::START].idom = BlockId::START;
    loop {
        let mut changed = false;
        for id in index::iter_range(1.into()..gcm.blocks.end()) {
            let mut new_idom = BlockId::INVALID.into();
            for &pred in gcm.cfg.uses(id) {
                if gcm.blocks[pred].idom != BlockId::INVALID.into() {
                    if new_idom != BlockId::INVALID.into() {
                        new_idom = lca(&gcm.blocks, pred, new_idom);
                    } else {
                        new_idom = pred;
                    }
                }
            }
            let b = &mut gcm.blocks[id];
            if b.idom != new_idom {
                b.idom = new_idom;
                changed = true;
            }
        }
        if !changed { break }
    }
}

fn earlyvisit(
    ins: &mut IndexSlice<InsId, InsData>,
    blocks: &IndexSlice<BlockId, Block>,
    dfg: &Dataflow<InsId>,
    code: &Code,
    id: InsId
) -> BlockId {
    let early = ins[id].early;
    if early != BlockId::INVALID.into() {
        return early
    }
    let cins = code.at(id);
    let block = match cins.opcode().is_pinned() {
        true => ins[cins.controls()[0]].early,
        false => {
            let mut b = BlockId::START;
            for &input in dfg.inputs(id) {
                let ib = earlyvisit(ins, blocks, dfg, code, input);
                b = max(b, ib);
            }
            b
        }
    };
    ins[id].early = block;
    block
}

fn earlyschedule(gcm: &mut Gcm, code: &Code) {
    for id in index::iter_span(gcm.dfg.end()) {
        earlyvisit(&mut gcm.ins, &gcm.blocks, &gcm.dfg, code, id);
    }
}

fn latevisit(
    ins: &mut IndexSlice<InsId, InsData>,
    place: &mut IndexVec<InsIdP, BlockId>,
    blocks: &IndexSlice<BlockId, Block>,
    dfg: &Dataflow<InsId>,
    mat: &ControlMatrix,
    code: &Code,
    work: &mut Vec<u16>, // <BlockId>
    id: InsId
) -> Range<InsIdP> {
    let InsData { pos, n, .. } = ins[id];
    if pos != InsIdP::INVALID.into() {
        return pos .. pos + n as isize
    }
    let base = work.len();
    let pinned = code.at(id).opcode().is_pinned();
    if pinned {
        work.push(zerocopy::transmute!(ins[id].early));
    }
    for &user in dfg.uses(id) {
        let upos = latevisit(ins, place, blocks, dfg, mat, code, work, user);
        if !pinned {
            'uloop: for u in index::iter_range(upos) {
                let ublock = place[u];
                for b in &mut work[base..] {
                    let up = lca(blocks, ublock, zerocopy::transmute!(*b));
                    if mat[blocks[up].ctr].test(id) {
                        // note: if i had a fancy rematerialization algorith, it would go right here.
                        *b = zerocopy::transmute!(up);
                        continue 'uloop;
                    }
                }
                work.push(zerocopy::transmute!(ublock));
            }
        }
    }
    // TODO: lift up loop invariants here
    let pos = place.end();
    let n = work[base..].len();
    ins[id].pos = pos;
    ins[id].n = n as _;
    place.raw.extend(work[base..].iter().map(|&b| {let b: BlockId = zerocopy::transmute!(b); b}));
    work.truncate(base);
    pos .. pos + n as isize
}

fn lateschedule(gcm: &mut Gcm, code: &Code) {
    for id in index::iter_span(gcm.dfg.end()) {
        latevisit(
            &mut gcm.ins,
            &mut gcm.place,
            &gcm.blocks,
            &gcm.dfg,
            &gcm.cmat,
            code,
            &mut gcm.work_u16,
            id
        );
    }
}

fn dominates(blocks: &IndexSlice<BlockId, Block>, a: BlockId, mut b: BlockId) -> bool {
    loop {
        match a.cmp(&b) {
            Ordering::Less => b = blocks[b].idom,
            Ordering::Equal => return true,
            Ordering::Greater => return false
        }
    }
}

fn collect(
    gcm: &mut Gcm,
    code: &Code,
    out: &mut IndexVec<InsId, Ins>,
    values: &mut IndexVec<InsId, InsValue>
) {
    // here block.tmp = number of instructions
    for block in &mut gcm.blocks.raw {
        block.tmp = 0;
    }
    for &block in &gcm.place.raw {
        gcm.blocks[block].tmp += 1;
    }
    // after this loop block.tmp = cursor (InsId).
    let mut cursor = 0;
    for block in &mut gcm.blocks.raw {
        cursor += block.tmp;
        block.tmp = cursor;
    }
    // place blocks
    let nins = gcm.place.raw.len();
    out.raw.resize(nins, Ins::NOP_FX);
    values.raw.resize(nins, Default::default());
    for (id, block) in gcm.blocks.pairs_mut() {
        values[zerocopy::transmute!(block.tmp-1)] = InsValue::from_block(id);
        block.ctr = zerocopy::transmute!(block.tmp-1);
    }
    // compute placements and insert dummy instructions.
    // since gcm.place is in reverse order, and block cursors start from the end,
    // place.data ends up in correct order.
    // after this, work[i] = position in output
    debug_assert!(gcm.work_u16.is_empty());
    for &place in &gcm.place.raw {
        let cursor: &mut u16 = &mut gcm.blocks[zerocopy::transmute!(place)].tmp;
        *cursor -= 1;
        gcm.work_u16.push(*cursor);
    }
    // place and patch instructions now that placements are known.
    for (id, ins) in code.pairs() {
        let InsData { pos, n, .. } = gcm.ins[id];
        for p in index::iter_range(pos..pos + n as isize) {
            let mut ins = ins;
            // replace inputs with the unique dominating placement.
            for v in ins.inputs_mut() {
                let InsData { pos, n, .. } = gcm.ins[*v];
                let vp: usize = index::iter_range(pos..pos + n as isize)
                    .find(|&vp| dominates(&gcm.blocks, gcm.place[vp], gcm.place[p]))
                    .unwrap()
                    .into();
                *v = zerocopy::transmute!(gcm.work_u16[vp]);
            }
            // replace controls with the unique placement
            for v in ins.controls_mut() {
                let vp: usize = gcm.ins[*v].pos.into();
                *v = zerocopy::transmute!(gcm.work_u16[vp]);
            }
            let p: usize = p.into();
            out[zerocopy::transmute!(gcm.work_u16[p])] = ins;
        }
    }
    gcm.work_u16.clear();
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
fn computeparams(
    blocks: &mut IndexSlice<BlockId, Block>,
    func: &Func,
    code: &IndexSlice<InsId, Ins>,
    cfg: &Dataflow<BlockId>,
    values: &IndexSlice<InsId, InsValue>,
    solver: &mut DataflowSystem<BlockId>,
    phis: &mut BitMatrix<BlockId, PhiId>,
    work: &mut BitmapVec
) {
    phis.resize(blocks.end(), func.phis.end());
    phis.clear_all();
    if func.phis.is_empty() { return }
    solver.resize(blocks.end());
    solver.queue_all(blocks.end());
    // here block.tmp = JMP(i)
    for block in &mut blocks.raw {
        block.tmp = !0;
    }
    // init dataflow system
    for (id, ins) in code.pairs() {
        match ins.opcode() {
            Opcode::JMP => {
                let (_, _, phi) = ins.decode_JMP();
                let block = values[id].block();
                blocks[block].tmp = zerocopy::transmute!(phi);
            },
            Opcode::PHI => {
                let (ctr, phi) = ins.decode_PHI();
                let block = values[ctr].block();
                phis[block].set(phi);
            },
            // TODO: this should be done for user funcs because they return values in RET, but not
            // for bundles and queries
            // Opcode::RET => {
            //     let block = values[id].block();
            //     for r in index::iter_range(func.returns()) {
            //         phis[block].set(r);
            //     }
            // },
            _ => {}
        }
    }
    for arg in index::iter_range(func.params()) {
        phis[BlockId::START].set(arg);
    }
    // mask out FX phis
    work.resize(func.phis.end().into());
    let work: &mut Bitmap<PhiId> = work.cast_mut();
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
    while let Some(id) = solver.poll() {
        let phi = blocks[id].tmp;
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
        if phi != !0 {
            phis[id].clear(zerocopy::transmute!(phi));
        }
        if phis[id].popcount() != pop {
            solver.queue_nodes(cfg.uses(id));
        }
    }
}

fn gcmclear(gcm: &mut Gcm) {
    gcm.ins.clear();
    gcm.blocks.clear();
    gcm.place.clear();
    gcm.cfg.clear();
    gcm.dfg.clear();
}

pub fn compute_schedule(
    gcm: &mut Gcm,
    func: &Func,
    out: &mut IndexVec<InsId, Ins>,
    values: &mut IndexVec<InsId, InsValue>,
    blockparams: &mut BitMatrix<BlockId, PhiId>
) -> BlockId {
    gcmclear(gcm);
    gcm.ins.raw.extend(
        index::iter_span(func.code.end()).map(|_| InsData {
            early: BlockId::INVALID.into(),
            pos: InsIdP::INVALID.into(),
            n: 1
        })
    );
    placeblock(gcm, &func.code, func.entry);
    // TODO: should either:
    //   (1) place unreachable blocks here, or
    //   (2) require that the cfg has no unreachable blocks here
    gcm.cfg.compute_uses();
    compute_dataflow(&mut gcm.dfg, &func.code);
    earlyschedule(gcm, &func.code);
    compute_controlflow(&func.code, &gcm.dfg, &mut gcm.solver_ins, &mut gcm.cmat,
        &mut gcm.work_bitmap);
    domtree(gcm);
    lateschedule(gcm, &func.code);
    collect(gcm, &func.code, out, values);
    computeparams(&mut gcm.blocks, func, out, &gcm.cfg, values, &mut gcm.solver_block, blockparams,
        &mut gcm.work_bitmap);
    gcm.blocks.end()
}
