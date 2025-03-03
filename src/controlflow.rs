//! Control flow analysis

use core::cmp::Ordering;
use core::iter::zip;
use core::ops::Range;

use alloc::vec::Vec;

use crate::bitmap::{BitMatrix, BitmapVec, Bitmap};
use crate::dataflow::{Dataflow, DataflowSystem};
use crate::index::{self, index, IndexSet, IndexSlice, IndexVec, InvalidValue};
use crate::ir::{Func, Ins, InsId, Opcode};

/* ---- Control flow graph -------------------------------------------------- */

index!(pub struct BlockId(u16) invalid(!0) debug("b{}"));

impl BlockId {
    pub const START: Self = Self(0);
}

fn visitdata(code: &IndexSlice<InsId, Ins>, visited: &mut IndexSet<InsId>, id: InsId) {
    if visited.test_and_set(id) {
        return;
    }
    for &v in code[id].inputs() {
        visitdata(code, visited, v);
    }
}

// NOTE: for correctness we only need to ensure that block(entry) = BlockId::START.
// visiting in preorder guarantees that the domtree algorithm terminates reasonably fast
// (but it is correct for any ordering).
fn visitcontrol(
    code: &IndexSlice<InsId, Ins>,
    blocks: &mut IndexVec<BlockId, InsId>,
    visited: &mut IndexSet<InsId>,
    id: InsId
) {
    if visited.test_and_set(id) {
        return;
    }
    let ins = code[id];
    blocks.push(id);
    for &v in ins.inputs() {
        visitdata(code, visited, v);
    }
    for &c in ins.controls() {
        visitcontrol(code, blocks, visited, c);
    }
}

fn compute_blocks(
    code: &mut IndexSlice<InsId, Ins>,
    blocks: &mut IndexVec<BlockId, InsId>,
    visited: &mut IndexSet<InsId>,
    entry: InsId
) {
    visited.clear();
    blocks.clear();
    visitcontrol(code, blocks, visited, entry);
    // nuke all unreachable code.
    // this is a bit of a ghetto solution, but it makes the rest of the algorithm much simpler.
    for (id, ins) in code.pairs_mut() {
        if !visited.contains(id) {
            *ins = Ins::NOP_FX;
        }
    }
}

const UNPLACED: Range<u16> = 0..1;

fn placeins1(
    inst: &mut IndexVec<InsId, Range<u16>>,
    place: &mut Vec<BlockId>,
    id: InsId,
    block: BlockId
) {
    debug_assert!(inst[id] == UNPLACED);
    debug_assert!(block != BlockId::INVALID.into());
    let pos = place.len();
    inst[id] = pos as u16 .. pos as u16 + 1;
    place.push(block);
}

fn placeins(
    inst: &mut IndexVec<InsId, Range<u16>>,
    place: &mut Vec<BlockId>,
    id: InsId,
    blocks: &[BlockId]
) {
    debug_assert!(inst[id] == UNPLACED);
    debug_assert!(blocks.iter().all(|&b| b != BlockId::INVALID.into()));
    let pos = place.len();
    inst[id] = pos as u16 .. (pos+blocks.len()) as u16;
    place.extend_from_slice(blocks);
}

fn compute_cfg(
    code: &IndexSlice<InsId, Ins>,
    cfg: &mut Dataflow<BlockId>,
    blocks: &IndexSlice<BlockId, InsId>,
    inst: &mut IndexVec<InsId, Range<u16>>,
    place: &mut Vec<BlockId>
) {
    for (block, &ctr) in blocks.pairs() {
        placeins1(inst, place, ctr, block);
    }
    cfg.clear();
    for &ctr in &blocks.raw {
        cfg.push();
        cfg.raw_inputs().extend(
            code[ctr]
            .controls()
            .iter()
            .map(|&id| place[inst[id].start as usize])
        );
    }
    cfg.compute_uses();
}

fn lca(idom: &IndexSlice<BlockId, BlockId>, mut a: BlockId, mut b: BlockId) -> BlockId {
    loop {
        match a.cmp(&b) {
            Ordering::Less    => b = idom[b],
            Ordering::Greater => a = idom[a],
            Ordering::Equal   => return a
        }
    }
}

pub fn dom(idom: &IndexSlice<BlockId, BlockId>, a: BlockId, mut b: BlockId) -> bool {
    loop {
        match a.cmp(&b) {
            Ordering::Less    => b = idom[b],
            Ordering::Equal   => return true,
            Ordering::Greater => return false
        }
    }
}

// "A Simple, Fast Dominance Algorithm", KD Cooper
// [https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf]
fn compute_domtree(cfg: &Dataflow<BlockId>, idom: &mut IndexSlice<BlockId, BlockId>) {
    idom.raw.fill(BlockId::INVALID.into());
    idom[BlockId::START] = BlockId::START;
    loop {
        let mut fixpoint = true;
        for id in index::iter_range(1.into()..idom.end()) {
            let mut new_idom = BlockId::INVALID.into();
            for &pred in cfg.uses(id) {
                if idom[pred] != BlockId::INVALID.into() {
                    if new_idom == BlockId::INVALID.into() {
                        new_idom = pred;
                    } else {
                        new_idom = lca(idom, pred, new_idom);
                    }
                }
            }
            if idom[id] != new_idom {
                idom[id] = new_idom;
                fixpoint = false;
            }
        }
        if fixpoint { break }
    }
    debug_assert!(idom.pairs().all(|(i,&d)| d <= i));
}

/* ---- Dataflow graph ------------------------------------------------------ */

fn compute_dfg(code: &[Ins], dfg: &mut Dataflow<InsId>) {
    dfg.clear();
    for &ins in code {
        dfg.push();
        dfg.raw_inputs().extend_from_slice(ins.inputs_and_controls());
    }
    dfg.compute_uses();
}

/* ---- Control matrices ---------------------------------------------------- */

// the entry (i,j) tells you:
//
//   IF control flow goes through node i, does it necessarily ALSO go through node j?
//
// this sounds a lot like a dominance tree, but it's not the same thing at all.
// it's also not a postdominance tree. it's also not a union of the two.
// the reason this needs to exist is because CSE across "basic blocks" (which the ir doesn't
// have anyway, but imagine for a second it did) causes wonky "control flows".
// example:
//                 3. IF
//                /     \
//             4. IF  5. use 1
//            /  \    6. use 2
//      7. use 1  6. use 1
//      8. use 2
//
// here:
//   * execution of 3 implies execution of 1
//   * execution 1 implies execution of 3, IF these are all the uses of 1. if there's other uses
//     of 1 not shown in the picture, then 1 does not imply 3.
//   * 3 does not imply 2, but 2 may or may not imply 3, again depending on its other uses.
//
// note that this has nothing to do with the order of computations, only whether control flow
// must pass through the instruction or not.
//
// it is the solution to the following system:
//
//   C(i,i) = 1   for all i
//   C(i,j) = 1   where i ≠ j, if (at least) one of the following is true:
//                * (1) C(k,j) = 1 for all k ∈ uses(i)
//                * (2) op(i) ≠ IF, and C(k,j) = 1 for some k ∈ inputs(i)
//                * (3) op(i) ≠ IF, and C(cond(i),j) = 1, or C(tru(i),j) = C(fal(i),j) = 1
//   C(i,j) = 0   otherwise,
//
// or in a more dataflow-y form:
//
//   C(i) = {i} ∪  (∩  C(j) : j ∈ uses(i)) ∪  (∪  C(j) : j ∈ inputs(i))               IF op(i) ≠ IF
//   C(i) = {i} ∪  (∩  C(j) : j ∈ uses(i)) ∪  C(cond(i)) ∪  (C(tru(i)) ∩  C(fal(i)))  IF op(i) = IF
//
// note that data and control are treated uniformly here: inputs(i) contains data inputs and
// successors, while uses(i) contains data uses and precedessors.
pub type ControlMatrix = BitMatrix<InsId>;

// set r(i) = r(i) ∪  (∩ r(j) : js)
fn addintersect(mat: &mut BitMatrix<InsId>, i: InsId, js: &[InsId], work: &mut Bitmap<InsId>) {
    match js.len() {
        0 => {},
        1 => {
            let [ri, rj] = mat.get_rows_mut([i, js[0]]);
            ri.union(rj);
        },
        _ => {
            work.copy_from(&mat[js[0]]);
            for &j in &js[1..] {
                work.intersect(&mat[j]);
            }
            mat[i].union(work);
        }
    }
}

fn compute_cmat(
    code: &IndexSlice<InsId, Ins>,
    dfg: &Dataflow<InsId>,
    solver: &mut DataflowSystem<InsId>,
    mat: &mut ControlMatrix,
    work: &mut BitmapVec
) {
    let end = dfg.end();
    mat.resize(end, end);
    mat.clear_all();
    for i in index::iter_span(end) {
        mat[i].set(i);
    }
    work.resize(end.into());
    let work: &mut Bitmap<InsId> = work.cast_mut();
    solver.resize(end);
    solver.queue_all(end);
    while let Some(i) = solver.poll() {
        let pop = mat[i].popcount();
        let inputs = dfg.inputs(i);
        let uses = dfg.uses(i);
        addintersect(mat, i, uses, work);
        match code[i].opcode() {
            Opcode::IF => {
                let [ri, rcond] = mat.get_rows_mut([i, inputs[0]]);
                ri.union(rcond);
                addintersect(mat, i, &inputs[1..], work);
            },
            _ => for &j in inputs {
                let [ri, rj] = mat.get_rows_mut([i, j]);
                ri.union(rj);
            }
        }
        if mat[i].popcount() != pop {
            solver.queue_nodes(inputs);
            solver.queue_nodes(uses);
        }
    }
}

/* ---- Scheduling ---------------------------------------------------------- */

fn place_pinned(
    code: &IndexSlice<InsId, Ins>,
    inst: &mut IndexVec<InsId, Range<u16>>,
    place: &mut Vec<BlockId>
) {
    for (id, ins) in code.pairs() {
        let op = ins.opcode();
        debug_assert!(!(op.is_control() && inst[id].len() != 1));
        if op.is_pinned() {
            placeins1(inst, place, id, place[inst[ins.controls()[0]].start as usize]);
        }
    }
}

fn dominating_instance(
    id: InsId,
    block: BlockId,
    idom: &IndexSlice<BlockId, BlockId>,
    inst: &IndexSlice<InsId, Range<u16>>,
    place: &[BlockId],
) -> usize {
    let Range { start, end } = inst[id];
    if end-start == 1 {
        // either:
        //   (1) this instruction is unplaced, in which case the unique unplaced instance dominates
        //       all uses (since it eventually gets instantiated and placed by scheduling)
        //   (2) the user is unplaced (block is INVALID), and this instruction is either unplaced
        //       or pinned
        //   (3) the unique placement dominates the user's block
        debug_assert!(
            inst[id] == UNPLACED
            || block == BlockId::INVALID.into()
            || dom(idom, place[start as usize], block)
        );
        0
    } else {
        place[start as usize .. end as usize]
            .iter()
            .enumerate()
            .find_map(|(i,&b)| dom(idom, b, block).then_some(i))
            .unwrap()
    }
}

struct WorkIns {
    id: InsId,
    user: u16,
    base: u16
}

fn schedule_next(
    work_state: &mut Vec<WorkIns>,
    work_blocks: &mut Vec<BlockId>,
    dfg: &Dataflow<InsId>,
    idom: &IndexSlice<BlockId, BlockId>,
    blocks: &IndexSlice<BlockId, InsId>,
    mat: &ControlMatrix,
    inst: &mut IndexVec<InsId, Range<u16>>,
    place: &mut Vec<BlockId>
) -> Option<InsId> {
    let mut state = loop {
        let state = work_state.last_mut()?;
        debug_assert!(work_blocks.len() >= state.base as usize);
        if inst[state.id] == UNPLACED {
            break state
        } else {
            work_blocks.truncate(state.base as usize);
            work_state.pop();
        }
    };
    'outer: loop {
        let users = dfg.uses(state.id);
        while (state.user as usize) < users.len() {
            let user = users[state.user as usize];
            if inst[user] == UNPLACED {
                work_state.push(WorkIns {
                    id: user,
                    user: 0,
                    base: work_blocks.len() as _
                });
                state = work_state.last_mut().unwrap();
                continue 'outer;
            }
            let base = state.base as usize;
            let Range { start, end } = inst[user];
            'uloop: for &p in &place[start as usize .. end as usize] {
                for b in &mut work_blocks[base..] {
                    let up = lca(idom, p, *b);
                    //crate::trace::trace!("[{:?}/{:?}] lca({:?}, {:?}) -> {:?}", state.id, user, p, *b, up);
                    if mat[blocks[up]].test(state.id) {
                        *b = up;
                        continue 'uloop;
                    }
                }
                // none of the proposed placements has a common ancestor with p that implies
                // execution of `state.ins`.
                // add a new proposed placement in the same block as the user.
                //crate::trace::trace!("[{:?}/{:?}] push {:?}", state.id, user, p);
                work_blocks.push(p);
            }
            state.user += 1;
        }
        let id = state.id;
        placeins(inst, place, id, &work_blocks[state.base as usize ..]);
        // TODO: re-enable these asserts when new cmat is implemented
        // if cfg!(debug_assertions) {
        //     for i in state.base as usize .. work_blocks.len() {
        //         debug_assert!(mat[blocks[work_blocks[i]]].test(id));
        //         for j in i+1..work_blocks.len() {
        //             debug_assert!(!dom(idom, work_blocks[i], work_blocks[j]));
        //             debug_assert!(!dom(idom, work_blocks[j], work_blocks[i]));
        //         }
        //     }
        // }
        work_blocks.truncate(state.base as usize);
        work_state.pop();
        break Some(id);
    }
}

// adapted from "Global code motion global value numbering", Cliff Click
// [https://courses.cs.washington.edu/courses/cse501/04wi/papers/click-pldi95.pdf]
// the `ControlFlow` type maps instructions (either all or a subset) to basic blocks.
// note that it does *not* determine the ordering among instructions in a basic block.
#[derive(Default)]
pub struct ControlFlow {
    pub dfg: Dataflow<InsId>,
    pub cfg: Dataflow<BlockId>,
    pub idom: IndexVec<BlockId, BlockId>,
    pub code: IndexVec<InsId, Ins>,
    pub blocks: IndexVec<BlockId, InsId>,
    solver: DataflowSystem<InsId>,
    cmat: ControlMatrix,
    pub work_bitmap: BitmapVec,
    inst: IndexVec<InsId, Range<u16>>,
    place: Vec<BlockId>,
    state: Vec<WorkIns>,
    work_blocks: Vec<BlockId>
}

#[derive(Default)]
pub struct InstanceMap {
    old: IndexVec<InsId, u16>,   // old ins -> start of placements
    new: Vec<InsId>,             // placement -> new ins
}

#[derive(Default)]
pub struct Schedule {
    pub inst: InstanceMap,
    pub cursor: IndexVec<BlockId, InsId>  // bb -> new ins
}

impl ControlFlow {

    pub fn set_func(&mut self, func: &Func, mark: &mut IndexSet<InsId>) {
        func.code.swap_inner(&mut self.code);
        compute_blocks(&mut self.code, &mut self.blocks, mark, func.entry);
        debug_assert!(self.blocks.raw.len()
            == self.code.raw.iter().filter(|i| i.opcode().is_control()).count());
        compute_dfg(&self.code.raw, &mut self.dfg);
        compute_cmat(&self.code, &self.dfg, &mut self.solver, &mut self.cmat, &mut self.work_bitmap);
        //crate::trace::trace!(OPTIMIZE "control matrix:\n{:?}", &self.cmat);
        // by default all instructions are based outside basic blocks
        self.place.clear();
        self.inst.clear();
        self.place.push(BlockId::INVALID.into());
        self.inst.raw.resize(self.code.raw.len(), UNPLACED);
        compute_cfg(&self.code, &mut self.cfg, &self.blocks, &mut self.inst, &mut self.place);
        self.idom.raw.resize(self.blocks.raw.len(), BlockId::INVALID.into());
        compute_domtree(&self.cfg, &mut self.idom);
        place_pinned(&self.code, &mut self.inst, &mut self.place);
    }

    pub fn queue(&mut self, id: InsId) {
        if self.inst[id] == UNPLACED {
            self.state.push(WorkIns {
                id,
                user: 0,
                base: self.work_blocks.len() as _
            });
        }
    }

    pub fn queue_all(&mut self) {
        for (id, inst) in self.inst.pairs() {
            if *inst == UNPLACED {
                self.state.push(WorkIns {
                    id,
                    user: 0,
                    base: self.work_blocks.len() as _
                });
            }
        }
    }

    pub fn next(&mut self) -> Option<InsId> {
        schedule_next(
            &mut self.state,
            &mut self.work_blocks,
            &self.dfg,
            &mut self.idom,
            &self.blocks,
            &self.cmat,
            &mut self.inst,
            &mut self.place
        )
    }

    pub fn place_all(&mut self) {
        while self.next().is_some() {}
    }

    pub fn get_blocks(&self, id: InsId) -> Option<&[BlockId]> {
        match &self.inst[id] {
            &UNPLACED => None,
            &Range { start, end } => Some(&self.place[start as usize .. end as usize])
        }
    }

    fn map(&self, id: InsId, inst: usize, map: &InstanceMap) -> Ins {
        let mut ins = self.code[id];
        let Range { start, end } = self.inst[id];
        debug_assert!(start as usize + inst < end as usize);
        let block = self.place[start as usize + inst];
        for v in ins.inputs_mut() {
            let i = dominating_instance(*v, block, &self.idom, &self.inst, &self.place);
            *v = map.new[map.old[*v] as usize + i];
        }
        for v in ins.controls_mut() {
            debug_assert!(self.inst[*v].len() == 1);
            *v = map.new[map.old[*v] as usize];
        }
        ins
    }

    pub fn map_all(&self, code: &mut IndexVec<InsId, Ins>, map: &InstanceMap) {
        code.clear();
        code.raw.resize(map.new.len(),
            match cfg!(debug_assertions) { true => Ins::UB(), false => Ins::NOP_FX });
        let mut cursor = 0;
        let mut old: InsId = 0.into();
        for &end in &map.old.raw[1..] {
            let mut j = 0;
            while cursor < end as usize {
                code[map.new[cursor]] = self.map(old, j, map);
                cursor += 1;
                j += 1;
            }
            old += 1;
        }
    }

}

impl InstanceMap {

    pub fn reset(&mut self, ctr: &ControlFlow) {
        self.old.clear();
        let mut cursor = 0;
        for &Range { start, end } in &ctr.inst.raw {
            self.old.push(cursor);
            cursor += end-start;
        }
        self.old.push(cursor); // for get(_mut) bounds
        self.new.clear();
        self.new.resize(cursor as _, InsId::INVALID.into());
        debug_assert!((cursor as usize) >= ctr.place.len()-1);
    }

    pub fn get(&self, id: InsId) -> &[InsId] {
        &self.new[self.old[id] as usize .. self.old[id+1] as usize]
    }

    pub fn get_mut(&mut self, id: InsId) -> &mut [InsId] {
        &mut self.new[self.old[id] as usize .. self.old[id+1] as usize]
    }

    pub fn is_placed(&self, id: InsId) -> bool {
        let place = self.get(id);
        debug_assert!(
            place.iter().all(|&i| i == InsId::INVALID.into())
            || place.iter().all(|&i| i != InsId::INVALID.into())
        );
        match place.get(0) {
            None => true,
            Some(&i) => i != InsId::INVALID.into()
        }
    }

    pub fn new_len(&self) -> usize {
        self.new.len()
    }

}

impl Schedule {

    pub fn reset(&mut self, ctr: &ControlFlow) {
        // at this point we must have full control flow, ie. all instructions must be assigned
        // a set of basic blocks
        debug_assert!(ctr.inst.raw.iter().all(|r| r != &UNPLACED));
        self.inst.reset(ctr);
        debug_assert!(self.inst.new.len() == ctr.place.len()-1);
        self.cursor.raw.clear();
        self.cursor.raw.resize(ctr.blocks.raw.len(), 0.into());
        for &block in &ctr.place[1..] {
            self.cursor[block] += 1;
        }
        // place control instructions at the end of their blocks
        let mut cursor: InsId = 0.into();
        for (&id, ptr) in zip(&ctr.blocks.raw, &mut self.cursor.raw) {
            let num: usize = (*ptr).into();
            *ptr = cursor;
            cursor += num as isize;
            self.inst.new[self.inst.old[id] as usize] = cursor - 1;
        }
    }

    pub fn place_all(&mut self, id: InsId, ctr: &ControlFlow) {
        debug_assert!(ctr.code[id].opcode().is_data());
        debug_assert!(ctr.code[id].inputs().iter().all(|&i| self.inst.is_placed(i)));
        debug_assert!(!self.inst.is_placed(id));
        debug_assert!(
            ctr.get_blocks(id).unwrap().iter()
            .all(|&block| self.cursor[block]
                < self.cursor.raw.get({let b: usize = block.into(); b+1})
                .cloned().unwrap_or(self.inst.new.len().into()))
        );
        for (&block, ptr) in zip(ctr.get_blocks(id).unwrap(), self.inst.get_mut(id)) {
            *ptr = self.cursor[block];
            self.cursor[block] += 1;
        }
    }

}
