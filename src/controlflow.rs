//! Control flow analysis

use core::cmp::Ordering;
use core::iter::zip;
use core::ops::Range;

use alloc::collections::vec_deque::VecDeque;
use alloc::vec::Vec;

use crate::bitmap::{BitMatrix, BitmapVec, Bitmap};
use crate::index::{self, index, Index, IndexSet, IndexSlice, IndexVec, InvalidValue};
use crate::ir::{Func, Ins, InsId, Opcode};
use crate::relation::{Graph, Relation};

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
    cfg: &mut Graph<BlockId>,
    blocks: &IndexSlice<BlockId, InsId>,
    inst: &mut IndexVec<InsId, Range<u16>>,
    place: &mut Vec<BlockId>
) {
    for (block, &ctr) in blocks.pairs() {
        placeins1(inst, place, ctr, block);
    }
    for (block, &ctr) in blocks.pairs() {
        cfg.forward.collect(
            block,
            code[ctr]
            .controls()
            .iter()
            .map(|&id| place[inst[id].start as usize])
        );
    }
    cfg.compute_backward();
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
fn compute_domtree(
    cfg_back: &Relation<BlockId, BlockId>,
    idom: &mut IndexSlice<BlockId, BlockId>
) {
    for (id, dom) in idom.pairs_mut() {
        *dom = cfg_back[id].get(0).cloned().unwrap_or(BlockId::START);
    }
    loop {
        let mut fixpoint = true;
        for id in index::iter_range(1.into()..idom.end()) {
            if let &[mut new_idom, ref rest@..] = &cfg_back[id] {
                for &p in rest {
                    new_idom = lca(idom, p, new_idom);
                }
                if idom[id] != new_idom {
                    idom[id] = new_idom;
                    fixpoint = false;
                }
            }
        }
        if fixpoint { break }
    }
    debug_assert!(idom.pairs().all(|(i,&d)| d <= i));
}

/* ---- Dataflow systems ---------------------------------------------------- */

pub struct DataflowSystem<I: Index> {
    worklist: VecDeque<I>,
    queued: BitmapVec<I>
}

impl<I: Index> Default for DataflowSystem<I> {
    fn default() -> Self {
        Self {
            worklist: Default::default(),
            queued: Default::default()
        }
    }
}

impl<I: Index> DataflowSystem<I> {

    pub fn resize(&mut self, end: I) {
        self.worklist.clear();
        self.queued.resize(end);
        self.queued.clear_all();
    }

    pub fn queue(&mut self, node: I) {
        if !self.queued.test_and_set(node) {
            self.worklist.push_back(node);
        }
    }

    pub fn queue_all(&mut self, end: I) {
        for idx in index::iter_span(end) {
            self.queue(idx);
        }
    }

    pub fn queue_nodes(&mut self, nodes: &[I]) {
        for &idx in nodes {
            self.queue(idx);
        }
    }

    pub fn poll(&mut self) -> Option<I> {
        let idx = self.worklist.pop_front();
        if let Some(i) = idx {
            self.queued.clear(i);
        }
        idx
    }

}

/* ---- Control matrices ---------------------------------------------------- */

// (i,j) is true if the execution of the block `i` implies the execution of the instruction `j`
// at some point in the program, either before, in, or after `i`.
// or, in other words, (i,j) is true if the block `i` is a legal placement for an instruction
// `j` with observable side-effects.
// note that fhk only guarantees that a model is not called unless its `where` conditions are
// satisfied, meaning it's valid (although inefficient) to execute the instruction `j`
// multiple times, as long as all executions are in legal blocks.
// side-effect-free instructions can be lifted anywhere, as long as it doesn't cause side-effectful
// instructions to be lifted into illegal blocks.
//
// the control matrix C is the solution to the dataflow system:
//   C(i,j) = 1 if `i` uses `j`,
//   ∩ (C(i') : i' ∈ pred(i)) ⊂  C(i),
//   ∩ (C(i') : i' ∈ succ(i)) ⊂  C(i)
//
// TODO: if all of `i`'s incoming edges imply `j`, but `i`'s immediate dominator doesn't, then
//       this should pull some tricks to avoid recomputing `j` at/after `i`, either by inserting a
//       phi at `i` or by modifying the control flow.

fn markins(code: &IndexSlice<InsId, Ins>, bitmap: &mut Bitmap<InsId>, id: InsId) {
    if bitmap.test_and_set(id) {
        return;
    }
    for &input in code[id].inputs() {
        markins(code, bitmap, input)
    }
}

// set mat[i] = mat[i] ∪  (∩ mat[j] : j ∈ js)
fn addintersect(
    mat: &mut BitMatrix<BlockId, InsId>,
    i: BlockId,
    js: &[BlockId],
    work: &mut Bitmap<InsId>
) {
    match js {
        &[] => {},
        &[j] => {
            let [ri, rj] = mat.get_rows_mut([i, j]);
            ri.union(rj);
        },
        &[first, ref rest@..] => {
            work.copy_from(&mat[first]);
            for &j in rest {
                work.intersect(&mat[j]);
            }
            mat[i].union(work);
        }
    }
}

fn compute_cmat(
    code: &IndexSlice<InsId, Ins>,
    blocks: &IndexSlice<BlockId, InsId>,
    cfg_back: &Relation<BlockId, BlockId>,
    inst: &IndexSlice<InsId, Range<u16>>,
    place: &[BlockId],
    mat: &mut BitMatrix<BlockId, InsId>,
    work: &mut BitmapVec,
    work_blocks: &mut Vec<BlockId>
) {
    mat.resize(blocks.end(), code.end());
    mat.clear_all();
    work.resize(code.end().into());
    let work: &mut Bitmap<InsId> = work.cast_mut();
    for (i, &j) in blocks.pairs() {
        markins(code, &mut mat[i], j);
    }
    for (i, &ins) in code.pairs() {
        if ins.opcode().is_pinned() {
            markins(code, &mut mat[place[inst[i].start as usize]], i);
        }
    }
    loop {
        let mut fixpoint = true;
        for (i, &j) in blocks.pairs() {
            let pop = mat[i].popcount();
            work_blocks.extend(
                code[j]
                .controls()
                .iter()
                .filter_map(|&c| match code[c].opcode() {
                    Opcode::UB => None,
                    _ => Some(place[inst[c].start as usize])
                })
            );
            addintersect(mat, i, &work_blocks, work);
            addintersect(mat, i, &cfg_back[i], work);
            work_blocks.clear();
            fixpoint &= mat[i].popcount() == pop;
        }
        if fixpoint { break }
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
            placeins1(inst, place, id, place[inst[ins.decode_C()].start as usize]);
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
    dfg_users: &Relation<InsId, InsId>,
    idom: &IndexSlice<BlockId, BlockId>,
    mat: &BitMatrix<BlockId, InsId>,
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
        let users = &dfg_users[state.id];
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
                    // crate::trace::trace!("[{:?}/{:?}] lca({:?}, {:?}) -> {:?}", state.id, user, p, *b, up);
                    if mat[up].test(state.id) {
                        *b = up;
                        continue 'uloop;
                    }
                }
                // none of the proposed placements has a common ancestor with p that implies
                // execution of `state.ins`.
                // add a new proposed placement in the same block as the user.
                // crate::trace::trace!("[{:?}/{:?}] push {:?}", state.id, user, p);
                work_blocks.push(p);
            }
            state.user += 1;
        }
        let id = state.id;
        placeins(inst, place, id, &work_blocks[state.base as usize ..]);
        if cfg!(debug_assertions) {
            for i in state.base as usize .. work_blocks.len() {
                debug_assert!(mat[work_blocks[i]].test(id));
                for j in i+1..work_blocks.len() {
                    debug_assert!(!dom(idom, work_blocks[i], work_blocks[j]));
                    debug_assert!(!dom(idom, work_blocks[j], work_blocks[i]));
                }
            }
        }
        work_blocks.truncate(state.base as usize);
        work_state.pop();
        break Some(id);
    }
}

// adapted from "Global code motion global value numbering", Cliff Click
// [https://courses.cs.washington.edu/courses/cse501/04wi/papers/click-pldi95.pdf]
// the `ControlFlow` type maps instructions (either all or a subset) to basic blocks.
// note that it does *not* determine the ordering among instructions in a basic block.
// TODO: cfg forward edges are now only used in schedule, change cfg to Relation<BlockId, BlockId>
//       when they are no longer needed.
#[derive(Default)]
pub struct ControlFlow {
    pub dfg_users: Relation<InsId, InsId>,
    pub cfg: Graph<BlockId>,
    pub idom: IndexVec<BlockId, BlockId>,
    pub code: IndexVec<InsId, Ins>,
    pub blocks: IndexVec<BlockId, InsId>,
    cmat: BitMatrix<BlockId, InsId>,
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
        self.cfg.clear();
        self.dfg_users.clear();
        debug_assert!(self.blocks.raw.len()
            == self.code.raw.iter().filter(|i| i.opcode().is_control()).count());
        for (id, ins) in self.code.pairs() {
            self.dfg_users.add_reverse(ins.inputs_and_controls(), id);
        }
        // by default all instructions are based outside basic blocks
        self.place.clear();
        self.inst.clear();
        self.place.push(BlockId::INVALID.into());
        self.inst.raw.resize(self.code.raw.len(), UNPLACED);
        compute_cfg(&self.code, &mut self.cfg, &self.blocks, &mut self.inst, &mut self.place);
        self.idom.raw.resize(self.blocks.raw.len(), BlockId::INVALID.into());
        compute_domtree(&self.cfg.backward, &mut self.idom);
        place_pinned(&self.code, &mut self.inst, &mut self.place);
        compute_cmat(
            &self.code,
            &self.blocks,
            &self.cfg.backward,
            &self.inst,
            &self.place,
            &mut self.cmat,
            &mut self.work_bitmap,
            &mut self.work_blocks
        );
        // crate::trace::trace!(OPTIMIZE "control matrix:\n{:?}", &self.cmat);
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
            &self.dfg_users,
            &mut self.idom,
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
