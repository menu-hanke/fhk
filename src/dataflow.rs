//! Dataflow graph & dataflow equation solver.

use alloc::collections::vec_deque::VecDeque;
use alloc::vec::Vec;

use crate::bitmap::BitmapVec;
use crate::index::{self, index, Index, IndexVec};

index!(struct InputId(u32));
index!(struct UseId(u32));

struct Node {
    inputs: InputId,
    uses: UseId
}

pub struct Dataflow<I: Index> {
    nodes: IndexVec<I, Node>,
    inputs: IndexVec<InputId, I>,
    uses: IndexVec<UseId, I>,
}

pub struct DataflowSystem<I: Index> {
    worklist: VecDeque<I>,
    queued: BitmapVec<I>
}

impl<I: Index> Default for Dataflow<I> {
    fn default() -> Self {
        Self {
            nodes: Default::default(),
            inputs: Default::default(),
            uses: Default::default()
        }
    }
}

impl<I: Index> Default for DataflowSystem<I> {
    fn default() -> Self {
        Self {
            worklist: Default::default(),
            queued: Default::default()
        }
    }
}

impl<I: Index> Dataflow<I> {

    pub fn push(&mut self) -> I {
        self.nodes.push(Node {
            inputs: self.inputs.end(),
            uses: 0.into()
        })
    }

    pub fn raw_inputs(&mut self) -> &mut Vec<I> {
        &mut self.inputs.raw
    }

    pub fn compute_uses(&mut self) {
        // count uses
        for node in &mut self.nodes.raw { node.uses = 0.into() };
        for &node in &self.inputs.raw { self.nodes[node].uses += 1 };
        // allocate pointers, node.uses will point to the end of the use list
        let mut cursor: UseId = 0.into();
        for node in &mut self.nodes.raw {
            let num: usize = node.uses.into();
            cursor += num as isize;
            node.uses = cursor;
        }
        let end = self.nodes.end();
        // insert dummy
        self.nodes.push(Node { inputs: self.inputs.end(), uses: cursor });
        // write uses, this also makes node.uses point at the start of the use list
        self.uses.raw.reserve(cursor.into());
        I::extend_vec_zeroed(&mut self.uses.raw, cursor.into()).unwrap();
        let mut inputs = 0;
        let mut inputs_end: usize;
        for id in index::iter_span(end) {
            let idx: usize = id.into();
            inputs_end = self.nodes.raw[idx+1].inputs.into();
            while inputs < inputs_end {
                let node = &mut self.nodes[self.inputs[inputs.into()]];
                node.uses -= 1;
                self.uses[node.uses] = id;
                inputs += 1;
            }
        }
    }

    pub fn clear(&mut self) {
        self.nodes.clear();
        self.inputs.clear();
        self.uses.clear();
    }

    pub fn inputs(&self, node: I) -> &[I] {
        let idx: usize = node.into();
        &self.inputs.raw[self.nodes.raw[idx].inputs.into()..self.nodes.raw[idx+1].inputs.into()]
    }

    pub fn uses(&self, node: I) -> &[I] {
        let idx: usize = node.into();
        &self.uses.raw[self.nodes.raw[idx].uses.into()..self.nodes.raw[idx+1].uses.into()]
    }

    pub fn end(&self) -> I {
        let end: usize = self.nodes.end().into();
        // last node is a dummy
        (end-1).into()
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
