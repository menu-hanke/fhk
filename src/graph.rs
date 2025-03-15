//! Graph data structures.

// TODO: *fg.inputs() is only used in compute_cmat and compute_blockparams.
// change this thing to a directed graph instead and only store use-edges.
// (after compute_cmat is nuked)

use core::cmp::max;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut, Range};

use crate::bump::{Bump, BumpPtr, BumpRef};
use crate::index::Index;

const NODE_BASE: BumpRef<Node> = BumpRef::zero();

#[derive(Clone, Copy)]
enum Elist {
    Inputs = 0,
    Uses = 1
}

#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(align(8))]
struct EdgeList {
    num: u16,
    cap: u16,
    nodes: BumpRef<()>,
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct Node {
    edges: [EdgeList; 2]
}

pub struct Graph<I: Index> {
    bump: Bump<I>
}

// view of the graph that doesn't support adding edges.
// this saves one pointer chase on operations.
#[repr(transparent)]
pub struct GraphPtr<I: Index> {
    _marker: PhantomData<fn(&I)>,
    pub bump: BumpPtr
}

impl<I: Index> Graph<I> {

    pub fn clear(&mut self, end: I) {
        self.bump.clear();
        let (_, nodes) = self.bump.reserve_dst(end.into());
        <[Node] as zerocopy::FromZeros>::zero(nodes);
    }

    // TODO: figure out a good way to not monomorphize this..
    fn grow_edges(&mut self, node: I, elist: Elist, newnum: usize) -> BumpRef<I> {
        let mut edges = self.bump[NODE_BASE.add(node)].edges[elist as usize];
        let mut cap = max(edges.cap as usize, 1);
        while cap < newnum { cap *= 2 }
        edges.cap = cap as _;
        let (nodes_ptr, _) = self.bump.reserve_dst::<[I]>(cap);
        let num = edges.num as usize;
        if num > 0 {
            let (data, new) = self.bump.get_dst_mut_split(nodes_ptr, num);
            let old = data.get_dst_mut(edges.nodes.cast(), num);
            new.copy_from_slice(old);
        }
        edges.num = newnum as _;
        edges.nodes = nodes_ptr.cast();
        self.bump[NODE_BASE.add(node)].edges[elist as usize] = edges;
        nodes_ptr.elem(num)
    }

    fn reserve_edges(&mut self, node: I, elist: Elist, need: usize) -> BumpRef<I> {
        let edges = &mut self.bump[NODE_BASE.add(node)].edges[elist as usize];
        let num = edges.num as usize;
        let newnum = num + need;
        if newnum <= edges.cap as usize {
            edges.num = newnum as _;
            edges.nodes.cast::<[I]>().elem(num)
        } else {
            self.grow_edges(node, elist, newnum)
        }
    }

    fn add_edge(&mut self, from: I, to: I, elist: Elist) {
        let ptr = self.reserve_edges(from, elist, 1);
        self.bump[ptr] = to;
    }

    pub fn add_input(&mut self, node: I, input: I) {
        self.add_edge(node, input, Elist::Inputs);
        self.add_edge(input, node, Elist::Uses);
    }

    pub fn add_inputs(&mut self, node: I, inputs: &[I]) {
        let ptr = self.reserve_edges(node, Elist::Inputs, inputs.len());
        self.bump[ptr..ptr.add(inputs.len())].copy_from_slice(inputs);
        for &input in inputs {
            self.add_edge(input, node, Elist::Uses);
        }
    }

    pub fn add_inputs_iter(&mut self, node: I, inputs: impl ExactSizeIterator<Item=I>) {
        let mut ptr = self.reserve_edges(node, Elist::Inputs, inputs.len());
        for input in inputs {
            self.bump[ptr] = input;
            self.add_edge(input, node, Elist::Uses);
            ptr = ptr.add(1);
        }
    }

    pub fn replace_input(&mut self, node: I, old: I, new: I) {
        let mut found = false;
        let inputs = self.bump_inputs(node);
        for input in &mut self.bump[inputs] {
            if *input == old {
                *input = new;
                found = true;
            }
        }
        if found {
            self.remove_edges(old, node, Elist::Uses);
            self.add_edge(new, node, Elist::Uses);
        }
    }

}

impl<I: Index> GraphPtr<I> {

    fn edgenum(&self, node: I, elist: Elist) -> usize {
        self.bump[NODE_BASE.add(node)].edges[elist as usize].num as _
    }

    pub fn use_count(&self, node: I) -> usize {
        self.edgenum(node, Elist::Uses)
    }

    fn edges(&self, node: I, elist: Elist) -> Range<BumpRef<I>> {
        let edges = self.bump[NODE_BASE.add(node)].edges[elist as usize];
        let start = edges.nodes.cast();
        let end = start.add(edges.num as usize);
        start..end
    }

    pub fn bump_inputs(&self, node: I) -> Range<BumpRef<I>> {
        self.edges(node, Elist::Inputs)
    }

    pub fn bump_uses(&self, node: I) -> Range<BumpRef<I>> {
        self.edges(node, Elist::Uses)
    }

    pub fn inputs(&self, node: I) -> &[I] {
        &self.bump[self.bump_inputs(node)]
    }

    pub fn uses(&self, node: I) -> &[I] {
        &self.bump[self.bump_uses(node)]
    }

    fn remove_edges(&mut self, from: I, to: I, elist: Elist) {
        let mut edges = self.bump[NODE_BASE.add(from)].edges[elist as usize];
        let mut cursor = 0;
        while cursor < edges.num as usize {
            let ptr = edges.nodes.cast::<I>().add(cursor);
            if self.bump[ptr] == to {
                self.bump[ptr] = self.bump[edges.nodes.cast::<I>().add((edges.num-1) as usize)];
                edges.num -= 1;
            } else {
                cursor += 1;
            }
        }
        self.bump[NODE_BASE.add(from)].edges[elist as usize] = edges;
    }

    pub fn remove_input(&mut self, node: I, input: I) {
        self.remove_edges(node, input, Elist::Inputs);
        self.remove_edges(input, node, Elist::Uses);
    }

    fn clear_edges(&mut self, from: I, edges: EdgeList, to_elist: Elist) {
        let base: BumpRef<I> = edges.nodes.cast();
        for i in 0..edges.num as usize {
            self.remove_edges(self.bump[base.add(i)], from, to_elist);
        }
    }

    pub fn remove_node(&mut self, node: I) {
        let edges = self.bump[NODE_BASE.add(node)].edges;
        self.clear_edges(node, edges[0], Elist::Uses);
        self.clear_edges(node, edges[1], Elist::Inputs);
    }

}

impl<I: Index> Deref for Graph<I> {
    type Target = GraphPtr<I>;
    fn deref(&self) -> &GraphPtr<I> {
        let bump: &BumpPtr = &self.bump;
        unsafe { core::mem::transmute(bump) }
    }
}

impl<I: Index> DerefMut for Graph<I> {
    fn deref_mut(&mut self) -> &mut GraphPtr<I> {
        let bump: &mut BumpPtr = &mut self.bump;
        unsafe { core::mem::transmute(bump) }
    }
}

impl<I: Index> Default for Graph<I> {
    fn default() -> Self {
        Self { bump: Default::default() }
    }
}
