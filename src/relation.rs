//! Relation data structure.
// caveat: it leaks like a sieve.
// but it leaks at most 50% of used memory.
// which is good enough for my purposes because it's a short-lived data structure anyway.
// and it only leaks in the sense that you don't get the memory back until you call clear().

use core::fmt::{Debug, Write};
use core::marker::PhantomData;

use alloc::vec::Vec;

use crate::bump::{Bump, BumpPtr, BumpRef};
use crate::index::{Index, IndexVec};

// public only for pairs() return type.
pub struct Node {
    edges: BumpRef<[u8]>,
    len: u16,
    cap: u16
}

pub struct Relation<I: Index, T> {
    _marker: PhantomData<T>,
    nodes: IndexVec<I, Node>,
    edges: Bump
}

pub struct Graph<I: Index> {
    pub forward: Relation<I, I>,
    pub backward: Relation<I, I>
}

impl<I: Index, T> Default for Relation<I, T> {
    fn default() -> Self {
        Self {
            _marker: Default::default(),
            nodes: Default::default(),
            edges: Default::default()
        }
    }
}

impl<I: Index> Default for Graph<I> {
    fn default() -> Self {
        Self {
            forward: Default::default(),
            backward: Default::default()
        }
    }
}

fn node(nodes: &mut Vec<Node>, idx: usize) -> &mut Node {
    if idx >= nodes.len() {
        nodes.resize_with(idx+1, || Node { edges: BumpRef::zero(), len: 0, cap: 0 });
    }
    // i trust that llvm can see that i already did the bound check (surely)
    &mut nodes[idx]
}

fn grow(node: &mut Node, bump: &mut Bump, want: usize, size: usize) {
    let mut cap = node.cap as usize;
    if cap == 0 {
        cap = 8;
    } else {
        cap = cap.next_power_of_two();
    }
    while cap < want {
        cap = cap << 1;
    }
    node.cap = cap as _;
    let newbytes = size * cap;
    let (edges, _) = bump.reserve_dst::<[u8]>(newbytes);
    if node.len > 0 {
        let oldbytes = node.len as usize * size;
        let (bump, newedges) = bump.get_dst_mut_split(edges, newbytes);
        newedges[..oldbytes].copy_from_slice(bump.get_dst(node.edges, oldbytes));
        // old alloc is leaked here. bye. you won't be reused until someone calls clear().
    }
    node.edges = edges;
}

fn add<T>(node: &mut Node, bump: &mut Bump, value: T) {
    if node.len >= node.cap {
        grow(node, bump, node.cap as usize + 1, size_of::<T>());
    }
    unsafe {
        let ptr = bump.as_mut_ptr().add(node.edges.ptr() + (node.len as usize) * size_of::<T>())
            as *mut T;
        ptr.write(value);
    }
    node.len += 1;
}

fn reserve<T>(node: &mut Node, bump: &mut Bump, want: usize) {
    if (node.cap as usize) < want {
        grow(node, bump, want, size_of::<T>());
    }
}

unsafe fn edges<'a, T>(node: &Node, bump: &'a BumpPtr) -> &'a [T] {
    unsafe {
        core::slice::from_raw_parts(
            bump.as_ptr().add(node.edges.ptr()) as _,
            node.len as usize
        )
    }
}

unsafe fn edges_mut<'a, T>(node: &Node, bump: &'a mut BumpPtr) -> &'a mut [T] {
    unsafe {
        core::slice::from_raw_parts_mut(
            bump.as_mut_ptr().add(node.edges.ptr()) as _,
            node.len as usize
        )
    }
}

impl<I: Index, T> Relation<I, T> {

    pub fn clear(&mut self) {
        self.nodes.clear();
        self.edges.clear();
    }

    pub fn reserve(&mut self, key: I, want: usize) {
        reserve::<T>(node(&mut self.nodes.raw, key.into()), &mut self.edges, want);
    }

    pub fn add(&mut self, key: I, value: T) {
        add(node(&mut self.nodes.raw, key.into()), &mut self.edges, value);
    }

    pub fn add_reverse(&mut self, keys: &[I], value: T)
        where T: Clone
    {
        for &key in keys {
            self.add(key, value.clone());
        }
    }

    pub fn collect(&mut self, key: I, values: impl ExactSizeIterator<Item=T>) {
        let node = node(&mut self.nodes.raw, key.into());
        reserve::<T>(node, &mut self.edges, node.len as usize + values.len());
        for value in values {
            add(node, &mut self.edges, value);
        }
    }

    // this takes ownership because i only use it with copy values anyway.
    // less typing and less pointer chasing.
    pub fn remove(&mut self, key: I, value: T)
        where T: PartialEq
    {
        let Some(node) = self.nodes.raw.get_mut(key.into()) else { return };
        let mut i = 0;
        let mut j = node.len as usize;
        let base = unsafe { self.edges.as_mut_ptr().add(node.edges.ptr()) } as *mut T;
        while i < j {
            let v = unsafe { &*base.add(i) };
            if v.eq(&value) {
                unsafe {
                    core::ptr::drop_in_place(base.add(i));
                    base.add(i).write(base.add(j-1).read());
                }
                j -= 1;
            } else {
                i += 1;
            }
        }
        node.len = j as _;
    }

    pub fn pairs<'a>(&'a self) -> core::iter::Map<core::iter::Zip<core::iter::Map<core::ops::Range<usize>, impl Fn(usize) -> I>, core::slice::Iter<'a, Node>>, impl FnMut((I, &'a Node)) -> (I, &'a [T])> {
        let bump = &self.edges;
        self.nodes.pairs().map(move |(i,n)| (i, unsafe { edges(n, bump) }))
    }

}

impl<I: Index> Relation<I, I> {

    // TODO: implement better (count+reserve)
    pub fn backward(&mut self, forward: &Self) {
        for (i,js) in forward.pairs() {
            self.add_reverse(js, i);
        }
    }

}

impl<I: Index> Graph<I> {

    pub fn clear(&mut self) {
        self.forward.clear();
        self.backward.clear();
    }

    pub fn compute_backward(&mut self) {
        self.backward.backward(&self.forward);
    }

}

impl<I: Index, T> core::ops::Index<I> for Relation<I, T> {
    type Output = [T];
    fn index(&self, index: I) -> &[T] {
        match self.nodes.raw.get(index.into()) {
            Some(node) => unsafe { edges(node, &self.edges) },
            None => &[]
        }
    }
}

impl<I: Index, T> core::ops::IndexMut<I> for Relation<I, T> {
    fn index_mut(&mut self, index: I) -> &mut [T] {
        match self.nodes.raw.get(index.into()) {
            Some(node) => unsafe { edges_mut(node, &mut self.edges) },
            None => &mut []
        }
    }
}

impl<I: Index+Debug, T: Debug> Debug for Relation<I, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("{\n")?;
        for (i, ts) in self.pairs() {
            write!(f, "  {:?}: {:?}\n", i, ts)?;
        }
        f.write_char('}')
    }
}
