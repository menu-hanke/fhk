//! Finalizer management.

use core::any::TypeId;

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::bump::Bump;
use crate::hash::HashMap;
use crate::index::{index, IndexSlice, IndexVec};

index!(struct FinalizerId(u16));

struct Finalizer {
    drop_in_place: unsafe fn(*mut ()),
    size: usize
}

#[derive(Default)]
pub struct FinalizerBuilder {
    mem: Bump<u8>,
    ty_drop: HashMap<TypeId, FinalizerId>,
    finalizers: IndexVec<FinalizerId, Finalizer>,
    cmd: Vec<FinalizerId>
}

pub struct Finalizers {
    mem: Box<[u8]>,
    finalizers: Box<IndexSlice<FinalizerId, Finalizer>>,
    cmd: Box<[FinalizerId]>
}

impl FinalizerBuilder {

    pub fn push<T>(&mut self, value: T) {
        todo!()
    }

    pub fn build(self) -> Finalizers {
        todo!()
    }

}
