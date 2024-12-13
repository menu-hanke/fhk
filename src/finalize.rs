//! Finalizer management.

use core::any::TypeId;

use alloc::boxed::Box;
use alloc::vec::Vec;
use hashbrown::hash_map::Entry;

use crate::bump::Bump;
use crate::hash::HashMap;
use crate::index::{index, IndexSlice, IndexVec};
use crate::mem::{Cursor, CursorType};

index!(struct FinalizerId(u16));

struct Finalizer {
    drop_in_place: unsafe fn(*mut ()),
    size: u32,
    align: u32
}

#[derive(Default)]
pub struct FinalizerBuilder {
    mem: Bump<u8>,
    ty_drop: HashMap<TypeId, FinalizerId>,
    finalizers: IndexVec<FinalizerId, Finalizer>,
    cmd: Vec<FinalizerId>
}

// TODO: sort finalized objects by finalizer, so that finalizerid isn't needed here.
pub struct Finalizers {
    mem: Bump<u8>,
    finalizers: Box<IndexSlice<FinalizerId, Finalizer>>,
    cmd: Box<[FinalizerId]>
}

impl FinalizerBuilder {

    fn intern_finalizer(&mut self, type_: TypeId, finalizer: Finalizer) -> FinalizerId {
        match self.ty_drop.entry(type_) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => *e.insert(self.finalizers.push(finalizer))
        }
    }

    fn finalizer<T: 'static>(&mut self) -> FinalizerId {
        let drop_in_place: unsafe fn(*mut T) = core::ptr::drop_in_place::<T>;
        self.intern_finalizer(
            TypeId::of::<T>(),
            Finalizer {
                drop_in_place: unsafe { core::mem::transmute(drop_in_place) },
                size: size_of::<T>() as _,
                align: align_of::<T>() as _,
            }
        )
    }

    pub fn push<T: 'static>(&mut self, value: T) {
        self.mem.align(align_of::<T>());
        let (_, data) = self.mem.reserve_dst::<[u8]>(size_of::<T>());
        unsafe { core::ptr::write(data as *mut [u8] as *mut u8 as *mut T, value) }
        let fin = self.finalizer::<T>();
        self.cmd.push(fin);

    }

    pub fn build(self) -> Finalizers {
        Finalizers {
            mem: Bump::copy_of(&self.mem),
            finalizers: IndexSlice::from_raw_box(self.finalizers.raw.into_boxed_slice()),
            cmd: self.cmd.into_boxed_slice()
        }
    }

}

impl Drop for Finalizers {
    fn drop(&mut self) {
        let mut cursor = Cursor::default();
        let base: *mut u8 = self.mem.as_mut_slice().as_mut_ptr();
        for &cmd in &self.cmd {
            let fin = &self.finalizers[cmd];
            let ofs = cursor.alloc(fin.size as _, fin.align as _);
            unsafe { (fin.drop_in_place)(base.add(ofs) as _) }
        }
    }
}
