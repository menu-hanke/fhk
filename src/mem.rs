//! Memory layout and representation.

use zerocopy::Unalign;

use crate::bitmap::bitmap_array;
use crate::hash::HashMap;
use crate::index::{index, IndexArray};
use crate::obj::{ObjRef, TAB};

pub type Offset = u32;

// user code identifier for grouping vars/models that should be reset together.
// could support an arbitrary amount, but 99.9% of users only need a few of these.
// if we allocate the max amount, we simply start over. resetting "too many" slots is always
// correct, it just may cause unnecessary recomputation. (in fact, always resetting everything
// is correct, too).
// note: reset allocation should start at 1. zero is the global reset which contains everything and
// can be used to create a fresh instance.
index!(pub struct ResetId(u8));

// breakpoints divide the instance memory into intervals that are reset together.
// like reset ids, it's possible to allow an arbitrary amount, but restricting to 64 simplifies
// data structures. note that the number of breakpoints is not related to the number of reset ids.
// if the layout would naturally produce too many breakpoints, the layout algorithm will merge
// them until there are at most MAXNUM.
index!(pub struct BreakpointId(u8));

impl ResetId {
    pub const GLOBAL: Self = Self(0);
    pub const MAXNUM: usize = 64;
}

impl BreakpointId {
    pub const MAXNUM: usize = 64;
}

// bitmap of reset ids
pub type ResetSet = bitmap_array![ResetId; ResetId::MAXNUM];

// map of object -> reset ids (ie. when user code issues any of the resets, it should reset the
// object.)
#[derive(Default)]
pub struct ResetMap {
    pub raw: HashMap<ObjRef/*VAR|MOD*/, Unalign<ResetSet>>
}

// bitmap of breakpoints (intervals)
pub type ResetMask = bitmap_array![BreakpointId; BreakpointId::MAXNUM];

// breakpoint memory offsets.
pub type Breakpoints = IndexArray<BreakpointId, Offset, {BreakpointId::MAXNUM+1}>;

// reset -> bitmap of breakpoints (intervals). multiple resets can be issued at once by OR'ing the
// masks.
pub type ResetAssignment = IndexArray<ResetId, ResetMask, {ResetId::MAXNUM}>;

// offset + bit
#[derive(Clone, Copy, Default, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct Slot(u32);

impl Slot {

    // TODO: should distinguish between "has a bit" and "doesn't have a bit",
    // so that non-colocated B1s can be expressed.
    // OR, alternatively, have an optimization pass turn them into I8s.
    // (this is probably cleaner)
    pub fn new(byte: Offset, bit: u8) -> Self {
        Self((byte << 3) | (bit as u32))
    }

    pub fn new_byte(byte: Offset) -> Self {
        Self::new(byte, 0)
    }

    pub fn byte(self) -> u32 {
        self.0 >> 3
    }

    pub fn bit(self) -> u32 {
        self.0 & 0x7
    }

}

#[derive(Default)]
pub struct Layout {
    pub breakpoints: Breakpoints,
    pub reset: ResetAssignment,
    pub size: Offset
}

// static / obj
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::IntoBytes)]
#[repr(transparent)]
pub struct SizeClass(u32);

impl SizeClass {

    pub const INVALID: Self = Self(!0);
    pub const GLOBAL: Self = Self::static_class(1);

    pub fn slot_size(self) -> Offset {
        todo!()
    }

    pub const fn static_class(size: u32) -> Self {
        Self(size)
    }

    pub const fn dynamic_class(tab: ObjRef<TAB>) -> Self {
        Self(!zerocopy::transmute!(tab))
    }

    pub fn is_dynamic(self) -> bool {
        (self.0 as i32) < 0
    }

}

pub struct Resets {
    next: ResetId,
    defs: ResetMap,
}

impl Resets {

    pub fn newid(&mut self) -> ResetId {
        let id = self.next;
        self.next.0 = (self.next.0 + 1) & 0x3f;
        id
    }

}

impl Default for Resets {
    fn default() -> Self {
        Self {
            next: ResetId(1),  // zero is the global reset, user resets start from 1
            defs: Default::default()
        }
    }
}

pub unsafe fn applyreset(mem: *mut u8, breakpoints: &Breakpoints, mut reset: u64) {
    let mut idx = 0;
    while reset != 0 {
        let num0 = reset.trailing_zeros() as usize;
        reset >>= num0;
        let num1 = reset.trailing_ones() as usize;
        reset >>= num1;
        let start = *breakpoints.raw.get_unchecked(idx+num0) as usize;
        let end = *breakpoints.raw.get_unchecked(idx+num0+num1) as usize;
        idx += num0+num1;
        core::ptr::write_bytes(mem.add(start), 0, end-start);
    }
}
