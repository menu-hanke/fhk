//! Memory layout and representation.

use core::cmp::max;
use core::fmt::Debug;

use alloc::vec::Vec;

use crate::bitmap::BitmapWord;
use crate::bump::BumpRef;
use crate::image::BreakpointId;
use crate::index::{index, IndexSlice, IndexVec};
use crate::ir::{PhiId, Type};
use crate::mcode::MCodeOffset;
use crate::obj::{ObjRef, TAB};

index!(pub struct ChunkId(u16) invalid(!0));

// these are the n'th occurrence of a:
// * VAR in the STATE table
// * VAR in the QUERY table
// * QUERY
// respectively. the obj->occurrence or occurrence->obj map isn't stored anywhere explicitly,
// but it's used implicitly in a few places when iterating through objects.
index!(pub struct ResetId(u16) debug("r{}"));
index!(pub struct ParamId(u16) debug("p{}"));
index!(pub struct QueryId(u16) debug("q{}"));

// reset occurrences are offset by one. the first "occurrence" is a "pseudo-reset" applied to
// all functions that depend on query parameters.
impl ResetId {
    pub const QUERY: Self = Self(0);
}

pub type Offset = u32;

// offset + bit
#[derive(Clone, Copy, Default, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable,
    PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct BitOffset(u32);

impl BitOffset {

    pub const INVALID: Self = Self(!0);

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

    pub fn align_byte(self, align: Offset) -> Self {
        Self::new_byte((self.byte() + ((self.bit() > 0) as Offset) + align - 1) & !(align - 1))
    }

    pub fn align_byte_bit(self, align: Offset) -> Self {
        if self.byte() & (align - 1) == 0 {
            self
        } else {
            self.align_byte(align)
        }
    }

    pub fn next_byte(self, offset: Offset) -> Self {
        Self::new_byte(self.byte() + offset)
    }

    pub fn next_bit_in_byte_wrapping(self) -> Self {
        Self::new(self.byte(), ((self.bit()+1) & 0x7) as _)
    }

    pub fn next_bit(self) -> Self {
        match self.bit() {
            7 => self.next_byte(1),
            _ => self.next_bit_in_byte_wrapping()
        }
    }

}

impl Debug for BitOffset {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.bit() {
            0 => write!(f, "{}", self.byte()),
            _ => write!(f, "{}.{}", self.byte(), self.bit())
        }
    }
}

// static / obj
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::IntoBytes)]
#[repr(transparent)]
pub struct SizeClass(u32);

impl SizeClass {

    pub const INVALID: Self = Self(!0);
    pub const GLOBAL: Self = Self::static_class(1);

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

impl Debug for SizeClass {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_dynamic() {
            let tab: ObjRef<TAB> = zerocopy::transmute!(!self.0);
            write!(f, "Dynamic({:?})", tab)
        } else if *self == Self::GLOBAL {
            write!(f, "Global")
        } else {
            write!(f, "Static({})", self.0)
        }
    }
}

// TODO: struct slot = bitoffset + colocated bit
pub struct Chunk {
    pub check: BitOffset,
    // slot info in ccx.bump, one for each ret phi
    pub slots: BumpRef<IndexSlice<PhiId, BitOffset>>,
    pub dynslots: MCodeOffset
}

// repr(C) structs are used directly by host.
// do not change layout without updating host as well.

#[derive(Default)]
#[repr(C)]
pub struct Param {
    pub check: BitOffset,
    pub value: BitOffset,
    pub size: u32
}

#[derive(Default)]
#[repr(C)]
pub struct Query {
    pub mcode: MCodeOffset,
    pub params_end: u32,
    pub vmctx_start: u32,
    pub vmctx_end: u32
}

#[derive(Default)]
#[repr(C)]
pub struct Reset {
    pub mask: BitmapWord<BreakpointId>
}

pub struct Layout {
    pub chunks: IndexVec<ChunkId, Chunk>,
    pub params: IndexVec<ParamId, Param>,
    // the following are only used by the host and not the emitter:
    pub queries: IndexVec<QueryId, Query>,
    pub query_params: Vec<ParamId>,
    pub resets: IndexVec<ResetId, Reset>
}

impl Default for Layout {
    fn default() -> Self {
        let mut resets: IndexVec<ResetId, Reset> = Default::default();
        resets.push(Reset { mask: BitmapWord::ones() });
        Self {
            chunks: Default::default(),
            params: Default::default(),
            queries: Default::default(),
            query_params: Default::default(),
            resets
        }
    }
}

// utility for allocating memory slots.
// CursorA remembers alignment, Cursor doesn't.
// TODO: remove these and just use (Bit)Offset instead
#[derive(Clone, Copy, Default)]
pub struct Cursor { pub ptr: usize }
#[derive(Clone, Copy)]
pub struct CursorA { pub ptr: usize, pub align: usize }

pub trait CursorType {

    fn align_ptr(&mut self, align: usize) -> &mut usize;

    fn align(&mut self, align: usize) -> usize {
        debug_assert!(align.is_power_of_two());
        *self.align_ptr(align)
    }

    fn alloc(&mut self, size: usize, align: usize) -> usize {
        let ptr = self.align_ptr(align);
        let ret = *ptr;
        *ptr += size;
        ret
    }

    fn alloc_type(&mut self, ty: Type) -> usize {
        let size = ty.size();
        self.alloc(size, size)
    }

}

impl CursorType for Cursor {
    fn align_ptr(&mut self, align: usize) -> &mut usize {
        self.ptr = (self.ptr + align - 1) & !(align - 1);
        &mut self.ptr
    }
}

impl CursorType for CursorA {
    fn align_ptr(&mut self, align: usize) -> &mut usize {
        self.ptr = (self.ptr + align - 1) & !(align - 1);
        self.align = max(self.align, align);
        &mut self.ptr
    }
}

impl Default for CursorA {
    fn default() -> Self {
        Self { ptr: 0 , align: 1 }
    }
}
