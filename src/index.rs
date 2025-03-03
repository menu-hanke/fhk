//! Index newtypes and collections.

// most of this is yoinked from rustc:
// https://github.com/rust-lang/rust/tree/master/compiler/rustc_index

use core::cell::UnsafeCell;
use core::fmt::Debug;
use core::marker::PhantomData;
use core::mem::transmute;
use core::ops::{Deref, DerefMut, Range};

use alloc::boxed::Box;
use alloc::vec::Vec;

pub trait Index : From<usize> + Into<usize> + Clone + Copy
    + zerocopy::FromBytes + zerocopy::IntoBytes + zerocopy::Immutable { }
pub trait InvalidValue { const INVALID: usize; }
impl Index for usize {}

#[repr(transparent)]
pub struct IndexSlice<I: Index, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T]
}

impl<I: Index, T> IndexSlice<I, T> {

    pub fn from_raw(raw: &[T]) -> &Self {
        unsafe { transmute(raw) }
    }

    pub fn from_raw_mut(raw: &mut [T]) -> &mut Self {
        unsafe { transmute(raw) }
    }

    pub fn ptr_from_raw(raw: *const [T]) -> *const Self {
        unsafe { transmute(raw) }
    }

    pub fn from_raw_box(raw: Box<[T]>) -> Box<Self> {
        unsafe { transmute(raw) }
    }

    pub fn end(&self) -> I {
        self.raw.len().into()
    }

    pub fn pairs(&self) -> core::iter::Zip<
            core::iter::Map<Range<usize>, fn(usize) -> I>,
            core::slice::Iter<T>>
    {
        iter_span(self.end()).zip(self.raw.iter())
    }

    pub fn pairs_mut(&mut self) -> core::iter::Zip<
            core::iter::Map<Range<usize>, fn(usize) -> I>,
            core::slice::IterMut<T>>
    {
        iter_span(self.end()).zip(self.raw.iter_mut())
    }

}

impl<I: Index, T> core::ops::Index<I> for IndexSlice<I, T> {
    type Output = T;
    fn index(&self, index: I) -> &T {
        &self.raw[index.into()]
    }
}

impl<I: Index, T> core::ops::IndexMut<I> for IndexSlice<I, T> {
    fn index_mut(&mut self, index: I) -> &mut T {
        &mut self.raw[index.into()]
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct IndexArray<I: Index, T, const N: usize> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T; N]
}

impl<I: Index, T: Default+Copy, const N: usize> Default for IndexArray<I, T, N> {
    fn default() -> Self {
        Self {
            _marker: PhantomData,
            raw: [T::default(); N]
        }
    }
}

impl<I: Index, T, const N: usize> Deref for IndexArray<I, T, N> {
    type Target = IndexSlice<I, T>;
    fn deref(&self) -> &IndexSlice<I, T> {
        IndexSlice::from_raw(&self.raw)
    }
}

impl<I: Index, T, const N: usize> DerefMut for IndexArray<I, T, N> {
    fn deref_mut(&mut self) -> &mut IndexSlice<I, T> {
        IndexSlice::from_raw_mut(&mut self.raw)
    }
}

#[repr(transparent)]
pub struct IndexVec<I: Index, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: Vec<T>
}

impl<I: Index, T> IndexVec<I, T> {

    pub fn push(&mut self, value: T) -> I {
        let idx = self.raw.len().into();
        self.raw.push(value);
        idx
    }

    pub fn clear(&mut self) {
        self.raw.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

}

impl<I: Index, T> Default for IndexVec<I, T> {
    fn default() -> Self {
        Self { _marker: PhantomData, raw: Default::default() }
    }
}

impl<I: Index, T> Deref for IndexVec<I, T> {
    type Target = IndexSlice<I, T>;
    fn deref(&self) -> &IndexSlice<I, T> {
        IndexSlice::from_raw(&self.raw)
    }
}

impl<I: Index, T> DerefMut for IndexVec<I, T> {
    fn deref_mut(&mut self) -> &mut IndexSlice<I, T> {
        IndexSlice::from_raw_mut(&mut self.raw)
    }
}

#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct IndexOption<I: Index+InvalidValue> {
    pub raw: I
}

impl<I: Index+InvalidValue> From<IndexOption<I>> for Option<I> {
    fn from(value: IndexOption<I>) -> Self {
        if value.raw.into() == I::INVALID {
            None
        } else {
            Some(value.raw)
        }
    }
}

impl<I: Index+InvalidValue> From<Option<I>> for IndexOption<I> {
    fn from(value: Option<I>) -> Self {
        Self {
            raw: match value {
                Some(idx) => idx,
                None      => I::INVALID.into()
            }
        }
    }
}

impl<I: Index+InvalidValue> Default for IndexOption<I> {
    fn default() -> Self {
        Self { raw: I::INVALID.into() }
    }
}

impl<I: Index+InvalidValue+Debug> Debug for IndexOption<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.unpack().fmt(f)
    }
}

impl<I: Index+InvalidValue> IndexOption<I> {

    pub fn unpack(self) -> Option<I> {
        self.into()
    }

    pub fn is_none(self) -> bool {
        self.raw.into() == I::INVALID
    }

    pub fn is_some(self) -> bool {
        !self.is_none()
    }

    pub fn unwrap(self) -> I {
        debug_assert!(self.is_some());
        self.raw
    }

}

// interior mutability vec type that doesn't hand out slices but can be modified through
// shared references.
// this is NOT the same as IndexVec<I, Cell<T>>: this allows pushing and popping through shared
// references, but does NOT deref to slice. this type can NEVER hand out a reference from a
// method taking &self. handing out refs from &mut self is fine though.
#[repr(transparent)]
pub struct IndexValueVec<I: Index, T>(UnsafeCell<IndexVec<I, T>>);

impl<I: Index, T> Default for IndexValueVec<I, T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

// SAFETY for all unsafe blocks here: NO REFS HANDED TO OUTSIDE WORLD.
impl<I: Index, T> IndexValueVec<I, T> {

    pub fn push(&self, value: T) -> I {
        unsafe { &mut *self.0.get() }.push(value)
    }

    pub fn set(&self, index: I, value: T) {
        (unsafe { &mut *self.0.get() })[index] = value;
    }

    pub fn clear(&self) {
        unsafe { &mut *self.0.get() }.clear();
    }

    pub fn end(&self) -> I {
        unsafe { &*self.0.get() }.end()
    }

    pub fn is_empty(&self) -> bool {
        unsafe { &*self.0.get() }.is_empty()
    }

    pub fn extend(&self, xs: impl IntoIterator<Item=T>) -> I {
        let i = self.end();
        unsafe { &mut *self.0.get() }.raw.extend(xs);
        i
    }

    pub fn inner_mut(&mut self) -> &mut IndexVec<I, T> {
        self.0.get_mut()
    }

    pub fn take_inner(&self) -> IndexVec<I, T> {
        core::mem::take(unsafe { &mut *self.0.get() })
    }

    pub fn swap_inner(&self, data: &mut IndexVec<I, T>) {
        core::mem::swap(unsafe { &mut *self.0.get() }, data);
    }

    pub fn replace_inner(&self, data: IndexVec<I, T>) -> IndexVec<I, T> {
        core::mem::replace(unsafe { &mut *self.0.get() }, data)
    }

    // pub fn pairs_mut(&mut self) -> core::iter::Zip<
    //         core::iter::Map<Range<usize>, fn(usize) -> I>,
    //         core::slice::IterMut<T>>
    // {
    //     self.inner_mut().pairs_mut()
    // }

}

// SAFETY for all unsafe blocks here: NO REFS HANDED TO OUTSIDE WORLD.
impl<I: Index, T: Clone> IndexValueVec<I, T> {

    pub fn at(&self, index: I) -> T {
        (unsafe { &*self.0.get() })[index].clone()
    }

    pub fn pairs(&self) -> IndexValueVecIter<'_, I, T> {
        IndexValueVecIter { vec: self, index: 0 }
    }

}

pub struct IndexValueVecIter<'a, I: Index, T> {
    vec: &'a IndexValueVec<I, T>,
    index: usize
}

impl<'a, I: Index, T: Clone> Iterator for IndexValueVecIter<'a, I, T> {
    type Item = (I, T);
    fn next(&mut self) -> Option<(I, T)> {
        let index = self.index;
        match unsafe { &*self.vec.0.get() }.raw.get(index) {
            Some(v) => {
                self.index += 1;
                Some((index.into(), v.clone()))
            },
            None => None
        }
    }
}

pub fn iter_range<I: Index>(range: Range<I>) -> core::iter::Map<Range<usize>, fn(usize) -> I> {
    (range.start.into()..range.end.into()).map(Into::into)
}

pub fn iter_span<I: Index>(end: I) -> core::iter::Map<Range<usize>, fn(usize) -> I> {
    iter_range(0.into()..end)
}

macro_rules! index {
    (
        $vis:vis struct $name:ident($inner:ty)
        $(default($default:expr))?
        $(invalid($invalid:expr))?
        $(debug($debug:literal))?
    ) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
            zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
        #[repr(transparent)]
        $vis struct $name($inner);
        impl From<usize> for $name { fn from(v: usize) -> Self { Self(v as _) } }
        impl From<$name> for usize { fn from(v: $name) -> Self { v.0 as _ } }
        impl core::ops::Add<isize> for $name {
            type Output = Self;
            fn add(self, rhs: isize) -> Self { Self(self.0.wrapping_add(rhs as _)) }
        }
        impl core::ops::Sub<isize> for $name {
            type Output = Self;
            fn sub(self, rhs: isize) -> Self { self + (-rhs) }
        }
        impl core::ops::AddAssign<isize> for $name {
            fn add_assign(&mut self, rhs: isize) { *self = *self + rhs }
        }
        impl core::ops::SubAssign<isize> for $name {
            fn sub_assign(&mut self, rhs: isize) { *self = *self - rhs }
        }
        impl crate::index::Index for $name {}
        $( impl Default for $name { fn default() -> Self { Self($default) } })?
        $(
            impl crate::index::InvalidValue for $name {
                const INVALID: usize = $invalid as $inner as usize;
            }
        )?
        $(
            impl core::fmt::Debug for $name {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    write!(f, $debug, self.0)
                }
            }
        )?
    };
}

pub(crate) use index;
