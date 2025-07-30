//! Intern table.

use core::cmp::max;
use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::Range;

use hashbrown::hash_table::Entry;
use hashbrown::HashTable;

use crate::bump::{self, as_bytes, Bump, BumpPtr, BumpRef};
use crate::hash::fxhash;

// for sized T, this is a BumpRef<T>
// for unsized T, this is an intern::Ref
#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct Interned<T: ?Sized>(u32, PhantomData<T>);

pub trait InternType {
    fn from_raw_ref(r: Ref) -> Interned<Self>;
    fn ptr(handle: Interned<Self>) -> usize;
    fn get(intern: &InternPtr, handle: Interned<Self>) -> &Self;
    fn get_range(intern: &InternPtr, handle: Interned<Self>) -> Range<usize>;
}

/*
 *  +-------+------+
 *  | 31..4 | 3..0 |
 *  +-------+------+
 *  |  ptr  | size |
 *  +-------+------+
 *
 *  size = 0..14  -> size in bytes
 *         15 -> size is stored in 4 bytes preceding ptr (aligned)
 */
#[derive(Clone, Copy, PartialEq, Eq, Hash, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
pub struct Ref(u32);

pub struct Intern {
    bump: Bump,
    tab: HashTable<Ref>,
}

#[repr(transparent)]
pub struct InternPtr {
    bump: BumpPtr
}

impl Ref {

    const EMPTY: Self = Self(0);
    const MAX_SMALL: usize = 14;

    const fn new_small(ptr: usize, size: usize) -> Self {
        debug_assert!(size <= Self::MAX_SMALL as _);
        Self(((ptr as u32) << 4) | (size as u32))
    }

    fn new_big(ptr: usize) -> Self {
        Self(((ptr as u32) << 4) | 0xf)
    }

    fn smallsize(self) -> Option<usize> {
        match (self.0 as usize) & 0xf {
            0xf => None,
            s => {
                debug_assert!(s > 0 || self == Self::EMPTY);
                Some(s)
            }
        }
    }

    fn ptr(self) -> usize {
        (self.0 as usize) >> 4
    }

}

impl<T: ?Sized> Clone for Interned<T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<T: ?Sized> Copy for Interned<T> {}

impl<T: ?Sized> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: ?Sized> Eq for Interned<T> {}

impl<T: ?Sized> Hash for Interned<T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<T: ?Sized> Interned<T> {

    pub fn ptr(self) -> usize
        where T: InternType
    {
        T::ptr(self)
    }

}

impl<T> Interned<[T]> {

    pub const EMPTY: Self = zerocopy::transmute!(Ref::EMPTY);

    pub const fn small_from_raw_parts(ptr: usize, len: usize) -> Self {
        zerocopy::transmute!(Ref::new_small(ptr, len))
    }

    pub fn is_empty(self) -> bool {
        self == Self::EMPTY
    }

}

impl Default for Intern {
    fn default() -> Self {
        let mut tab = HashTable::new();
        tab.insert_unique(fxhash(&[0;0]), Ref::EMPTY, |_| unreachable!());
        Self { tab, bump: Default::default() }
    }
}

// safety: bump and r must come from the same intern table
unsafe fn refsize(bump: *const u8, r: Ref) -> usize {
    match r.smallsize() {
        Some(s) => s,
        None => (unsafe { *(bump.add(r.ptr()) as *const u32).sub(1) }) as _
    }
}

// safety: bump and r must come from the same intern table
unsafe fn refbytes<'a>(bump: *const u8, r: Ref) -> &'a [u8] {
    unsafe { core::slice::from_raw_parts(bump.add(r.ptr()), refsize(bump, r)) }
}

// safety: bump and r must come from the same intern table
unsafe fn refmatch(bump: *const u8, r: Ref, bytes: &[u8], align: usize) -> bool {
    ((unsafe { refbytes(bump, r) }) == bytes) && (r.ptr() & (align-1) == 0)
}

// safety: tab and bump must come from the same intern table
unsafe fn entry<'a, 'tab>(
    tab: &'tab mut HashTable<Ref>,
    bump: *const u8,
    bytes: &'a [u8],
    align: usize
) -> Entry<'tab, Ref> {
    tab.entry(
        fxhash(bytes),
        |&r| unsafe { refmatch(bump, r, bytes, align) },
        |&r| fxhash(unsafe { refbytes(bump, r) })
    )
}

fn newbigref(bump: &mut Bump, len: usize, align: usize) -> Ref {
    bump.align_for::<u32>();
    let base = bump.end();
    bump.align(align);
    if bump.end().ptr() - base.ptr() < size_of::<u32>() {
        bump.reserve_dst::<[u8]>(max(align, size_of::<u32>()));
    }
    let ptr = bump.end();
    bump[ptr.cast::<u32>().offset(-1)] = len as _;
    Ref::new_big(ptr.ptr())
}

fn internbytes(intern: &mut Intern, bytes: &[u8], align: usize) -> Ref {
    match unsafe { entry(&mut intern.tab, intern.bump.as_slice().as_ptr(), bytes, align) } {
        Entry::Occupied(e) => *e.get(),
        Entry::Vacant(e) => {
            let r = if bytes.len() > Ref::MAX_SMALL {
                newbigref(&mut intern.bump, bytes.len(), align)
            } else {
                intern.bump.align(align);
                Ref::new_small(intern.bump.end().ptr(), bytes.len())
            };
            intern.bump.write(bytes);
            e.insert(r);
            r
        }
    }
}

fn findbytes(intern: &Intern, bytes: &[u8], align: usize) -> Option<Ref> {
    intern.tab.find(
        fxhash(bytes),
        |&r| unsafe { refmatch(intern.bump.as_slice().as_ptr(), r, bytes, align) }
    ).cloned()
}

impl<T> InternType for T
    where T: bump::FromBytes + bump::IntoBytes + bump::Immutable
{

    fn from_raw_ref(r: Ref) -> Interned<T> {
        zerocopy::transmute!(BumpRef::<T>::from_ptr(r.ptr()))
    }

    fn ptr(handle: Interned<T>) -> usize {
        let ptr: BumpRef<T> = zerocopy::transmute!(handle);
        ptr.ptr()
    }

    fn get(intern: &InternPtr, handle: Interned<T>) -> &T {
        let ptr: BumpRef<T> = zerocopy::transmute!(handle);
        &intern.bump[ptr]
    }

    fn get_range(_: &InternPtr, handle: Interned<T>) -> Range<usize> {
        let ptr: BumpRef<T> = zerocopy::transmute!(handle);
        let start = ptr.ptr();
        start..start+size_of::<T>()
    }

}

fn refsize_checked(bump: &BumpPtr, r: Ref) -> usize {
    match r.smallsize() {
        Some(s) => s,
        None => {
            let p: BumpRef<u32> = BumpRef::from_ptr(r.ptr());
            bump[p.offset(-1)] as usize
        }
    }
}

impl<T> InternType for [T]
    where T: bump::FromBytes + bump::IntoBytes + bump::Immutable
{

    fn from_raw_ref(r: Ref) -> Interned<Self> {
        zerocopy::transmute!(r)
    }

    fn ptr(handle: Interned<Self>) -> usize {
        let r: Ref = zerocopy::transmute!(handle);
        r.ptr()
    }

    fn get(intern: &InternPtr, handle: Interned<Self>) -> &Self {
        let r: Ref = zerocopy::transmute!(handle);
        intern.bump.get_dst(BumpRef::from_ptr(r.ptr()),
            refsize_checked(&intern.bump, r) / size_of::<T>())
    }

    fn get_range(intern: &InternPtr, handle: Interned<Self>) -> Range<usize> {
        let r: Ref = zerocopy::transmute!(handle);
        let start = r.ptr();
        start..start+refsize_checked(&intern.bump, r)
    }

}

impl Intern {

    pub fn intern<T>(&mut self, value: &T) -> Interned<T>
        where T: ?Sized + bump::Aligned + bump::IntoBytes + InternType
    {
        T::from_raw_ref(internbytes(self, as_bytes(value), T::ALIGN))
    }

    pub fn intern_range(&mut self, Range { start, end }: Range<usize>) -> Interned<[u8]> {
        let bump = self.bump.as_slice();
        <_>::from_raw_ref(match unsafe { entry(&mut self.tab, bump.as_ptr(), &bump[start..end], 1) } {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let len = end-start;
                let r = if len > Ref::MAX_SMALL {
                    let r = newbigref(&mut self.bump, len, 1);
                    self.bump.write_range::<u8>(BumpRef::from_ptr(start)..BumpRef::from_ptr(end));
                    r
                } else {
                    Ref::new_small(start, len)
                };
                e.insert(r);
                r
            }
        })
    }

    pub fn find<T>(&self, value: &T) -> Option<Interned<T>>
        where T: ?Sized + bump::Aligned + bump::IntoBytes + InternType
    {
        findbytes(self, as_bytes(value), T::ALIGN).map(T::from_raw_ref)
    }

}

impl InternPtr {

    fn get<T>(&self, handle: Interned<T>) -> &T
        where T: ?Sized + InternType
    {
        T::get(self, handle)
    }

    pub fn get_range<T>(&self, handle: Interned<T>) -> Range<usize>
        where T: ?Sized + InternType
    {
        T::get_range(self, handle)
    }

    pub fn as_slice(&self) -> &[u8] {
        self.bump.as_slice()
    }

}

impl core::ops::Deref for Intern {
    type Target = InternPtr;
    fn deref(&self) -> &Self::Target {
        let ptr: &BumpPtr = &*self.bump;
        unsafe { core::mem::transmute(ptr) }
    }
}

impl<T> core::ops::Index<Interned<T>> for InternPtr
    where T: ?Sized + InternType
{
    type Output = T;
    fn index(&self, index: Interned<T>) -> &Self::Output {
        self.get(index)
    }
}
