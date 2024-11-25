//! Bump allocator.

// Q: why not use one of the 294 thousand existing arena/bump crates?
// A: none of them (afaik) have all of the following in one lib:
//    * support mixed types, including slices and trailing VLAs
//    * support both static and dynamic alignment
//    * 32-bit plain integer pointers into one flat array
//    * no lifetimes (on pointers)
//    * no refcell/freelist/atomics etc overhead
// iow a special purpose data structure works better here than a general purpose one (as is
// typical).

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut, Range, RangeFrom};
use core::ptr::NonNull;

use alloc::alloc::Layout;

const MAX_ALIGN: usize = 16;

// need repr(C) to transmute between Bump<W1> and Bump<W2>
#[repr(C)]
pub struct Bump<W=u8> {
    ptr: NonNull<u8>,
    len: u32, // in bytes
    cap: u32, // in bytes
    _marker: PhantomData<fn(&W)>
}

// one less pointer chase for when you don't need to push stuff.
// same idea as vec (bump) vs slice (bumpptr)
// invariant: pointer and length are both aligned to MAX_ALIGN
#[repr(transparent)]
pub struct BumpPtr([u8]);

// note: this counts multiples of *alignment*, not size.
// Q1: why not count multiples of size?
// A1: division by non-power-of-2 is painful
// Q2: why not count bytes then?
// A2: because then it would be possible to represent unaligned pointers
#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct BumpRef<T: ?Sized>(u32, PhantomData<T>);

// #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
// #[repr(C)]
// struct BumpSliceRaw { ptr: u32, len: u32 }
//
// // "fat pointer" with length (multiples of *alignments*, not elements).
// // this is defined in a funny way (with the BumpSliceRaw struct) because it must be
// // repr(transparent) to implement the zerocopy traits, but it also should be aligned to 4 (and not
// // 8, like if it was defined with a single u64).
// #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
// #[repr(transparent)]
// pub struct BumpSlice<T>(BumpSliceRaw, PhantomData<T>);

pub unsafe trait Write {
    fn write(&self, bump: &mut Bump);
}

pub unsafe trait Read {
    fn read(base: *const u8, ptr: usize, len: usize) -> *const Self;
}

// NOTE: this is *not* the alignment of the type itself; it is the alignment the type requires
// for writing/reading. in particular, types that implement Write but not Read may have
// Alignment::ALIGN < align_of::<Self>()    (see obj.rs and trailing &[slice])
pub unsafe trait Aligned {
    const ALIGN: usize;
}

// the idea here is that these are equivalent to zerocopy::Intobytes+zerocopy::Immutable
// and zerocopy::FromBytes respectively, but they can be implemented manually where zerocopy's
// analysis fails. ideally these wouldn't be needed if zerocopy's analysis was better.
// (the main problems are slices/DSTs and generics)
pub unsafe trait WriteBytes {}
pub unsafe trait ReadBytes {}
unsafe impl<T: ?Sized + zerocopy::IntoBytes + zerocopy::Immutable> WriteBytes for T {}
unsafe impl<T: ?Sized + zerocopy::FromBytes> ReadBytes for T {}

// do *not* auto implement for all T.
// write-only types should explicitly set their required alignments, because it's probably
// something else than the type's alignment.
unsafe impl<T: ReadBytes> Aligned for T {
    const ALIGN: usize = align_of::<T>();
}

unsafe impl<T: ReadBytes> Aligned for [T] {
    const ALIGN: usize = align_of::<T>();
}

unsafe impl Aligned for str {
    const ALIGN: usize = 1;
}

pub fn as_bytes<T: ?Sized + WriteBytes>(value: &T) -> &[u8] {
    unsafe {
        core::slice::from_raw_parts(
            value as *const T as *const u8,
            size_of_val(value)
        )
    }
}

unsafe impl<T: ?Sized + WriteBytes> Write for T {
    fn write(&self, bump: &mut Bump) {
        // TODO: special case for 1, 2, 4, 8 here.
        // compiler doesn't know bump is aligned.
        bump.push_slice(as_bytes(self))
    }
}

unsafe impl<T: ReadBytes> Read for T {
    fn read(base: *const u8, ptr: usize, len: usize) -> *const Self {
        if ptr + size_of::<T>() <= len {
            unsafe { base.add(ptr) }.cast()
        } else {
            core::ptr::null()
        }
    }
}

impl<T: ?Sized> BumpRef<T> {

    pub fn zero() -> Self {
        Self(0, PhantomData)
    }

    pub fn from_align_index(idx: u32) -> Self {
        Self(idx, PhantomData)
    }

    pub fn align_index(self) -> usize {
        self.0 as _
    }

    pub fn add_align(self, offset: isize) -> Self {
        Self::from_align_index((self.0 as isize + offset) as _)
    }

}

impl<T: Aligned> BumpRef<T> {

    pub fn size_index(self) -> usize {
        self.align_index() * size_of::<T>() / T::ALIGN
    }

    pub fn add_size(self, offset: isize) -> Self {
        self.add_align(offset * ((size_of::<T>() / T::ALIGN) as isize))
    }

}

impl<T: ?Sized + Aligned> BumpRef<T> {

    pub fn cast<U: ?Sized + Aligned>(self) -> BumpRef<U> {
        debug_assert!(self.0 * T::ALIGN as u32 % U::ALIGN as u32 == 0);
        BumpRef(self.0 * T::ALIGN as u32 / U::ALIGN as u32, PhantomData)
    }

    pub fn from_offset(ofs: usize) -> Self {
        Self((ofs/T::ALIGN) as u32, PhantomData)
    }

    pub fn offset(self) -> usize {
        self.0 as usize * T::ALIGN
    }

}

impl<T: ?Sized> Clone for BumpRef<T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<T: ?Sized> Copy for BumpRef<T> {}

impl<T: ?Sized> PartialEq for BumpRef<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: ?Sized> Eq for BumpRef<T> {}

impl<T: ?Sized> PartialOrd for BumpRef<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<T: ?Sized> Ord for BumpRef<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T: ?Sized> Hash for BumpRef<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.0)
    }
}

// Q: why is this needed?
// A: if T has too high alignment, then we can't guarantee that base+ptr stays aligned
//    after a realloc (or if the pointer is used with the wrong Bump).
// this is why *reads* must ensure T has low enough alignment. writes don't need to care,
// as the pointer is aligned just before the write.
fn check_alignment<T: ?Sized + Aligned>() {
    const { assert!(T::ALIGN <= MAX_ALIGN) }
}

impl<W> Bump<W> {

    pub fn new() -> Self {
        Self {
            ptr: NonNull::new(MAX_ALIGN as _).unwrap(),
            len: 0,
            cap: 0,
            _marker: PhantomData
        }
    }

    #[cold]
    fn grow(&mut self) {
        let mut cap = self.cap;
        if cap == 0 { cap = 64; }
        while cap < self.len { cap *= 2 }
        let ptr = match self.cap {
            0 => unsafe {
                alloc::alloc::alloc(Layout::from_size_align_unchecked(cap as _, MAX_ALIGN))
            },
            c => unsafe {
                alloc::alloc::realloc(
                    self.ptr.as_ptr(),
                    Layout::from_size_align_unchecked(c as _, MAX_ALIGN),
                    cap as _
                )
            }
        };
        self.cap = cap;
        self.ptr = NonNull::new(ptr).unwrap();
    }

    fn checksize(&mut self) {
        if self.len > self.cap {
            self.grow();
        }
    }

    pub fn align(&mut self, align: u32) {
        let newlen = (self.len + align - 1) & !(align - 1);
        if newlen > self.len {
            self.len = newlen;
            self.checksize();
            for i in self.len..newlen {
                unsafe { *self.ptr.as_ptr().add(i as _) = 0 }
            }
        }
    }

}

impl<W: Aligned> Bump<W> {

    pub fn push<T>(&mut self, value: &T) -> BumpRef<T>
        where T: ?Sized + Write + Aligned
    {
        if T::ALIGN > W::ALIGN {
            self.align(T::ALIGN as _);
        }
        let ptr = self.len / T::ALIGN as u32;
        value.write(unsafe { core::mem::transmute(&mut *self) });
        if T::ALIGN < W::ALIGN {
            self.align(W::ALIGN as _);
        }
        BumpRef(ptr, PhantomData)
    }

    pub fn push_zeroed_slice<T>(&mut self, len: usize) -> (BumpRef<T>, &mut [T])
        where T: ReadBytes + WriteBytes
    {
        let len0 = self.len;
        if T::ALIGN > W::ALIGN {
            // don't call align() here, include it in the padding
            self.len = (self.len + T::ALIGN as u32 - 1) & !(T::ALIGN as u32 - 1);
        }
        let start = self.len;
        self.len += (len*size_of::<T>()) as u32;
        self.checksize();
        unsafe {
            // this must also zero padding bytes since someone could read them
            core::ptr::write_bytes(
                self.ptr.as_ptr().add(len0 as _),
                0,
                (self.len - len0) as _
            );
        }
        let ptr = BumpRef(start/T::ALIGN as u32, PhantomData);
        let ret = unsafe {
            // this must start from `start`, not `len0` which is unaligned
            core::slice::from_raw_parts_mut(
                self.ptr.as_ptr().add(start as _).cast(),
                len
            )
        };
        (ptr, ret)
    }

    pub fn next<T: ?Sized + Aligned>(&self) -> BumpRef<T> {
        let mut ptr = self.len;
        if T::ALIGN > W::ALIGN {
            ptr = (ptr + T::ALIGN as u32 - 1) & !(T::ALIGN as u32 - 1);
        }
        BumpRef(ptr/T::ALIGN as u32, PhantomData)
    }

    pub fn end(&self) -> BumpRef<W> {
        self.next()
    }

    pub fn truncate(&mut self, end: BumpRef<W>) {
        let len = end.offset() as u32;
        assert!(len <= self.len);
        self.len = len;
    }

}

impl Bump {

    pub fn align_for<T>(&mut self) -> &mut Bump<T> {
        self.align(align_of::<T>() as _);
        unsafe { core::mem::transmute(self) }
    }

    // this could `data: &[W]`?
    pub fn push_slice(&mut self, data: &[u8]) {
        let ofs = self.len;
        self.len = ofs + data.len() as u32;
        self.checksize();
        unsafe {
            core::ptr::copy_nonoverlapping(
                data.as_ptr(),
                self.ptr.as_ptr().add(ofs as _),
                data.len()
            )
        }
    }

    // this could be `range: Range<BumpRef<T>>`?
    pub fn push_range(&mut self, range: Range<usize>) {
        todo!()
    }

}

impl BumpPtr {

    pub fn get<T>(&self, ptr: BumpRef<T>) -> &T
        where T: ?Sized + Read + Aligned
    {
        check_alignment::<T>();
        debug_assert!((self.0.as_ptr() as usize + ptr.offset()) % T::ALIGN == 0);
        let p = T::read(self.0.as_ptr(), ptr.offset(), self.0.len());
        assert!(!p.is_null());
        unsafe { &*p }
    }

    pub fn get_mut<T>(&mut self, ptr: BumpRef<T>) -> &mut T
        where T: ?Sized + Read + Write + Aligned
    {
        check_alignment::<T>();
        debug_assert!((self.0.as_ptr() as usize + ptr.offset()) % T::ALIGN == 0);
        let p = T::read(self.0.as_mut_ptr(), ptr.offset(), self.0.len()) as *mut T;
        assert!(!p.is_null());
        unsafe { &mut *p }
    }

    pub fn as_slice<T>(&self) -> &[T]
        where T: ReadBytes
    {
        check_alignment::<T>();
        unsafe {
            core::slice::from_raw_parts(
                self.0.as_ptr().cast(),
                self.0.len() / size_of::<T>()
            )
        }
    }

    pub fn as_mut_slice<T>(&mut self) -> &mut [T]
        where T: ReadBytes + WriteBytes
    {
        check_alignment::<T>();
        unsafe {
            core::slice::from_raw_parts_mut(
                self.0.as_mut_ptr().cast(),
                self.0.len() / size_of::<T>()
            )
        }
    }

    // safety: check alignment and length
    unsafe fn from_slice_unchecked(data: &[u8]) -> &Self {
        core::mem::transmute(data)
    }

    // safety: check alignment and length
    unsafe fn from_mut_slice_unchecked(data: &mut [u8]) -> &mut Self {
        core::mem::transmute(data)
    }

    pub fn empty() -> &'static Self {
        unsafe {
            Self::from_slice_unchecked(core::slice::from_raw_parts(MAX_ALIGN as *const u8, 0))
        }
    }

}

impl<W> Default for Bump<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Aligned> core::fmt::Write for Bump<W> {

    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.push(s);
        Ok(())
    }

}

impl<W> Drop for Bump<W> {
    fn drop(&mut self) {
        if self.cap > 0 {
            unsafe {
                alloc::alloc::dealloc(
                    self.ptr.as_ptr(),
                    Layout::from_size_align_unchecked(self.cap as _, MAX_ALIGN)
                )
            }
        }
    }
}

impl<T: ?Sized + Read + Aligned> core::ops::Index<BumpRef<T>> for BumpPtr {
    type Output = T;
    fn index(&self, index: BumpRef<T>) -> &T {
        self.get(index)
    }
}

impl<T: ?Sized + Read + Write + Aligned> core::ops::IndexMut<BumpRef<T>> for BumpPtr {
    fn index_mut(&mut self, index: BumpRef<T>) -> &mut T {
        self.get_mut(index)
    }
}

impl<T: ReadBytes> core::ops::Index<Range<BumpRef<T>>> for BumpPtr {
    type Output = [T];
    fn index(&self, index: Range<BumpRef<T>>) -> &[T] {
        &self.as_slice()[index.start.size_index()..index.end.size_index()]
    }
}

impl<T: ReadBytes + WriteBytes> core::ops::IndexMut<Range<BumpRef<T>>> for BumpPtr {
    fn index_mut(&mut self, index: Range<BumpRef<T>>) -> &mut [T] {
        &mut self.as_mut_slice()[index.start.size_index()..index.end.size_index()]
    }
}

impl<T: ReadBytes> core::ops::Index<RangeFrom<BumpRef<T>>> for BumpPtr {
    type Output = [T];
    fn index(&self, index: RangeFrom<BumpRef<T>>) -> &[T] {
        &self.as_slice()[index.start.size_index()..]
    }
}

impl<T: ReadBytes + WriteBytes> core::ops::IndexMut<RangeFrom<BumpRef<T>>> for BumpPtr {
    fn index_mut(&mut self, index: RangeFrom<BumpRef<T>>) -> &mut [T] {
        &mut self.as_mut_slice()[index.start.size_index()..]
    }
}

impl<W> Deref for Bump<W> {
    type Target = BumpPtr;
    fn deref(&self) -> &BumpPtr {
        unsafe {
            BumpPtr::from_slice_unchecked(
                core::slice::from_raw_parts(self.ptr.as_ptr(), self.len as _)
            )
        }
    }
}

impl<W> DerefMut for Bump<W> {
    fn deref_mut(&mut self) -> &mut BumpPtr {
        unsafe {
            BumpPtr::from_mut_slice_unchecked(
                core::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len as _)
            )
        }
    }
}

// impl<W: ReadBytes> Deref for BumpPtr<W> {
//     type Target = [W];
//     fn deref(&self) -> &[W] {
//         self.as_slice()
//     }
// }
// 
// impl<W: ReadBytes + WriteBytes> DerefMut for BumpPtr<W> {
//     fn deref_mut(&mut self) -> &mut [W] {
//         self.as_mut_slice()
//     }
// }

#[repr(C)]
pub struct TrailingVLA<Body, Tail> {
    body: Body,
    tail: [Tail]
}

pub unsafe fn trailing_vla_ptr<Body, Tail>(
    base: *const u8,
    ptr: usize,
    len: usize,
    num: usize
) -> *const TrailingVLA<Body, Tail> {
    if ptr + size_of::<Body>() + num*size_of::<Tail>() <= len {
        let vlabase = unsafe { base.add(ptr) };
        // this is a hack to make it work on stable.
        // replace with ptr::from_raw_parts when it stabilizes.
        core::ptr::slice_from_raw_parts(vlabase.cast::<Tail>(), num) as *const _
    } else {
        (&[]) as *const [u8] as *const _
    }
}
