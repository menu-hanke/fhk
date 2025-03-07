//! Bump allocator.

use core::alloc::Layout;
use core::any::type_name;
use core::cmp::{max, Ordering};
use core::fmt::Debug;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Deref, Range, RangeFrom};
use core::ptr::NonNull;

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

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct BumpRefOption<T: ?Sized> { pub raw: BumpRef<T> }

// safety: must have T::ALIGN >= align_of_val(t)
// (but inequality may be strict)
pub unsafe trait Aligned {
    const ALIGN: usize;
}

unsafe impl<T> Aligned for T {
    const ALIGN: usize = align_of::<T>();
}

unsafe impl<T> Aligned for [T] {
    const ALIGN: usize = align_of::<T>();
}

unsafe impl<I: index::Index, T> Aligned for IndexSlice<I, T> {
    const ALIGN: usize = align_of::<T>();
}

unsafe impl Aligned for str {
    const ALIGN: usize = 1;
}

// safety: type must have no padding and it must have the following layout:
//   struct T {
//      head: T::Head,
//      tail: [T::Item]
//   }
pub unsafe trait PackedSliceDst {
    type Head;
    type Item;
    fn ptr_from_raw_parts(addr: *const Self::Head, len: usize) -> *const Self;
}

fn size_of_dst<T>(len: usize) -> usize
    where T: ?Sized + PackedSliceDst
{
    size_of::<T::Head>() + len*size_of::<T::Item>()
}

unsafe impl<T> PackedSliceDst for [T] {
    type Head = ();
    type Item = T;
    fn ptr_from_raw_parts(addr: *const Self::Head, len: usize) -> *const Self {
        core::ptr::slice_from_raw_parts(addr.cast(), len)
    }
}

unsafe impl<I: index::Index, T> PackedSliceDst for IndexSlice<I, T> {
    type Head = ();
    type Item = T;
    fn ptr_from_raw_parts(addr: *const Self::Head, len: usize) -> *const Self {
        Self::ptr_from_raw(<[T] as PackedSliceDst>::ptr_from_raw_parts(addr, len))
    }
}

// same meaning as zerocopy traits but can be manually implemented when zerocopy's analysis fails.
pub unsafe trait FromBytes {}
pub unsafe trait IntoBytes {}
pub unsafe trait Immutable {}
unsafe impl<T> FromBytes for T where T: ?Sized + zerocopy::FromBytes {}
unsafe impl<T> IntoBytes for T where T: ?Sized + zerocopy::IntoBytes {}
unsafe impl<T> Immutable for T where T: ?Sized + zerocopy::Immutable {}

/* ---- Bump references ----------------------------------------------------- */

impl<T: ?Sized> BumpRef<T> {

    pub fn zero() -> Self {
        Self(0, PhantomData)
    }

}

impl<T: Aligned> BumpRef<T> {

    pub fn index(self) -> usize {
        (self.0 as usize) * T::ALIGN / size_of::<T>()
    }

    pub fn offset(self, offset: isize) -> Self {
        Self(((self.0 as isize) + offset * ((size_of::<T>() / T::ALIGN) as isize)) as _, PhantomData)
    }

}

impl<T: ?Sized + Aligned> BumpRef<T> {

    pub fn cast<U: ?Sized + Aligned>(self) -> BumpRef<U> {
        debug_assert!(self.0 * T::ALIGN as u32 % U::ALIGN as u32 == 0);
        BumpRef(self.0 * T::ALIGN as u32 / U::ALIGN as u32, PhantomData)
    }

    pub fn cast_up<U: ?Sized + Aligned>(self) -> BumpRef<U> {
        BumpRef((self.0 * T::ALIGN as u32 + U::ALIGN as u32 - 1) / U::ALIGN as u32, PhantomData)
    }

    pub fn from_ptr(ofs: usize) -> Self {
        Self((ofs/T::ALIGN) as u32, PhantomData)
    }

    pub fn ptr(self) -> usize {
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

impl<T: ?Sized> Debug for BumpRef<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "BumpRef<{}>({})", type_name::<T>(), self.0)
    }
}

impl<T: ?Sized> BumpRefOption<T> {

    pub const RAW_NONE: BumpRef<T> = zerocopy::transmute!(!0);

    pub fn unpack(self) -> Option<BumpRef<T>> {
        self.into()
    }

}

impl<T: ?Sized> From<Option<BumpRef<T>>> for BumpRefOption<T> {

    fn from(value: Option<BumpRef<T>>) -> Self {
        BumpRefOption { raw: value.unwrap_or(Self::RAW_NONE) }
    }

}

impl<T: ?Sized> From<BumpRefOption<T>> for Option<BumpRef<T>> {

    fn from(value: BumpRefOption<T>) -> Self {
        if value.raw == BumpRefOption::RAW_NONE {
            None
        } else {
            Some(value.raw)
        }
    }

}

impl<T: ?Sized> Default for BumpRefOption<T> {
    fn default() -> Self {
        None.into()
    }
}

impl<T: ?Sized> Clone for BumpRefOption<T> {
    fn clone(&self) -> Self {
        BumpRefOption { raw: self.raw }
    }
}

impl<T: ?Sized> Copy for BumpRefOption<T> {}

impl<T: ?Sized> PartialEq for BumpRefOption<T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<T: ?Sized> Eq for BumpRefOption<T> {}


/* ---- Bump management ----------------------------------------------------- */

impl<W> Bump<W> {

    pub fn new() -> Self {
        Self {
            ptr: NonNull::new(MAX_ALIGN as _).unwrap(),
            len: 0,
            cap: 0,
            _marker: PhantomData
        }
    }

    pub fn copy_of(data: &BumpPtr) -> Self {
        let mut bump = Self::new();
        bump.write(data.as_slice::<u8>());
        bump
    }

}

impl<W> Default for Bump<W> {
    fn default() -> Self {
        Self::new()
    }
}

/* ---- Writing values ------------------------------------------------------ */

// Q: why is this needed?
// A: if T has too high alignment, then we can't guarantee that base+ptr stays aligned
//    after a realloc (or if the pointer is used with the wrong Bump).
// this is why *reads* must ensure T has low enough alignment. writes don't need to care,
// as the pointer is aligned just before the write.
fn assert_type_alignment<T: ?Sized + Aligned>() {
    const { assert!(T::ALIGN <= MAX_ALIGN) }
}

impl<W> Bump<W> {

    pub fn align(&mut self, align: usize) {
        // note: don't need to grow here even if len goes out of bounds,
        // since all writes check for grow anyway.
        self.len = (self.len + align as u32 - 1) & !(align as u32 - 1);
    }

    #[cold]
    fn grow_cap(&mut self, need: u32) {
        let mut cap = self.cap;
        if cap == 0 { cap = 64; }
        while cap < need { cap *= 2 }
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
        let ptr = NonNull::new(ptr).unwrap();
        unsafe {
            core::ptr::write_bytes(ptr.as_ptr().add(self.cap as _), 0, (cap - self.cap) as _);
        }
        self.ptr = ptr;
        self.cap = cap;
    }

    #[cold]
    fn grow(&mut self) {
        self.grow_cap(self.len)
    }

}

impl<W: Aligned> Bump<W> {

    fn reserve_aligned<T>(&mut self, num_bytes: u32) -> u32
        where T: ?Sized + Aligned
    {
        assert_type_alignment::<T>();
        if T::ALIGN > W::ALIGN {
            self.align(T::ALIGN);
        }
        let ofs = self.len;
        self.len += num_bytes;
        if T::ALIGN < W::ALIGN {
            self.align(W::ALIGN);
        }
        if self.len > self.cap {
            self.grow();
        }
        ofs
    }

    pub fn reserve<T>(&mut self) -> (BumpRef<T>, &mut T)
        where T: FromBytes + IntoBytes
    {
        let ptr = self.reserve_aligned::<T>(size_of::<T>() as _);
        let r = unsafe { &mut *self.ptr.as_ptr().add(ptr as _).cast() };
        (BumpRef(ptr / T::ALIGN as u32, PhantomData), r)
    }

    pub fn push<T>(&mut self, value: T) -> BumpRef<T>
        where T: FromBytes + IntoBytes
    {
        let (ptr, r) = self.reserve();
        *r = value;
        ptr
    }

    pub fn reserve_dst<T>(&mut self, len: usize) -> (BumpRef<T>, &mut T)
        where T: ?Sized + Aligned + PackedSliceDst,
              T::Head: FromBytes + IntoBytes,
              T::Item: FromBytes + IntoBytes
    {
        let ptr = self.reserve_aligned::<T>(size_of_dst::<T>(len) as u32);
        let addr = unsafe { self.ptr.as_ptr().add(ptr as _) as *const T::Head };
        let r = T::ptr_from_raw_parts(addr, len) as *mut T;
        let r = unsafe { &mut *r };
        (BumpRef(ptr / T::ALIGN as u32, PhantomData), r)
    }

    pub fn reserve_slice_init<T>(&mut self, len: usize, init: T) -> (BumpRef<[T]>, &mut [T])
        where T: Clone + Copy
    {
        let ptr = self.reserve_aligned::<T>((len*size_of::<T>()) as u32);
        let uninit: &mut [MaybeUninit<T>] = unsafe {
            core::slice::from_raw_parts_mut(
                self.ptr.as_ptr().add(ptr as _) as _,
                len
            )
        };
        uninit.fill(MaybeUninit::new(init));
        // XXX: replace this with MaybeUninit::slice_assume_init_mut when it stabilizes
        let r = unsafe { core::slice::from_raw_parts_mut( uninit.as_mut_ptr() as _, len) };
        (BumpRef(ptr / T::ALIGN as u32, PhantomData), r)
    }

    pub fn write<T>(&mut self, value: &T) -> BumpRef<T>
        where T: ?Sized + Aligned + IntoBytes
    {
        let ptr = self.reserve_aligned::<T>(size_of_val(value) as _);
        unsafe {
            core::ptr::copy_nonoverlapping(
                value as *const T as *const u8,
                self.ptr.as_ptr().add(ptr as _),
                size_of_val(value)
            );
        }
        BumpRef(ptr/T::ALIGN as u32, PhantomData)
    }

    pub fn write_range<T>(&mut self, range: Range<BumpRef<T>>) -> BumpRef<T>
        where T: FromBytes + IntoBytes
    {
        let Range { start, end } = range;
        let len = end.index() - start.index();
        let (ptr, data) = self.reserve_dst::<[T]>(len);
        let data = data as *mut [T] as *mut T;
        unsafe {
            let src = self.ptr.as_ptr().cast::<T>().add(start.index());
            core::ptr::copy_nonoverlapping(src, data, len);
        }
        ptr.cast()
    }

    pub fn extend<I>(&mut self, iter: I) -> BumpRef<I::Item>
        where I: IntoIterator,
              I::Item: Aligned + IntoBytes
    {
        if I::Item::ALIGN > W::ALIGN {
            self.align(I::Item::ALIGN);
        }
        let iter = iter.into_iter();
        let (hint, _) = iter.size_hint();
        if self.len + hint as u32 > self.cap {
            self.grow_cap(self.len + hint as u32);
        }
        let ofs = self.len;
        let mut len = ofs;
        for item in iter {
            let p = len;
            len += size_of::<I::Item>() as u32;
            if len > self.cap {
                self.grow_cap(len);
            }
            unsafe {
                *self.ptr.as_ptr().add(p as _).cast() = item;
            }
        }
        self.len = len;
        if I::Item::ALIGN < W::ALIGN {
            self.align(W::ALIGN);
        }
        BumpRef(ofs / I::Item::ALIGN as u32, PhantomData)
    }

    pub fn end(&self) -> BumpRef<W> {
        BumpRef(self.len / W::ALIGN as u32, PhantomData)
    }

    pub fn pop<T>(&mut self) -> Option<T>
        where T: FromBytes
    {
        if self.len < size_of::<T>() as u32 {
            None
        } else {
            self.len -= size_of::<T>() as u32;
            if T::ALIGN > W::ALIGN {
                self.len &= !(T::ALIGN as u32 - 1);
            }
            let value = unsafe { self.ptr.as_ptr().add(self.len as _).cast::<T>().read() };
            if T::ALIGN < W::ALIGN {
                self.len &= !(W::ALIGN as u32 - 1);
            }
            Some(value)
        }
    }

}

// these functions require bump to be unaligned because they may lower alignment
impl Bump {

    pub fn align_for<T>(&mut self) -> &mut Bump<T> {
        self.align(align_of::<T>() as _);
        unsafe { core::mem::transmute(self) }
    }

    pub fn truncate<T: ?Sized + Aligned>(&mut self, end: BumpRef<T>) {
        let len = end.ptr() as u32;
        assert!(len <= self.len);
        self.len = len;
    }

    pub fn clear(&mut self) {
        self.len = 0;
    }

    pub fn null_terminate(&mut self) {
        if self.as_slice().last() != Some(&0) {
            self.push(0u8);
        }
    }

}

impl<W: Aligned> core::fmt::Write for Bump<W> {

    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.write(s);
        Ok(())
    }

}

/* ---- Reading values ------------------------------------------------------ */

pub trait Get {
    fn get(bump: &BumpPtr, ptr: BumpRef<Self>) -> &Self;
}

pub trait GetMut {
    fn get_mut(bump: &mut BumpPtr, ptr: BumpRef<Self>) -> &mut Self;
}

impl<T> Get for T
    where T: FromBytes + Immutable
{
    fn get(BumpPtr(buf): &BumpPtr, ptr: BumpRef<Self>) -> &Self {
        let ofs = ptr.ptr();
        assert!(ofs + size_of::<T>() <= buf.len());
        unsafe { &*buf.as_ptr().add(ofs).cast() }
    }
}

impl<T> GetMut for T
    where T: FromBytes + IntoBytes
{
    fn get_mut(BumpPtr(buf): &mut BumpPtr, ptr: BumpRef<Self>) -> &mut Self {
        let ofs = ptr.ptr();
        assert!(ofs + size_of::<T>() <= buf.len());
        unsafe { &mut *buf.as_mut_ptr().add(ofs).cast() }
    }
}

unsafe fn transmute_slice<T>(mem: &[u8]) -> &[T] {
    unsafe { core::slice::from_raw_parts(mem.as_ptr().cast(), mem.len() / size_of::<T>()) }
}

unsafe fn transmute_slice_mut<T>(mem: &mut [u8]) -> &mut [T] {
    unsafe { core::slice::from_raw_parts_mut(mem.as_mut_ptr().cast(), mem.len() / size_of::<T>()) }
}

impl BumpPtr {

    pub fn get<T>(&self, ptr: BumpRef<T>) -> &T
        where T: ?Sized + Get
    {
        T::get(self, ptr)
    }

    pub fn get_mut<T>(&mut self, ptr: BumpRef<T>) -> &mut T
        where T: ?Sized + GetMut
    {
        T::get_mut(self, ptr)
    }

    pub fn get_dst<T>(&self, ptr: BumpRef<T>, num: usize) -> &T
        where T: ?Sized + Aligned + PackedSliceDst,
              T::Head: FromBytes + Immutable,
              T::Item: FromBytes + Immutable
    {
        let ofs = ptr.ptr();
        let buf = &self.0;
        assert!(ofs + size_of_dst::<T>(num) <= buf.len());
        let ptr = T::ptr_from_raw_parts(unsafe { buf.as_ptr().add(ofs).cast() }, num);
        unsafe { &*ptr }
    }

    pub fn get_dst_mut<T>(&mut self, ptr: BumpRef<T>, num: usize) -> &mut T
        where T: ?Sized + Aligned + PackedSliceDst,
              T::Head: FromBytes + IntoBytes,
              T::Item: FromBytes + IntoBytes
    {
        let ofs = ptr.ptr();
        let buf = &mut self.0;
        assert!(ofs + size_of_dst::<T>(num) <= buf.len());
        let ptr = T::ptr_from_raw_parts(unsafe { buf.as_mut_ptr().add(ofs) as _ }, num) as *mut _;
        unsafe { &mut *ptr }
    }

    pub fn as_slice<T>(&self) -> &[T]
        where T: FromBytes + Immutable
    {
        assert_type_alignment::<T>();
        unsafe { transmute_slice(&self.0) }
    }

    pub fn as_mut_slice<T>(&mut self) -> &mut [T]
        where T: FromBytes + IntoBytes
    {
        assert_type_alignment::<T>();
        unsafe { transmute_slice_mut(&mut self.0) }
    }

    // safety: alignment
    unsafe fn from_slice_unchecked(mem: &[u8]) -> &Self {
        debug_assert!(mem.as_ptr() as usize % MAX_ALIGN == 0);
        unsafe { core::mem::transmute(mem) }
    }

    // safety: alignment
    unsafe fn from_mut_slice_unchecked(mem: &mut [u8]) -> &mut Self {
        debug_assert!(mem.as_ptr() as usize % MAX_ALIGN == 0);
        unsafe { core::mem::transmute(mem) }
    }

}

/* ---- Get-many-mut operation ---------------------------------------------- */

pub struct GetManyMut<'a, const K: usize> {
    reserved: [Range<u32>; K],
    idx: usize,
    buf: *mut [u8],
    _marker: PhantomData<&'a mut ()>
}

impl<'a, const K: usize> GetManyMut<'a, K> {

    fn reserve_range(&mut self, range: Range<u32>) {
        let idx = self.idx;
        assert!(idx < K);
        assert!((range.end as usize) <= self.buf.len());
        for &Range { start, end } in &self.reserved[..idx] {
            assert!(range.end <= start || range.start >= end);
        }
        self.reserved[self.idx] = range;
        self.idx += 1;
    }

    pub fn get_mut<T>(&mut self, ptr: BumpRef<T>) -> &'a mut T
        where T: FromBytes + IntoBytes
    {
        let ofs = ptr.ptr();
        self.reserve_range(ofs as u32 .. (ofs + size_of::<T>()) as u32);
        unsafe { &mut *(self.buf as *mut u8).add(ofs).cast() }
    }

    pub fn get_dst_mut<T>(&mut self, ptr: BumpRef<T>, num: usize) -> &'a mut T
        where T: ?Sized + Aligned + PackedSliceDst,
              T::Head: FromBytes + IntoBytes,
              T::Item: FromBytes + IntoBytes
    {
        let ofs = ptr.ptr();
        self.reserve_range(ofs as u32 .. (ofs + size_of_dst::<T>(num)) as u32);
        let ptr = T::ptr_from_raw_parts(unsafe { (self.buf as *mut u8).add(ofs) as _ }, num) as *mut _;
        unsafe { &mut *ptr }
    }

}

impl BumpPtr {

    pub fn get_many_mut<const K: usize>(&mut self) -> GetManyMut<'_, K> {
        GetManyMut {
            reserved: [const { Range { start: 0, end: 0 }}; K],
            idx: 0,
            buf: &mut self.0 as _,
            _marker: PhantomData
        }
    }

}

/* ---- Operators ----------------------------------------------------------- */

impl<T> core::ops::Index<BumpRef<T>> for BumpPtr
    where T: ?Sized + Get
{
    type Output = T;
    fn index(&self, index: BumpRef<T>) -> &T {
        self.get(index)
    }
}

impl<T> core::ops::IndexMut<BumpRef<T>> for BumpPtr
    where T: ?Sized + Get + GetMut
{
    fn index_mut(&mut self, index: BumpRef<T>) -> &mut T {
        self.get_mut(index)
    }
}

impl<T> core::ops::Index<Range<BumpRef<T>>> for BumpPtr
    where T: FromBytes + Immutable
{
    type Output = [T];
    fn index(&self, index: Range<BumpRef<T>>) -> &[T] {
        assert_type_alignment::<T>();
        let mem: &[u8] = &self.as_slice()[index.start.ptr()..index.end.ptr()];
        unsafe { transmute_slice(mem) }
    }
}

impl<T> core::ops::IndexMut<Range<BumpRef<T>>> for BumpPtr
    where T: FromBytes + IntoBytes + Immutable
{
    fn index_mut(&mut self, index: Range<BumpRef<T>>) -> &mut [T] {
        assert_type_alignment::<T>();
        let mem: &mut [u8] = &mut self.as_mut_slice()[index.start.ptr()..index.end.ptr()];
        unsafe { transmute_slice_mut(mem) }
    }
}

impl<T> core::ops::Index<RangeFrom<BumpRef<T>>> for BumpPtr
    where T: FromBytes + Immutable
{
    type Output = [T];
    fn index(&self, index: RangeFrom<BumpRef<T>>) -> &[T] {
        assert_type_alignment::<T>();
        let mem: &[u8] = &self.as_slice()[index.start.ptr()..];
        unsafe { transmute_slice(mem) }
    }
}

impl<T> core::ops::IndexMut<RangeFrom<BumpRef<T>>> for BumpPtr
    where T: FromBytes + IntoBytes + Immutable
{
    fn index_mut(&mut self, index: RangeFrom<BumpRef<T>>) -> &mut [T] {
        assert_type_alignment::<T>();
        let mem: &mut [u8] = &mut self.as_mut_slice()[index.start.ptr()..];
        unsafe { transmute_slice_mut(mem) }
    }
}

impl<W> core::ops::Deref for Bump<W> {
    type Target = BumpPtr;
    fn deref(&self) -> &BumpPtr {
        unsafe {
            BumpPtr::from_slice_unchecked(
                core::slice::from_raw_parts(self.ptr.as_ptr(), self.len as _)
            )
        }
    }
}

impl<W> core::ops::DerefMut for Bump<W> {
    fn deref_mut(&mut self) -> &mut BumpPtr {
        unsafe {
            BumpPtr::from_mut_slice_unchecked(
                core::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len as _)
            )
        }
    }
}

impl<W> Drop for Bump<W> {
    fn drop(&mut self) {
        if self.cap != 0 {
            unsafe {
                alloc::alloc::dealloc(
                    self.ptr.as_ptr(),
                    Layout::from_size_align_unchecked(self.cap as _, MAX_ALIGN)
                );
            }
        }
    }
}

/* ---- VLAs ---------------------------------------------------------------- */

macro_rules! vla_struct {
    (
        // this allows also non-vla structs to simplify some macros that use this macro.
        $(#[$meta:meta])*
        $vis:vis struct $name:ident {
            $($fvis:vis $field:ident : $type:ty),* $(,)?
        }
    ) => {
        #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
        $(#[$meta])*
        $vis struct $name<Tail: ?Sized=[$tailtype]> {
            $($fvis $field : $type,)*
        }
    };
    (
        $(#[$meta:meta])*
        $vis:vis struct $name:ident {
            $($fvis:vis $field:ident : $type:ty),* $(,)?
        } $tvis:vis $tail:ident : [$tailtype:ty; |$lenx:ident| $len:expr]
    ) => {

        $(#[$meta])*
        #[repr(C)]
        $vis struct $name<Tail: ?Sized=[$tailtype]> {
            $($fvis $field : $type,)*
            $tvis $tail: Tail
        }

        impl $name {
            fn __bump_vla_len(bump: &$crate::bump::BumpPtr, ptr: $crate::bump::BumpRef<Self>) -> usize {
                // the purpose of Head and Head1 here is only to make sure they pass zerocopy's
                // analysis. both are needed to ensure the dst cannot have padding for any
                // slice length.
                #[allow(dead_code)]
                #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
                $(#[$meta])*
                #[repr(C)]
                struct Head { $($field:$type,)* $tail: [$tailtype; 0] }
                #[allow(dead_code)]
                #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
                $(#[$meta])*
                #[repr(C)]
                struct Head1 { $($field:$type,)* $tail: [$tailtype; 1] }
                let $lenx = &bump[ptr.cast::<Head>()];
                $len
            }
        }

        unsafe impl $crate::bump::FromBytes for $name<[$tailtype]> {}
        unsafe impl $crate::bump::IntoBytes for $name<[$tailtype]> {}
        unsafe impl $crate::bump::Immutable for $name<[$tailtype]> {}
        unsafe impl<const K: usize> $crate::bump::FromBytes for $name<[$tailtype; K]> {}
        unsafe impl<const K: usize> $crate::bump::IntoBytes for $name<[$tailtype; K]> {}
        unsafe impl<const K: usize> $crate::bump::Immutable for $name<[$tailtype; K]> {}

        unsafe impl $crate::bump::PackedSliceDst for $name {
            type Head = $name<[$tailtype; 0]>;
            type Item = $tailtype;
            fn ptr_from_raw_parts(addr: *const Self::Head, len: usize) -> *const Self {
                core::ptr::slice_from_raw_parts(addr, len) as _
            }
        }

        unsafe impl $crate::bump::Aligned for $name {
            const ALIGN: usize = align_of::<$name<[$tailtype; 0]>>();
        }

        impl $crate::bump::Get for $name {
            fn get(bump: &$crate::bump::BumpPtr, ptr: $crate::bump::BumpRef<Self>) -> &Self {
                bump.get_dst(ptr, $name::__bump_vla_len(bump, ptr))
            }
        }

        impl $crate::bump::GetMut for $name {
            fn get_mut(bump: &mut $crate::bump::BumpPtr, ptr: $crate::bump::BumpRef<Self>) -> &mut Self {
                bump.get_dst_mut(ptr, $name::__bump_vla_len(bump, ptr))
            }
        }

    };
}

pub(crate) use vla_struct;

/* ---- Containers ---------------------------------------------------------- */

// note: the `*Raw` structs are a hack to work around the lack of generic support in zerocopy.

#[derive(Clone, Copy, Default, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct BumpSliceRaw {
    data: u32, // BumpRef<T>
    len: u32
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct BumpSlice<T> {
    raw: BumpSliceRaw,
    _marker: PhantomData<T>
}

impl<T> Clone for BumpSlice<T> {
    fn clone(&self) -> Self {
        BumpSlice { raw: self.raw, _marker: PhantomData }
    }
}

impl<T> Copy for BumpSlice<T> {}

#[derive(Default, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct BumpVecRaw {
    data: BumpSliceRaw,
    cap: u32
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct BumpVec<T> {
    raw: BumpVecRaw,
    _marker: PhantomData<T>
}

impl<T> BumpSlice<T> {

    pub fn len(self) -> u32 {
        self.raw.len
    }

    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    pub fn base(self) -> BumpRef<T> {
        zerocopy::transmute!(self.raw.data)
    }

    pub fn as_slice(self, bump: &BumpPtr) -> &[T]
        where T: FromBytes + Immutable
    {
        bump.get_dst(self.base().cast(), self.len() as _)
    }

    pub fn as_mut_slice(self, bump: &mut BumpPtr) -> &mut [T]
        where T: FromBytes + IntoBytes + Immutable
    {
        bump.get_dst_mut(self.base().cast(), self.len() as _)
    }

}

impl<T> Default for BumpSlice<T> {
    fn default() -> Self {
        Self { raw: Default::default(), _marker: PhantomData }
    }
}

impl<T> BumpVec<T> {

    #[cold]
    fn grow<W>(&mut self, bump: &mut Bump<W>, need: u32)
        where T: FromBytes + IntoBytes + Immutable
    {
        let mut cap = max(self.raw.cap, 8);
        while cap < need {
            cap *= 2;
        }
        let (newdata, _) = bump.reserve_dst::<[T]>(cap as _);
        let have = self.len();
        if have > 0 {
            let (old, new) = bump.as_mut_slice::<u8>().split_at_mut(newdata.ptr());
            let base = self.base().ptr();
            let havebytes = have as usize * size_of::<T>();
            new[..havebytes].copy_from_slice(&old[base..base+havebytes]);
        }
        self.raw.data.data = zerocopy::transmute!(newdata);
        self.raw.cap = cap;
    }

    // pub fn reserve<'bump,W>(&mut self, bump: &'bump mut Bump<W>, num: usize) -> &'bump mut [T]
    //     where T: FromBytes + IntoBytes + Immutable
    // {
    //     let idx = self.len();
    //     if idx + num as u32 > self.raw.cap {
    //         self.grow(bump, idx + num as u32);
    //     }
    //     self.raw.data.len = idx + num as u32;
    //     let base = self.base().add_size(idx as _);
    //     &mut bump[base..base.add_size(num as _)]
    // }

    pub fn push<W>(&mut self, bump: &mut Bump<W>, value: T)
        where T: FromBytes + IntoBytes + Immutable
    {
        let idx = self.raw.data.len;
        if idx >= self.raw.cap {
            self.grow(bump, idx + 1);
        }
        self.raw.data.len = idx+1;
        bump[self.base().offset(idx as _)] = value;
    }

    pub fn truncate(&mut self, len: u32) {
        self.raw.data.len = len;
    }

}

impl<T> Default for BumpVec<T> {
    fn default() -> Self {
        Self { raw: Default::default(), _marker: PhantomData }
    }
}

// do not implement DerefMut!
// there's nothing useful you can do with a &mut BumpArray,
// but you can misuse it by eg. swapping the data arrays of two bumpvecs
impl<T> Deref for BumpVec<T> {
    type Target = BumpSlice<T>;
    fn deref(&self) -> &BumpSlice<T> {
        zerocopy::transmute_ref!(&self.raw.data)
    }
}

// note: you may *NOT* assume that the bytes here are actually aligned.
// this is just a convenience wrapper to make the write functions align the written value.
// you *may* assume that the written value is aligned to the higher alignment.
#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct AlignedBytes<const ALIGN: usize>([u8]);

unsafe impl<const ALIGN: usize> Aligned for AlignedBytes<ALIGN> {
    const ALIGN: usize = ALIGN;
}

impl<const ALIGN: usize> AlignedBytes<ALIGN> {

    pub fn new(bytes: &[u8]) -> &Self {
        unsafe { core::mem::transmute(bytes) }
    }

}
