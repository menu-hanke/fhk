//! Intern table.

use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::Range;

use hashbrown::hash_table::Entry;
use hashbrown::HashTable;

use crate::bump::{self, Aligned, Bump, BumpRef, PackedSliceDst};
use crate::hash::fxhash;

/*
 * +-------+------+
 * | 31..4 | 3..0 |
 * +-------+------+
 * |  end  | size |
 * +-------+------+
 *
 * size 1..8 -> smallref of `size`
 *      9..0 -> bigref of `-size`
 */
#[derive(Clone, Copy, PartialEq, Eq, Hash,
    zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct RawRef(u32);

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct IRef<T: ?Sized>(RawRef, PhantomData<T>);

pub struct Intern {
    bump: Bump<u8>,
    tab: HashTable<RawRef>,
    base: BumpRef<u8>
}

impl RawRef {

    const SIZE_BITS: usize = 4;
    const MAX_SMALL: u32 = 8;
    const EMPTY: Self = Self(0);

    const fn pack(end: u32, size: u32) -> Self {
        Self((end << Self::SIZE_BITS) | size)
    }

    fn end(self) -> u32 {
        self.0 >> Self::SIZE_BITS
    }

    fn raw_size(self) -> u32 {
        self.0 & 0xf
    }

}

impl<T: ?Sized> Clone for IRef<T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<T: ?Sized> Copy for IRef<T> {}

impl<T: ?Sized> PartialEq for IRef<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: ?Sized> Eq for IRef<T> {}

impl<T: ?Sized> Hash for IRef<T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<T: ?Sized> IRef<T> {

    pub const EMPTY: Self = Self(RawRef::EMPTY, PhantomData);

    pub fn cast<U: ?Sized>(self) -> IRef<U> {
        zerocopy::transmute!(self)
    }

}

impl<T: ?Sized + Aligned> IRef<T> {

    pub fn to_bump_sized(self, size: usize) -> BumpRef<T> {
        BumpRef::from_offset(self.0.end() as usize - size)
    }

    // pub fn to_bump_small_unchecked(self) -> BumpRef<T> {
    //     debug_assert!((refsize(self.0) as i32) >= 0);
    //     self.to_bump_sized(refsize(self.0) as usize + 1)
    // }

}

impl<T: Aligned> IRef<T> {

    pub fn to_bump(self) -> BumpRef<T> {
        self.to_bump_sized(size_of::<T>())
    }

}

impl<T: ?Sized> IRef<T> {

    // public for hardcoding constant references (eg. Ccx::SEQ_GLOBAL).
    // extremely easy to misuse.
    pub const fn small_from_end_size(end: u32, size: u32) -> Self {
        Self(RawRef::pack(end, size), PhantomData)
    }

    // const fn big(ptr: u32, size: u32) -> Self {
    //     Self(bigref(ptr, size), PhantomData)
    // }

}

unsafe fn bigsize(mut end: *const u8, mut raw_size: usize) -> usize {
    let mut shift = 0;
    let mut size = 0;
    loop {
        size |= (*end as usize) << shift;
        raw_size += 1;
        if raw_size == 0x10 { return size }
        end = end.add(1);
        shift += 8;
    }
}

unsafe fn bigbytes<'a>(data: *const u8, end: usize, raw_size: usize) -> &'a [u8] {
    let end = data.add(end);
    let size = bigsize(end, raw_size);
    core::slice::from_raw_parts(end.sub(size), size)
}

unsafe fn bytesmatch(data: *const u8, r: RawRef, bytes: &[u8]) -> bool {
    let raw_size = r.raw_size() as usize;
    let end = r.end() as usize;
    if bytes.len() <= RawRef::MAX_SMALL as _ {
        // if `r` is big then the first comparison is always false
        raw_size == bytes.len()
            && bytes == core::slice::from_raw_parts(data.add(end-raw_size), raw_size)
    } else {
        raw_size > RawRef::MAX_SMALL as _ && bytes == bigbytes(data, end, raw_size)
    }
}

unsafe fn refdata<'a>(data: *const u8, r: RawRef) -> &'a [u8] {
    let raw_size = r.raw_size() as usize;
    let end = r.end() as usize;
    let ep = data.add(end);
    let size = if raw_size <= RawRef::MAX_SMALL as _ {
        raw_size
    } else {
        bigsize(ep, raw_size)
    };
    core::slice::from_raw_parts(ep.sub(size), size)
}

// safety: tab and bump must come from the same intern table
unsafe fn entry<'tab, 'short>(
    tab: &'tab mut HashTable<RawRef>,
    bump: &'short [u8],
    bytes: &'short [u8],
    align: u32
) -> Entry<'tab, RawRef> {
    tab.entry(
        fxhash(bytes),
        // note: this tests that the *end* is aligned, which works as long as size is a multiple
        // of alignment.
        |&r| r.end() & (align - 1) == 0 && bytesmatch(bump.as_ptr(), r, bytes),
        |&r| fxhash(refdata(bump.as_ptr(), r))
    )
}

fn writebigsize(data: &mut Bump<u8>, mut len: usize) -> u32 {
    let mut bytes = 0;
    loop {
        data.push(len as u8);
        len >>= 8;
        bytes += 1;
        if len == 0 { return bytes }
    }
}

fn newref(bump: &mut Bump<u8>, len: usize) -> RawRef {
    let end = bump.end().offset() as _;
    let size = if len <= RawRef::MAX_SMALL as _ {
        len as _
    } else {
        0x10 - writebigsize(bump, len)
    };
    RawRef::pack(end, size)
}

fn internbytes(intern: &mut Intern, bytes: &[u8], align: u32) -> RawRef {
    match unsafe { entry(&mut intern.tab, intern.bump.as_slice(), bytes, align) } {
        Entry::Occupied(e) => *e.get(),
        Entry::Vacant(e) => {
            intern.bump.align(align as _);
            intern.bump.write(bytes);
            intern.base = intern.bump.end();
            *e.insert(newref(&mut intern.bump, bytes.len())).get()
        }
    }
}

fn reflen(data: &[u8], end: usize, raw_size: usize) -> usize {
    if raw_size <= RawRef::MAX_SMALL as _ {
        raw_size
    } else {
        assert!(end + (0x10 - raw_size) <= data.len());
        unsafe { bigsize(data.as_ptr().add(end), raw_size) }
    }
}

fn refrange(data: &[u8], r: RawRef) -> Range<usize> {
    let end = r.end() as usize;
    end - reflen(data, end, r.raw_size() as _) .. end
}

impl Intern {

    pub fn intern<T>(&mut self, value: &T) -> IRef<T>
        where T: ?Sized + Aligned + bump::IntoBytes
    {
        let bytes = unsafe {
            core::slice::from_raw_parts(
                value as *const T as *const u8,
                size_of_val(value)
            )
        };
        IRef(internbytes(self, bytes, T::ALIGN as _), PhantomData)
    }

    pub fn intern_collect<T>(&mut self, values: impl IntoIterator<Item=T>) -> IRef<[T]>
        where T: Aligned + bump::FromBytes + bump::IntoBytes
    {
        let base = self.bump.extend(values).cast();
        self.intern_consume_from(base).cast()
    }

    pub fn intern_range(&mut self, range: Range<usize>) -> IRef<[u8]> {
        todo!()
    }

    pub fn find<T>(&self, value: &T) -> Option<IRef<T>>
        where T: ?Sized + bump::IntoBytes
    {
        todo!()
    }

    pub fn get_range(&self, r: IRef<[u8]>) -> Range<usize> {
        refrange(self.bump.as_slice(), r.0)
    }

    pub fn get<T>(&self, r: IRef<T>) -> &T
        where T: ?Sized + Aligned + bump::Get
    {
        &self.bump[BumpRef::from_offset(refrange(self.bump.as_slice(), r.0).start)]
    }

    pub fn get_slice<T>(&self, r: IRef<[T]>) -> &[T]
        where T: bump::FromBytes + bump::Immutable
    {
        let Range { start, end } = refrange(self.bump.as_slice(), r.0);
        &self.bump[BumpRef::from_offset(start)..BumpRef::from_offset(end)]
    }

    pub fn bump(&self) -> &Bump {
        &self.bump
    }

    // pub fn ref_to_bump<T>(&self, r: IRef<T>) -> BumpRef<T>
    //     where T: ?Sized + Aligned
    // {
    //     r.to_bump_sized(reflen(self.bump.as_slice(), r.0))
    // }

    pub fn write<T>(&mut self, value: &T)
        where T: ?Sized + Aligned + bump::IntoBytes
    {
        self.bump.write(value);
    }

    // type doesn't matter here, so take a concrete type for better type inference and less
    // monomorphization
    pub fn write_ref(&mut self, r: IRef<[u8]>) {
        let Range { start, end } = self.get_range(r);
        self.bump.write_range::<u8>(BumpRef::from_offset(start)..BumpRef::from_offset(end));
    }

    pub fn reserve_dst<T>(&mut self, len: usize) -> &mut T
        where T: ?Sized + Aligned + PackedSliceDst,
              T::Head: bump::FromBytes + bump::IntoBytes,
              T::Item: bump::FromBytes + bump::IntoBytes
    {
        self.bump.reserve_dst(len).1
    }

    pub fn intern_consume_from(&mut self, cursor: BumpRef<u8>) -> IRef<[u8]> {
        match unsafe { entry(&mut self.tab, self.bump.as_slice(), &self.bump[cursor..], 1) } {
            Entry::Occupied(e) => {
                // this assert is needed for correctness because any ref in the hashtable
                // is assumed to be valid and can therefore skip bound checks.
                // ie. it's not ok in any situation to remove data that is referenced
                // from the hashtable.
                assert!(cursor >= self.base);
                self.bump.truncate(cursor);
                IRef(*e.get(), PhantomData)
            },
            Entry::Vacant(e) => {
                let len = self.bump.end().offset() - cursor.offset();
                let r = newref(&mut self.bump, len);
                self.base = cursor;
                IRef(*e.insert(r).get(), PhantomData)
            }
        }
    }

}

impl Default for Intern {
    fn default() -> Self {
        let mut tab = HashTable::new();
        tab.insert_unique(fxhash(&[0; 0]), RawRef::EMPTY, |_| unreachable!());
        Self { tab, bump: Default::default(), base: BumpRef::zero() }
    }
}

impl<T> core::ops::Index<IRef<T>> for Intern
    where T: ?Sized + Aligned + bump::Get
{
    type Output = T;
    fn index(&self, r: IRef<T>) -> &T {
        self.get(r)
    }
}

impl core::fmt::Write for Intern {

    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.bump.write_str(s)
    }

}

// the following COULD be implemented...
//     impl<T: ReadBytes> core::ops::Index<IRef<[T]>> for Intern { ... }
// BUT implementing it breaks type inference in...
//     let v: Type = intern[zerocopy::transmute!(handle)]
// so for now just use get_slice() for slices.
