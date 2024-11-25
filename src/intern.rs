//! Intern table.

use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::Range;

use hashbrown::hash_table::Entry;
use hashbrown::HashTable;

use crate::bump::{as_bytes, Aligned, Bump, BumpRef, Read, ReadBytes, Write, WriteBytes};
use crate::hash::fxhash;

const PTR_BITS: usize = 27;

/*
 * layout:
 *
 *   +------+--------+-------+
 *   |  31  | 30..28 | 27..0 |
 *   +======+========+=======+
 *   | mode |  size  |  end  |
 *   +------+--------+-------+
 *
 * where
 *
 *   +--------------+-----------------------------------+
 *   |     mode     | string length                     |
 *   +==============+===================================+
 *   | 0 (smallref) | 1+size                            |
 *   +--------------+-----------------------------------+
 *   | 1 (bigref)   | length is stored as `size` bytes  |
 *   |              | right after `end` (unaligned)     |
 *   +--------------+-----------------------------------+
 */
#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct InternRef<T: ?Sized>(u32, PhantomData<T>);

pub struct Intern {
    bump: Bump<u8>,
    tab: HashTable<InternRef<[u8]>>,
    base: BumpRef<u8>
}

impl<T: ?Sized> Clone for InternRef<T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<T: ?Sized> Copy for InternRef<T> {}

impl<T: ?Sized> PartialEq for InternRef<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: ?Sized> Eq for InternRef<T> {}

impl<T: ?Sized> Hash for InternRef<T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.0)
    }
}

impl<T: ?Sized> InternRef<T> {

    pub fn cast<U: ?Sized>(self) -> InternRef<U> {
        zerocopy::transmute!(self)
    }

}

impl<T: ?Sized + Aligned> InternRef<T> {

    pub fn to_bump_sized(self, size: usize) -> BumpRef<T> {
        BumpRef::from_offset(refend(self.0) as usize - size)
    }

    pub fn to_bump_small_unchecked(self) -> BumpRef<T> {
        debug_assert!((refsize(self.0) as i32) >= 0);
        self.to_bump_sized(refsize(self.0) as usize + 1)
    }

}

impl<T: Aligned> InternRef<T> {

    pub fn to_bump(self) -> BumpRef<T> {
        self.to_bump_sized(size_of::<T>())
    }

}

// note: you must pass size = seq len - 1
const fn smallref(ptr: u32, size: u32) -> u32 {
    ptr | (size << PTR_BITS)
}

const fn bigref(ptr: u32, size: u32) -> u32 {
    ptr | ((!size) << PTR_BITS)
}

impl<T: ?Sized> InternRef<T> {

    // public for hardcoding constant references (eg. Ccx::SEQ_GLOBAL).
    // extremely easy to misuse.
    pub const fn small(ptr: u32, size: u32) -> Self {
        Self(smallref(ptr, size), PhantomData)
    }

    const fn big(ptr: u32, size: u32) -> Self {
        Self(bigref(ptr, size), PhantomData)
    }

    pub const EMPTY: Self = Self::big(0, 0);

}

fn refend(r: u32) -> u32 {
    r & ((1 << PTR_BITS) - 1)
}

// big ref   => bitwise NOT of size of seq len
// small ref => seq len - 1
fn refsize(r: u32) -> u32 {
    ((r as i32) >> PTR_BITS) as _
}

// safety: ref must be in bounds
unsafe fn smallmatch(data: &[u8], r: u32, bytes: &[u8]) -> bool {
    let size = refsize(r) as usize;
    if size == bytes.len().wrapping_sub(1) {
        let end = refend(r) as usize;
        data.get_unchecked(end-(size+1)..end) == bytes
    } else {
        // either `r` is big, or `r` small with wrong size
        false
    }
}

unsafe fn bigreflen(data: &[u8], end: usize, size: usize) -> usize {
    let mut ptr = end + size;
    let mut len = 0;
    while ptr > end {
        len = (len << 8) | (*data.get_unchecked(ptr) as usize);
        ptr -= 1;
    }
    len
}

unsafe fn bigrefdata(data: &[u8], end: usize, size: usize) -> &[u8] {
    data.get_unchecked(end-bigreflen(data, end, size)..end)
}

// safety: ref must be in bounds
unsafe fn bigmatch(data: &[u8], r: u32, bytes: &[u8]) -> bool {
    let size = refsize(r);
    if (size as i32) < 0 {
        bigrefdata(data, refend(r) as _, (!size) as _) == bytes
    } else {
        // `r` is small
        false
    }
}

fn issmallbytes(len: usize) -> bool {
    len.wrapping_sub(1) < 8
}

unsafe fn bytesmatch(data: &[u8], r: u32, bytes: &[u8]) -> bool {
    if issmallbytes(bytes.len()) {
        smallmatch(data, r, bytes)
    } else {
        bigmatch(data, r, bytes)
    }
}

unsafe fn dyndata(r: u32, data: &[u8]) -> &[u8] {
    let size = refsize(r);
    let end = refend(r) as usize;
    if (size as i32) >= 0 {
        data.get_unchecked(end-(size as usize + 1)..end)
    } else {
        bigrefdata(data, end, (!size) as _)
    }
}

// safety: tab and bump must come from the same intern table
unsafe fn entry<'tab, 'short>(
    tab: &'tab mut HashTable<InternRef<[u8]>>,
    bump: &'short [u8],
    bytes: &'short [u8],
    align: u32
) -> Entry<'tab, InternRef<[u8]>> {
    tab.entry(
        fxhash(bytes),
        // note: this tests that the *end* is aligned, which works as long as size is a multiple
        // of alignment.
        |r| r.0 & (align - 1) == 0 && bytesmatch(bump, r.0, bytes),
        |r| fxhash(dyndata(r.0, bump))
    )
}

fn writebiglen(data: &mut Bump<u8>, mut len: usize) -> u32 {
    let mut bytes = 0;
    loop {
        data.push(&(len as u8));
        len >>= 8;
        bytes += 1;
        if len == 0 { return bytes }
    }
}

fn newref(bump: &mut Bump<u8>, len: usize) -> u32 {
    let end = bump.end().offset() as _;
    match issmallbytes(len) {
        true  => smallref(end, len as u32 - 1),
        false => bigref(end, writebiglen(bump, len))
    }
}

fn internbytes(intern: &mut Intern, bytes: &[u8], align: u32) -> InternRef<[u8]> {
    match unsafe { entry(&mut intern.tab, intern.bump.as_slice(), bytes, align) } {
        Entry::Occupied(e) => *e.get(),
        Entry::Vacant(e) => {
            intern.bump.align(align);
            intern.bump.push_slice(bytes);
            *e.insert(InternRef(newref(&mut intern.bump, bytes.len()), PhantomData)).get()
        }
    }
}

fn reflen(data: &[u8], r: u32) -> usize {
    let end = refend(r) as usize;
    let size = refsize(r);
    if (size as i32) >= 0 {
        size as usize + 1
    } else {
        let size = (!size) as usize;
        // STRICT inequality here, because data[end+size] is the last length byte.
        assert!(end+size < data.len());
        unsafe { bigreflen(data, end, size) }
    }
}

fn refrange(data: &[u8], r: u32) -> Range<usize> {
    let end = refend(r) as usize;
    end - reflen(data, r) .. end
}

impl Intern {

    pub fn intern<T: ?Sized + WriteBytes + Aligned>(&mut self, value: &T) -> InternRef<T> {
        internbytes(self, as_bytes(value), T::ALIGN as _).cast()
    }

    pub fn intern_range(&mut self, range: Range<usize>) -> InternRef<[u8]> {
        todo!()
    }

    pub fn find<T: ?Sized + WriteBytes>(&self, value: &T) -> Option<InternRef<T>> {
        todo!()
    }

    pub fn get_range(&self, r: InternRef<[u8]>) -> Range<usize> {
        refrange(self.bump.as_slice(), r.0)
    }

    pub fn get<T: ?Sized + Read + Aligned>(&self, r: InternRef<T>) -> &T {
        &self.bump[BumpRef::from_offset(refrange(self.bump.as_slice(), r.0).start)]
    }

    pub fn get_slice<T: ReadBytes>(&self, r: InternRef<[T]>) -> &[T] {
        let Range { start, end } = refrange(self.bump.as_slice(), r.0);
        &self.bump[BumpRef::from_offset(start)..BumpRef::from_offset(end)]
    }

    pub fn bump(&self) -> &Bump {
        &self.bump
    }

    pub fn ref_to_bump<T: ?Sized + Aligned>(&self, r: InternRef<T>) -> BumpRef<T> {
        r.to_bump_sized(reflen(self.bump.as_slice(), r.0))
    }

    pub fn push<T: ?Sized + Write + Aligned>(&mut self, value: &T) {
        self.bump.push(value);
    }

    // type doesn't matter here, so take a concrete type for better type inference and less
    // monomorphization
    pub fn push_ref(&mut self, r: InternRef<[u8]>) {
        self.bump.push_range(self.get_range(r));
    }

    pub fn intern_consume_from(&mut self, cursor: BumpRef<u8>) -> InternRef<[u8]> {
        match unsafe { entry(&mut self.tab, self.bump.as_slice(), &self.bump[cursor..], 1) } {
            Entry::Occupied(e) => {
                // this assert is needed for correctness because any ref in the hashtable
                // is assumed to be valid and can therefore skip bound checks.
                // ie. it's not ok in any situation to remove data that is referenced
                // from the hashtable.
                assert!(cursor >= self.base);
                self.bump.truncate(cursor);
                *e.get()
            },
            Entry::Vacant(e) => {
                let len = self.bump.end().offset() - cursor.offset();
                let r = newref(&mut self.bump, len);
                self.base = cursor;
                *e.insert(InternRef(r, PhantomData)).get()
            }
        }
    }

}

impl Default for Intern {
    fn default() -> Self {
        let mut tab = HashTable::new();
        tab.insert_unique(fxhash(&[0; 0]), InternRef::EMPTY, |_| unreachable!());
        Self { tab, bump: Default::default(), base: BumpRef::zero() }
    }
}

impl<T: ?Sized + Read + Aligned> core::ops::Index<InternRef<T>> for Intern {
    type Output = T;
    fn index(&self, r: InternRef<T>) -> &T {
        self.get(r)
    }
}

impl core::fmt::Write for Intern {

    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.bump.write_str(s)
    }

}

// the following COULD be implemented...
//     impl<T: ReadBytes> core::ops::Index<InternRef<[T]>> for Intern { ... }
// BUT implementing it breaks type inference in...
//     let v: Type = intern[zerocopy::transmute!(handle)]
// so for now just use get_slice() for slices.
