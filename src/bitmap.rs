//! Bit maps.

use core::cmp::max;
use core::fmt::{Debug, Write};
use core::iter::zip;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut, Range, RangeTo};
use core::slice;

use alloc::vec::Vec;

use crate::index::Index;

// this can be changed to experiment with smaller (or larger, ie u128) word sizes,
// but register size, ie u64, probably works best.
type Word = u64;

const WORD_BITS: usize = 8*size_of::<Word>();
const SHIFT: usize = WORD_BITS.ilog2() as _;
const MASK: usize = WORD_BITS - 1;

#[repr(transparent)]
pub struct Bitmap<I: Index = usize> {
    _marker: PhantomData<fn(&I)>,
    raw: [Word]
}

fn set(bitmap: &mut [Word], bit: usize) {
    bitmap[bit>>SHIFT] |= 1 << (bit&MASK);
}

fn set_range(bitmap: &mut [Word], start: usize, end: usize) {
    debug_assert!(WORD_BITS == 64); // this is not generic atm
    if start == end { return }
    let endw = (end-1) >> 6;
    let idx = start >> 6;
    if idx == endw {
        let mask = ((-1i64 as u64) << (start & 0x3f))
            & ((-1i64 as u64) >> (((-(end as isize)) & 0x3f) as usize));
        bitmap[idx] |= mask;
    } else {
        let mask = (-1i64 as u64) << (start & 0x3f);
        bitmap[idx] |= mask;
        for j in idx+1..endw {
            bitmap[j] = -1i64 as u64;
        }
        let mask = (-1i64 as u64) >> (((-(end as isize)) & 0x3f) as usize);
        bitmap[endw] |= mask;
    }
}

fn test(bitmap: &[Word], bit: usize) -> bool {
    bitmap[bit>>SHIFT] & (1 << (bit&MASK)) != 0
}

fn clear(bitmap: &mut [Word], bit: usize) {
    bitmap[bit>>SHIFT] &= !(1 << (bit&MASK));
}

fn test_and_set(bitmap: &mut [Word], bit: usize) -> bool {
    let idx = bit>>SHIFT;
    let mask = 1 << (bit&MASK);
    let test = bitmap[idx] & mask != 0;
    bitmap[idx] |= mask;
    test
}

fn intersect(bitmap: &mut [Word], other: &[Word]) {
    for (a, &b) in bitmap.iter_mut().zip(other.iter()) {
        *a &= b;
    }
}

fn union(bitmap: &mut [Word], other: &[Word]) {
    for (a, &b) in bitmap.iter_mut().zip(other.iter()) {
        *a |= b;
    }
}

fn is_subset(a: &[Word], b: &[Word]) -> bool {
    zip(a, b).all(|(&aw,&bw)| aw & bw == aw)
}

fn popcount(bitmap: &[Word]) -> u32 {
    bitmap.iter().map(|w| w.count_ones()).sum()
}

fn popcount_leading(bitmap: &[Word], end: usize) -> u32 {
    if end == 0 { return 0; }
    let idx = (end-1)>>SHIFT;
    popcount(&bitmap[..idx])
        + (bitmap[idx] & ((!0) >> ((-(end as isize) as usize)&MASK))).count_ones()
}

fn ffs(bitmap: &[Word]) -> Option<usize> {
    bitmap
        .iter()
        .enumerate()
        .find_map(|(i,&w)| match w {
            0 => None,
            w => Some(i*WORD_BITS + w.trailing_zeros() as usize)
        })
}

// nb. watch out for monomorphization. anything that takes a generic should delegate to a
// non-generic version.
impl<I: Index> Bitmap<I> {

    #[inline(always)] pub fn set(&mut self, idx: I) { set(&mut self.raw, idx.into()) }
    #[inline(always)] pub fn set_range(&mut self, idx: Range<I>) { set_range(&mut self.raw, idx.start.into(), idx.end.into()) }
    #[inline(always)] pub fn test(&self, idx: I) -> bool { test(&self.raw, idx.into()) }
    #[inline(always)] pub fn clear(&mut self, idx: I) { clear(&mut self.raw, idx.into()) }
    #[inline(always)] pub fn clear_all(&mut self) { self.raw.fill(0); }
    #[inline(always)] pub fn set_all(&mut self) { self.raw.fill(!0); }
    #[inline(always)] pub fn test_and_set(&mut self, idx: I) -> bool { test_and_set(&mut self.raw, idx.into()) }
    #[inline(always)] pub fn intersect(&mut self, other: &Bitmap<I>) { intersect(&mut self.raw, &other.raw) }
    #[inline(always)] pub fn is_subset(&self, other: &Bitmap<I>) -> bool { is_subset(&self.raw, &other.raw) }
    #[inline(always)] pub fn union(&mut self, other: &Bitmap<I>) { union(&mut self.raw, &other.raw) }
    #[inline(always)] pub fn popcount(&self) -> u32 { popcount(&self.raw) }
    #[inline(always)] pub fn popcount_leading(&self, end: I) -> u32 { popcount_leading(&self.raw, end.into()) }
    #[inline(always)] pub fn ffs(&self) -> Option<I> { ffs(&self.raw).map(Into::into) }

    pub fn copy_from(&mut self, other: &Bitmap<I>) {
        self.raw.copy_from_slice(&other.raw)
    }

    pub fn is_empty(&self) -> bool {
        self.raw.iter().all(|&w| w == 0)
    }

    #[inline(always)]
    pub fn end(&self) -> I {
        (self.raw.len()*WORD_BITS).into()
    }

    pub fn end_set(&self) -> I {
        todo!()
    }

    pub fn ones_in(&self, idx: Range<I>) -> core::iter::Map<BitmapIterOnes, fn(usize) -> I> {
        iter_ones(&self.raw, idx.start.into()..idx.end.into()).map(Into::into)
    }

    pub fn ones(&self) -> core::iter::Map<BitmapIterOnes, fn(usize) -> I> {
        iter_ones(&self.raw, 0..self.end().into()).map(Into::into)
    }

    pub fn cast<J: Index>(&self) -> &Bitmap<J> {
        // safety: this transmutes a repr(transparent) [Word] wrapper to another
        // repr(transparent) [Word] wrapper.
        unsafe { core::mem::transmute(self) }
    }

    pub fn cast_mut<J: Index>(&mut self) -> &mut Bitmap<J> {
        // safety: same as above
        unsafe { core::mem::transmute(self) }
    }

    fn from_raw(raw: &[Word]) -> &Self {
        // safety: see above
        unsafe { core::mem::transmute(raw) }
    }

    fn from_raw_mut(raw: &mut [Word]) -> &mut Self {
        // safety: see above
        unsafe { core::mem::transmute(raw) }
    }

}

// note: it doesn't really make sense to implement Index for other Range types (except for usize
// ranges), because that would offset the indices, which isn't really something you ever want to do
impl<I: Index> core::ops::Index<RangeTo<I>> for Bitmap<I> {
    type Output = Bitmap<I>;
    fn index(&self, index: RangeTo<I>) -> &Bitmap<I> {
        todo!()
    }
}

impl<I: Index> core::ops::IndexMut<RangeTo<I>> for Bitmap<I> {
    fn index_mut(&mut self, index: RangeTo<I>) -> &mut Bitmap<I> {
        todo!()
    }
}

pub struct BitmapIterOnes<'a> {
    _phantom: PhantomData<&'a [Word]>,
    bitmap: *const Word,
    cur: Word,
    end: usize,
    base: usize,
}

impl<'a> Iterator for BitmapIterOnes<'a> {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        while self.cur == 0 {
            self.base += WORD_BITS;
            if self.base >= self.end { return None; }
            self.cur = unsafe { *self.bitmap };
            self.bitmap = unsafe { self.bitmap.add(1) };
        }
        let bit = self.cur.trailing_zeros() as usize;
        self.cur &= !(1<<bit);
        let idx = self.base + bit;
        if idx < self.end {
            Some(idx)
        } else {
            None
        }
    }
}

fn iter_ones(bitmap: &[Word], range: Range<usize>) -> BitmapIterOnes {
    let Range { start, end } = range;
    let ofs = start>>SHIFT;
    BitmapIterOnes {
        _phantom: PhantomData,
        bitmap: unsafe { bitmap.as_ptr().add(1) },
        cur: bitmap.get(ofs).cloned().unwrap_or(0) & ((!0) << (start&MASK)),
        end,
        base: ofs<<SHIFT
    }
}

impl<'a, I: Index> IntoIterator for &'a Bitmap<I> {
    type IntoIter = core::iter::Map<BitmapIterOnes<'a>, fn(usize) -> I>;
    type Item = I;
    fn into_iter(self) -> Self::IntoIter { self.ones() }
}

impl<I: Index> Debug for Bitmap<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.ones().map(Into::into)).finish()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct BitmapArray<const W: usize, I: Index = usize> {
    _marker: PhantomData<fn(&I)>,
    raw: [Word; W]
}

pub type BitmapWord<I=usize> = BitmapArray<1, I>;

impl<const W: usize> BitmapArray<W> {
    pub const BITS: usize = W * WORD_BITS;
}

macro_rules! bitmap_array {
    ($index:ty; $bits:expr) => {
        $crate::bitmap::BitmapArray<
            { ($bits + $crate::bitmap::BitmapWord::BITS - 1) / $crate::bitmap::BitmapWord::BITS },
            $index
        >
    };
    ($bits:expr) => { $crate::bitmap::bitmap_array![usize; $bits] };
}

pub(crate) use bitmap_array;

impl<const W: usize, I: Index> Deref for BitmapArray<W, I> {
    type Target = Bitmap<I>;
    fn deref(&self) -> &Bitmap<I> {
        Bitmap::from_raw(&self.raw)
    }
}

impl<const W: usize, I: Index> DerefMut for BitmapArray<W, I> {
    fn deref_mut(&mut self) -> &mut Bitmap<I> {
        Bitmap::from_raw_mut(&mut self.raw)
    }
}

impl<const W: usize, I: Index> core::ops::BitOr<I> for BitmapArray<W, I> {
    type Output = Self;
    fn bitor(mut self, rhs: I) -> Self {
        self.set(rhs);
        self
    }
}

impl<'a, const W: usize, I: Index> TryFrom<&'a Bitmap<I>> for BitmapArray<W, I> {
    type Error = <[Word; W] as TryFrom<&'a [Word]>>::Error;
    fn try_from(value: &'a Bitmap<I>) -> Result<Self, Self::Error> {
        Ok(Self {
            _marker: PhantomData,
            raw: value.raw.try_into()?
        })
    }
}

impl<const W: usize, I: Index> Default for BitmapArray<W, I> {
    fn default() -> Self { Self { _marker: PhantomData, raw: [0; W] } }
}

impl<const W: usize, I: Index> Debug for BitmapArray<W, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Bitmap::fmt(self, f)
    }
}

pub struct BitmapVec<I: Index = usize> {
    _marker: PhantomData<I>,
    data: Vec<Word>
}

impl<I: Index> Default for BitmapVec<I> {
    fn default() -> Self {
        Self {
            _marker: PhantomData,
            data: Default::default()
        }
    }
}

impl<I: Index> BitmapVec<I> {

    pub fn resize(&mut self, end: I) {
        let end: usize = end.into();
        self.data.resize((end + WORD_BITS-1) >> SHIFT, 0);
    }

}

impl<I: Index> Deref for BitmapVec<I> {
    type Target = Bitmap<I>;
    fn deref(&self) -> &Bitmap<I> {
        Bitmap::from_raw(&self.data)
    }
}

impl<I: Index> DerefMut for BitmapVec<I> {
    fn deref_mut(&mut self) -> &mut Bitmap<I> {
        Bitmap::from_raw_mut(&mut self.data)
    }
}

impl<I: Index> Debug for BitmapVec<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Bitmap::fmt(self, f)
    }
}

pub struct BitMatrix<I: Index=usize, J: Index=I> {
    _marker: PhantomData<fn(&(I,J))>,
    data: Vec<Word>,
    width: usize // words
}

impl<I: Index, J: Index> BitMatrix<I, J> {

    pub fn resize(&mut self, rows: I, cols: J) {
        let wbits: usize = cols.into();
        let width = max((wbits + WORD_BITS-1) >> SHIFT, 1);
        let height: usize = rows.into();
        self.data.resize(width * height, 0);
        self.width = width;
    }

    pub fn clear_all(&mut self) {
        self.data.fill(0);
    }

    pub fn get_rows_mut<const N: usize>(&mut self, idx: [I; N]) -> [&mut Bitmap<J>; N]
        where I: PartialEq
    {
        for i in 0..N {
            for j in i+1..N {
                assert!(idx[i] != idx[j]);
            }
        }
        let base = self.data.as_mut_ptr();
        let width = self.width;
        let mut ret: MaybeUninit<[&mut Bitmap<J>; N]> = MaybeUninit::uninit();
        let p = ret.as_mut_ptr() as *mut &mut Bitmap<J>;
        for i in 0..N {
            let j: usize = idx[i].into();
            let ofs = width*j;
            assert!(ofs < self.data.len());
            unsafe {
                *p.add(i) = Bitmap::from_raw_mut(slice::from_raw_parts_mut(base.add(ofs), width))
            }
        }
        unsafe { ret.assume_init() }
    }

    pub fn pairs(&self) -> impl Iterator<Item=(I, &Bitmap<J>)> {
        self.data
            .chunks_exact(self.width)
            .enumerate()
            .map(|(i,w)| (i.into(), Bitmap::from_raw(w)))
    }

    pub fn rows(&self) -> I {
        (self.data.len()/self.width).into()
    }

}

impl<I: Index, J: Index> Default for BitMatrix<I, J> {
    fn default() -> Self {
        Self {
            _marker: PhantomData,
            data: Default::default(),
            width: 0
        }
    }
}

impl<I: Index, J: Index> core::ops::Index<I> for BitMatrix<I, J> {
    type Output = Bitmap<J>;
    fn index(&self, row: I) -> &Bitmap<J> {
        let row: usize = row.into();
        Bitmap::from_raw(&self.data[row*self.width..(row+1)*self.width])
    }
}

impl<I: Index, J: Index> core::ops::IndexMut<I> for BitMatrix<I, J> {
    fn index_mut(&mut self, row: I) -> &mut Bitmap<J> {
        let row: usize = row.into();
        Bitmap::from_raw_mut(&mut self.data[row*self.width..(row+1)*self.width])
    }
}

impl<I: Index, J: Index> Debug for BitMatrix<I, J> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("[\n")?;
        for (id, row) in self.pairs() {
            let id: usize = id.into();
            write!(f, "  {:-4} ", id)?;
            row.fmt(f)?;
            f.write_char('\n')?;
        }
        f.write_char(']')
    }
}
