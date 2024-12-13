//! Dealing with array values at runtime (ABSOLUTELY UNSAFE)

use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr::NonNull;

use crate::bump::Bump;
use crate::obj::{ObjRef, ObjectRef, Objects, TPRI, TTEN};
use crate::typing::{Idx, Primitive};

// the point of this enum is to elide bound checks for ArrayType
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Nest { Scalar, Tensor, _2, _3, _4, X5 }

impl Nest {

    unsafe fn outer_unchecked(self) -> Nest {
        core::mem::transmute((self as u8) + 1)
    }

    fn outer(self) -> Nest {
        if self == Nest::X5 { unreachable!() }
        unsafe { self.outer_unchecked() }
    }

    unsafe fn inner_unchecked(self) -> Nest {
        core::mem::transmute((self as u8) - 1)
    }

    // fn inner(self) -> Nest {
    //     if self == Nest::Scalar { unreachable!() }
    //     unsafe { self.inner_unchecked() }
    // }

    fn inner_or_scalar(self) -> Nest {
        match self {
            Nest::Scalar => Nest::Scalar,
            _ => unsafe { self.inner_unchecked() }
        }
    }

}

// TODO: use this in lower
// NOTE: layout here is important. if you change it, update [un]pack, too.
#[derive(Clone, Copy)]
#[repr(C, align(8))]
pub struct ArrayType {
    pri: Primitive,
    nest: Nest,
    deco: [u8; 6] // let me guess, you *need* more indirection?
}

impl ArrayType {

    fn new_scalar(pri: Primitive) -> Self {
        Self {
            pri,
            nest: Nest::Scalar,
            deco: [1, 0, 0, 0, 0, 0]
        }
    }

    fn new_array(mut element: ArrayType, dim: u8) -> Self {
        let nest = element.nest.outer();
        element.deco[nest as usize] = element.deco[element.nest as usize] + dim;
        element.nest = nest;
        element
    }

    pub fn from_obj(objs: &Objects, idx: ObjRef) -> Self {
        match objs.get(idx) {
            ObjectRef::TPRI(&TPRI { ty, .. }) => Self::new_scalar(Primitive::from_u8(ty)),
            ObjectRef::TTEN(&TTEN { elem, dim, .. }) => Self::new_array(
                Self::from_obj(objs, elem),
                dim
            ),
            _ => unreachable!()
        }
    }

    // this must be fast
    #[cfg(target_endian="little")]
    pub unsafe fn unpack_unchecked(ptr: &mut *const u8) -> Self {
        let mut this: ArrayType = core::mem::transmute((*ptr).cast::<u16>().read_unaligned() as u64);
        this.deco[0] = 1;
        *ptr = (*ptr).add(2);
        for i in 1..this.nest as usize+1 {
            this.deco[i] = **ptr;
            *ptr = (*ptr).add(1);
        }
        this
    }

    pub fn pack_into(self, bump: &mut Bump) {
        bump.push([self.pri as u8, self.nest as u8]);
        bump.write(&self.deco[1..self.nest as usize+1]);
    }

    pub fn is_scalar(self) -> bool {
        self.nest == Nest::Scalar
    }

    pub fn is_tensor(self) -> bool {
        self.nest == Nest::Tensor
    }

    pub fn element(self) -> ArrayType {
        let mut element = self;
        element.nest = element.nest.inner_or_scalar();
        element
    }

    pub fn decomposition_size(self) -> usize {
        self.deco[self.nest as usize] as usize
    }

    pub fn primitive(self) -> Primitive {
        self.pri
    }

    // this must be fast. TODO check asm.
    fn element_decomposition_size(self) -> usize {
        self.element().decomposition_size()
    }

    // this must be fast. TODO check asm.
    pub fn dimension(self) -> usize {
        self.decomposition_size() - self.element_decomposition_size()
    }

    // this must be fast. TODO check asm.
    fn shape_info(self) -> (usize, usize) {
        (self.element_decomposition_size(), self.dimension())
    }

}

#[derive(Clone, Copy)]
pub struct ArrayRef<D> {
    // 0 levels of nesting (scalar):
    //   * scalar value
    // 1 level of nesting (tensor/ndarray):
    //   * pointer to scalar
    //   * shape[0], ..., shape[N-1]
    // 2 levels of nesting (ndarray of tensors):
    //   * pointer to pointer to scalar
    //   * pointer to inner shape[0]
    //   ...
    //   * pointer to inner shape[N-1]
    //   * shape[0], ..., shape[M-1]
    // etc.
    // each additional level of nesting adds a level of indirection to each field of the element.
    data: NonNull<()>,
    type_: ArrayType, // invariant: nest != Scalar
    _marker: PhantomData<D>
}

pub type Array<'a> = ArrayRef<&'a ()>;
pub type ArrayMut<'a> = ArrayRef<&'a mut ()>;

impl<'a> Array<'a> {

    pub unsafe fn new_unchecked(data: NonNull<()>, type_: ArrayType) -> Self {
        Self { data, type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub fn type_(self) -> ArrayType {
        self.type_
    }

    #[inline(always)]
    pub fn shape(self) -> &'a [Idx] {
        let (ofs, dim) = self.type_.shape_info();
        unsafe {
            core::slice::from_raw_parts(
                self.data.as_ptr().cast::<*const ()>().add(ofs).cast(),
                dim
            )
        }
    }

    #[inline(always)]
    pub fn data(self) -> &'a [*const ()] {
        let ds = self.type_.element_decomposition_size();
        unsafe { core::slice::from_raw_parts(self.data.as_ptr().cast(), ds) }
    }

}

impl<'a> ArrayMut<'a> {

    pub unsafe fn new_unchecked_mut(data: NonNull<()>, type_: ArrayType) -> Self {
        Self { data, type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub fn borrow<'b>(&'b self) -> Array<'b> {
        ArrayRef { data: self.data, type_: self.type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub fn borrow_mut<'b>(&'b mut self) -> ArrayMut<'b> {
        ArrayRef { data: self.data, type_: self.type_, _marker: PhantomData }
    }

    #[inline(always)]
    pub unsafe fn shape_mut(self) -> &'a mut [Idx] {
        let (ofs, dim) = self.type_.shape_info();
        core::slice::from_raw_parts_mut(
            self.data.as_ptr().cast::<*const ()>().add(ofs).cast(),
            dim
        )
    }

    #[inline(always)]
    pub unsafe fn data_mut(self) -> &'a mut [*mut ()] {
        let ds = self.type_.element_decomposition_size();
        core::slice::from_raw_parts_mut(self.data.as_ptr().cast(), ds)
    }

}

#[repr(C)]
union Slot {
    ptr: *mut (),
    idx: [Idx; 2]
}

// on-stack storage suitable for holding an array representation (NOT the data itself)
pub struct ArrayBuf<const K: usize>([MaybeUninit<Slot>; K]);

impl<const K: usize> Default for ArrayBuf<K> {
    fn default() -> Self {
        Self([const { MaybeUninit::uninit() }; K])
    }
}

impl<'a> Array<'a> {

    pub fn get<'b: 'a, const K: usize>(self, _idx: usize, _buf: &'b mut ArrayBuf<K>) -> Array<'b> {
        // TODO: nest>=2
        todo!()
    }

}

impl<'a> ArrayMut<'a> {

    pub fn new_empty<const K: usize>(_type_: ArrayType, _buf: &'a mut ArrayBuf<K>) -> Self {
        // TODO: nest>=2
        todo!()
    }

}
