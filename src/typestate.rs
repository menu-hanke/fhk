//! Small type state library.

use core::marker::PhantomData;
use core::mem::transmute;
use core::ops::{Deref, DerefMut};

pub struct RW;
pub struct R<'a>(PhantomData<*mut &'a ()>);

// Access<T, RW> behaves like &mut T, but without indirection
// Access<T, R<'a>> behaves like &'a T, but without indirection
// the main point is that you can get aliasing `&'a T`s from an &mut Access<T, R<'a>>.
// why does this work? Access<T, R<'a>> is invariant wrt. to 'a, so as long as the creation
// of Access<T, R<'a>> is controlled somehow, eg. they are only handed out from a closure,
// then safe code cannot create an instance of Access<T, R<'_>> that could be mem::swapped
// or otherwise written to the &mut Access<T, R<'a>>.
// (and this is why a safe constructor is only provided for Access<T, RW>)
#[repr(transparent)]
pub struct Access<T,A>(T, PhantomData<A>);

impl<T> Access<T, RW> {

    pub fn new(value: T) -> Self {
        Self(value, PhantomData)
    }

}

impl<T: Default> Default for Access<T, RW> {
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<'a, T: 'a> Access<T, R<'a>> {

    pub fn borrow(a: &Self) -> &'a T {
        unsafe { transmute(a) }
    }

}

impl<T,A> Deref for Access<T,A> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> DerefMut for Access<T,RW> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

// markers for using typestate for partial borrows.
#[derive(Clone, Copy, Default)]
pub struct Present;
#[derive(Clone, Copy, Default)]
pub struct Absent;

macro_rules! typestate_union {
    (
        $vis:vis union $name:ident : $union:ident
        { $($field:ident: $ty:ty),* }
    ) => {

        #[repr(C)]
        union $union {
            __absent: crate::typestate::Absent,
            $( $field: core::mem::ManuallyDrop<$ty> ),*
        }

        #[repr(transparent)]
        pub struct $name<T=crate::typestate::Absent>($union, core::marker::PhantomData<fn(&T)>);

        impl Default for $name {
            fn default() -> Self {
                Self($union { __absent: Default::default() }, Default::default())
            }
        }

        $(
            impl From<$ty> for $name<$ty> {
                fn from(value: $ty) -> Self {
                    Self($union { $field: core::mem::ManuallyDrop::new(value) },
                    core::marker::PhantomData)
                }
            }
        )*

        // it's ok to implement Deref[Mut] for all types, since constructing the union either
        // requires using unsafe or one of the safe wrappers.
        impl<T> core::ops::Deref for $name<T> {
            type Target = T;
            fn deref(&self) -> &T {
                unsafe { core::mem::transmute(self) }
            }
        }

        impl<T> core::ops::DerefMut for $name<T> {
            fn deref_mut(&mut self) -> &mut T {
                unsafe { core::mem::transmute(self) }
            }
        }

        impl<T> Drop for $name<T> {
            fn drop(&mut self) {
                drop(unsafe { core::ptr::read(self as *mut _ as *mut T) })
            }
        }

    };
}

pub(crate) use typestate_union;
