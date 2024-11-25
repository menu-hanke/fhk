//! Dynamic library loading.

use core::ops::Deref;
use core::ptr::NonNull;

// invariant: never hand out `&mut Lib`.
// then we can treat Lib as pinned.
pub struct Lib { _private: () }

// on unix: handle returned by dlopen
// on windows: handle returned by LoadLibrary*
#[repr(transparent)]
pub struct LibBox(NonNull<Lib>);

impl Drop for LibBox {
    fn drop(&mut self) {
        // TODO: target
        todo!()
    }
}

impl Deref for LibBox {
    type Target = Lib;
    fn deref(&self) -> &Lib {
        unsafe { &*self.0.as_ptr() }
    }
}

// macro_rules! dynlib {
//     (
//         $vis:vis struct $libname:ident {
//             $(fn $name:ident($($pname:ident : $pty:ty),*) $(-> $rty:ty)?;)*
//             $(sym $sname:ident: $sty:ty;)*
//         }
//     ) => {
// 
//         $vis struct $libname {
//             lib: crate::dl::Lib,
//             $( $name: unsafe extern "C" fn($($pty,)*) $(-> $rty)?, )*
//             $( $sname: core::ptr::NonNull<$sty>, )*
//         }
// 
//         impl $libname {
// 
//             pub fn init(lib: crate::dl::Lib) -> Option<Self> {
//                 $(
//                     let $name = unsafe {
//                         core::mem::transmute(
//                             lib.sym(concat!(stringify!($name), "\0").as_bytes())?.as_ptr()
//                         )
//                     };
//                 )*
//                 $(
//                     let $sname = lib.sym(concat!(stringify!($sname), "\0").as_bytes())?.cast();
//                 )*
//                 Some(Self { lib, $($name,)* $($sname,)* })
//             }
// 
//             #[allow(dead_code)]
//             pub fn open(name: &[u8]) -> Option<Self> {
//                 Self::init(crate::dl::Lib::open(name)?)
//             }
// 
//             #[allow(dead_code)]
//             pub fn open_first(name: &[u8]) -> Option<Self> {
//                 Self::init(crate::dl::Lib::open_first(name)?)
//             }
// 
//             $(
//                 #[allow(dead_code)]
//                 pub unsafe fn $name(&self, $($pname : $pty),*) $(-> $rty)? {
//                     let fp: extern "C" fn($($pty),*) $(-> $rty)? = core::mem::transmute(self.$name);
//                     fp($($pname),*)
//                 }
//             )*
// 
//         }
// 
//     };
// }
// 
// pub(crate) use dynlib;

#[cfg(unix)]
#[allow(dead_code)]
mod target {

    use core::ffi::c_void;
    use core::ptr::NonNull;

    use alloc::borrow::Cow;
    use alloc::vec::Vec;

    pub struct Lib(NonNull<c_void>);

    fn cstr(s: &[u8]) -> Cow<'_, [u8]> {
        match s.last() {
            Some(&0) => Cow::Borrowed(s),
            _ => Cow::Owned({
                let mut bytes = Vec::with_capacity(s.len()+1);
                bytes.extend_from_slice(s);
                bytes.push(0);
                bytes
            })
        }
    }

    impl Lib {

        pub fn open(name: &[u8]) -> Option<Self> {
            let ptr = unsafe { libc::dlopen(cstr(name).as_ptr().cast(), libc::RTLD_LAZY) };
            Some(Self(NonNull::new(ptr as _)?))
        }

        pub fn sym(&self, name: &[u8]) -> *const c_void {
            unsafe { libc::dlsym(self.0.as_ptr(), cstr(name).as_ptr().cast()) }
        }

    }

    impl Drop for Lib {
        fn drop(&mut self) {
            unsafe {
                libc::dlclose(self.0.as_ptr());
            }
        }
    }

}

#[cfg(windows)]
mod target {
    /* TODO */
}
