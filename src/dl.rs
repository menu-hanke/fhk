//! Dynamic library loading.

use core::ffi::{c_void, CStr};
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
        unsafe {
            target::close(self);
        }
    }
}

impl Deref for LibBox {
    type Target = Lib;
    fn deref(&self) -> &Lib {
        unsafe { &*self.0.as_ptr() }
    }
}

pub fn open(mut name: &[u8]) -> Option<LibBox> {
    while let Some(end) = name.iter().position(|&c| c == 0) {
        let lib = unsafe { target::open(name.as_ptr().cast()) };
        if lib.is_some() {
            return lib;
        }
        name = &name[end+1..];
    }
    None
}

impl Lib {

    pub fn sym(&self, name: &CStr) -> *mut c_void {
        unsafe { target::sym(self, name.as_ptr()) }
    }

}

macro_rules! lib {
    (
        $vis:vis struct $libname:ident {
            $(fn $name:ident($($pname:ident : $pty:ty),*) $(-> $rty:ty)?;)*
            $(extern $sname:ident: $sty:ty;)*
        }
    ) => {

        $vis struct $libname {
            lib: $crate::dl::LibBox,
            $( $name: unsafe extern "C" fn($($pty,)*) $(-> $rty)?, )*
            $( $sname: *mut $sty, )*
        }

        impl $libname {

            pub fn new(lib: $crate::dl::LibBox) -> Option<Self> {
                $(
                    let $name = lib.sym({
                        let name = concat!(stringify!($name), "\0");
                        unsafe { core::ffi::CStr::from_ptr(name.as_ptr().cast()) }
                    });
                    if $name.is_null() { return None }
                    let $name = unsafe { core::mem::transmute($name) };
                )*
                $(
                    let $sname = lib.sym({
                        let name = concat!(stringify!($sname), "\0");
                        unsafe { core::ffi::CStr::from_ptr(name.as_ptr().cast()) }
                    }) as _;
                )*
                Some(Self { lib, $($name,)* $($sname,)* })
            }

            $(
                #[allow(dead_code)]
                pub unsafe fn $name(&self, $($pname : $pty),*) $(-> $rty)? {
                    unsafe { (self.$name)($($pname),*) }
                }
            )*

        }

    };
}

pub(crate) use lib;

#[cfg(unix)]
mod target {

    use core::ffi::{c_char, c_void};
    use core::ptr::NonNull;

    use super::{Lib, LibBox};

    pub unsafe fn open(name: *const c_char) -> Option<LibBox> {
        Some(LibBox(NonNull::new(unsafe { libc::dlopen(name, libc::RTLD_LAZY) }.cast())?))
    }

    pub unsafe fn sym(lib: &Lib, name: *const c_char) -> *mut c_void {
        // i'm not sure if const ref -> mut pointer is technically haram, but lib is zero-sized and
        // never dereferenced in rust code so it's probably fine (?).
        // if this is a problem, then ig the zero-sized type inside it can be wrapped in an
        // unsafecell.
        // but since unsafecell semantics work on byte ranges (i think?) it is not necessary (i
        // think?).
        (unsafe { libc::dlsym(lib as *const Lib as *mut Lib as *mut c_void, name) }) as *mut c_void
    }

    pub unsafe fn close(lib: &Lib) {
        // see comment in sym()
        unsafe { libc::dlclose(lib as *const Lib as *mut Lib as *mut c_void); }
    }

}

#[cfg(windows)]
mod target {

    use core::ffi::{c_char, c_int, c_void};
    use core::ptr::NonNull;

    use super::{Lib, LibBox};

    #[link(name="KERNEL32")]
    unsafe extern "C" {
        fn LoadLibraryA(lpLibFileName: *const c_char) -> *mut c_void;
        fn GetProcAddress(hModule: *mut c_void, lpProcName: *const c_char) -> *mut c_void;
        fn FreeLibrary(hLibModule: *mut c_void) -> c_int;
    }

    pub unsafe fn open(name: *const c_char) -> Option<LibBox> {
        Some(LibBox(NonNull::new(unsafe { LoadLibraryA(name) }.cast())?))
    }

    pub unsafe fn sym(lib: &Lib, name: *const c_char) -> *mut c_void {
        unsafe { GetProcAddress(lib as *const Lib as *mut Lib as *mut c_void, name) }
    }

    pub unsafe fn close(lib: &Lib) {
        unsafe { FreeLibrary(lib as *const Lib as *mut Lib as *mut c_void); }
    }

}
