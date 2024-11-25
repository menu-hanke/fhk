//! Memory mapping.

use core::ffi::c_void;
use core::ops::Range;

use enumset::{EnumSet, EnumSetType};

#[derive(EnumSetType)]
pub enum Prot {
    Read,
    Write,
    Exec
}

pub struct Mmap {
    base: *mut c_void,
    size: usize
}

impl Mmap {

    pub fn new(size: usize, prot: EnumSet<Prot>) -> Option<Self> {
        target::map(size, prot)
    }

    pub fn protect(&self, range: Range<usize>, prot: EnumSet<Prot>) {
        if range.is_empty() { return }
        target::protect(self, range, prot)
    }

    pub fn base(&self) -> *mut u8 {
        self.base.cast()
    }

    // note: this function is safe because you can't go out of bounds,
    // but it will segfault if you try to write without PROT_WRITE.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.base.cast(), self.size) }
    }

}

impl Drop for Mmap {

    fn drop(&mut self) {
        unsafe {
            target::unmap(self)
        }
    }

}

#[cfg(unix)]
mod target {

    use core::ffi::c_int;
    use core::ops::Range;

    use enumset::EnumSet;

    use super::{Mmap, Prot};

    fn prot2flags(prot: EnumSet<Prot>) -> c_int {
        prot.as_u8_truncated() as _
    }

    const PAGE_SIZE: usize = 4096;

    // TODO: return io::Result here when it's available on no_std.
    pub fn map(size: usize, prot: EnumSet<Prot>) -> Option<Mmap> {
        match unsafe {
            libc::mmap(
                core::ptr::null_mut(),
                size,
                prot2flags(prot),
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0
            )
        } {
            libc::MAP_FAILED => None,
            base             => Some(Mmap { base, size })
        }
    }

    pub fn protect(mmap: &Mmap, range: Range<usize>, prot: EnumSet<Prot>) {
        let start = range.start & !(PAGE_SIZE-1);
        unsafe {
            libc::mprotect(
                mmap.base.cast::<u8>().add(start).cast(),
                range.end - start,
                prot2flags(prot)
            );
        }
    }

    pub unsafe fn unmap(mmap: &Mmap) {
        libc::munmap(mmap.base, mmap.size);
    }

}

#[cfg(windows)]
mod target {

    use core::ffi::c_void;
    use core::ops::Range;
    use core::ptr;

    use enumset::EnumSet;

    use super::{Mmap, Prot};

    #[link(name="KERNEL32")]
    extern "C" {
        fn VirtualAlloc(lpAddress: *mut c_void, dwSize: usize, flAllocationType: u32, flProtect: u32) -> *mut c_void;
        fn VirtualFree(lpAddress: *mut c_void, dwSize: usize, dwFreeType: u32) -> bool;
        fn VirtualProtect(lpAddress: *mut c_void, dwSize: usize, flNewProtect: u32, lpflOldProtect: *mut u32) -> bool;
    }

    const MEM_COMMIT: u32  = 0x00001000;
    const MEM_RESERVE: u32 = 0x00002000;
    const MEM_RELEASE: u32 = 0x00008000;

    const PAGE_READONLY: u32 = 0x02;
    const PAGE_READWRITE: u32 = 0x04;
    const PAGE_EXECUTE_READ: u32 = 0x20;

    fn prot2flags(prot: EnumSet<Prot>) -> u32 {
        if prot == Prot::Read {
            PAGE_READONLY
        } else if prot == Prot::Read | Prot::Write {
            PAGE_READWRITE
        } else if prot == Prot::Read | Prot::Exec {
            PAGE_EXECUTE_READ
        } else {
            unreachable!()
        }
    }

    pub fn map(size: usize, prot: EnumSet<Prot>) -> Option<Mmap> {
        let base = unsafe {
            VirtualAlloc(ptr::null_mut(), size, MEM_COMMIT | MEM_RESERVE, prot2flags(prot))
        };
        match base.is_null() {
            true => None,
            false => Some(Mmap { base, size })
        }
    }

    pub fn protect(mmap: &Mmap, range: Range<usize>, prot: EnumSet<Prot>) {
        let start = range.start;
        let mut old = 0u32;
        unsafe {
            VirtualProtect(
                mmap.base.add(start),
                range.end - start,
                prot2flags(prot),
                &mut old
            );
        }
    }

    pub unsafe fn unmap(mmap: &Mmap) {
        VirtualFree(mmap.base, 0, MEM_RELEASE);
    }

}
