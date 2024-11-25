//! Memory mapping.

#[cfg(unix)]
mod target {

    use core::ffi::{c_int, c_void};
    use core::ops::Range;

    pub type Prot = c_int;

    pub struct Mmap {
        base: *mut c_void,
        size: usize
    }

    impl Mmap {
        pub const READ: Prot  = libc::PROT_READ;
        pub const WRITE: Prot = libc::PROT_WRITE;
        pub const EXEC: Prot  = libc::PROT_EXEC;
    }

    const PAGE_SIZE: usize = 4096;

    // TODO: return io::Result here when it's available on no_std.
    pub fn mmap(size: usize, prot: c_int) -> Option<Mmap> {
        match unsafe {
            libc::mmap(
                core::ptr::null_mut(),
                size,
                prot,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0
            )
        } {
            libc::MAP_FAILED => None,
            base             => Some(Mmap { base, size })
        }
    }

    impl Mmap {

        pub fn base(&self) -> *mut u8 {
            self.base.cast()
        }

        // note: this function is safe because you can't go out of bounds,
        // but it will segfault if you try to write without PROT_WRITE.
        pub fn as_mut_slice(&mut self) -> &mut [u8] {
            unsafe { core::slice::from_raw_parts_mut(self.base.cast(), self.size) }
        }

        pub fn protect(&self, range: Range<usize>, prot: c_int) {
            if range.is_empty() { return; }
            assert!(range.end <= self.size);
            let start = range.start & !(PAGE_SIZE-1);
            unsafe {
                libc::mprotect(
                    self.base.cast::<u8>().add(start).cast(),
                    range.end - start,
                    prot
                );
            }
        }

    }

    impl Drop for Mmap {

        fn drop(&mut self) {
            unsafe {
                libc::munmap(self.base, self.size);
            }
        }

    }

}

#[cfg(windows)]
mod target {
    /* TODO */
}

pub use target::*;
