//! Byte strings.

use core::borrow::Borrow;
use core::fmt::{Display, Write};
use core::mem::transmute;
use core::ops::Deref;
use core::str::{self, Utf8Error};

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

pub struct ByteStr([u8]);

#[derive(Default)]
pub struct ByteString(Vec<u8>);

impl ByteString {

    pub fn new() -> Self {
        Default::default()
    }

    pub fn push_bytes(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }

    pub fn push_str(&mut self, s: &str) {
        self.push_bytes(s.as_bytes());
    }

    pub fn push(&mut self, ch: char) {
        match ch.len_utf8() {
            1 => self.0.push(ch as u8),
            _ => self.0.extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    pub fn to_str(&self) -> Result<&str, Utf8Error> {
        str::from_utf8(&self.0)
    }

    pub fn into_boxed_slice(self) -> Box<[u8]> {
        self.0.into_boxed_slice()
    }

    pub fn null_terminate(&mut self) {
        if self.0.last() != Some(&0) {
            self.0.push(0);
        }
    }

    pub fn clear(&mut self) {
        self.0.clear()
    }

}

impl Deref for ByteString {
    type Target = ByteStr;

    fn deref(&self) -> &ByteStr {
        let bytes: &[u8] = &self.0;
        bytes.into()
    }
}

impl Borrow<ByteStr> for ByteString {
    fn borrow(&self) -> &ByteStr {
        &*self
    }
}

impl From<String> for ByteString {
    fn from(value: String) -> Self {
        Self(value.into_bytes())
    }
}

impl Write for ByteString {

    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.push_bytes(s.as_bytes());
        Ok(())
    }

    fn write_char(&mut self, c: char) -> core::fmt::Result {
        self.push(c);
        Ok(())
    }

}

impl Display for ByteString {

    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.to_str().map_err(|_| core::fmt::Error)?)
    }

}

impl Deref for ByteStr {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.0
    }
}

impl ToOwned for ByteStr {
    type Owned = ByteString;

    fn to_owned(&self) -> Self::Owned {
        ByteString(self.0.to_owned())
    }
}

impl From<&[u8]> for &ByteStr {
    fn from(value: &[u8]) -> Self {
        unsafe { transmute(value) }
    }
}

impl<const N: usize> From<&[u8; N]> for &ByteStr {
    fn from(value: &[u8; N]) -> Self {
        let bytes: &[u8] = value;
        bytes.into()
    }
}
