//! Error handling.

use core::ffi::CStr;

use crate::compile::{Ccx, CompileError};
use crate::typestate::R;

/* ---- Compiler errors ----------------------------------------------------- */

#[derive(Clone, Copy)]
pub enum ErrorMessage {
    InvalidToken,
    ExpectedValue,
    CapNameInTemplate,
    CapPosInBody,
    UndefCap,
    BadImplicitTab
}

impl ErrorMessage {

    pub fn str(self) -> &'static str {
        use ErrorMessage::*;
        match self {
            InvalidToken       => "invalid token",
            ExpectedValue      => "expected value",
            CapNameInTemplate  => "named capture not allowed in templates",
            CapPosInBody       => "positional capture not allowed in macro body",
            UndefCap           => "undefined capture",
            BadImplicitTab     => "implicit table not allowed here"
        }
    }

}

impl CompileError for ErrorMessage {
    fn write(self, ccx: &mut Ccx<(), R, R>) {
        ccx.host.buf.write(self.str());
    }
}

impl CompileError for &CStr {
    fn write(self, ccx: &mut Ccx<(), R, R>) {
        ccx.host.buf.write(self.to_bytes());
    }
}
