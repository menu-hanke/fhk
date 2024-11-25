//! Lua language support.

use crate::compile::{self, Ccx};
use crate::lang::Language;
use crate::obj::{ObjRef, CALLX};
use crate::parser::Pcx;

#[derive(Default)]
pub struct Lua {

}

// funcdef :: (module+func)|source + arg?
// arg     :: value + arg?
// value   :: obj|tab
// tab     :: key next
// etc...

impl Language for Lua {

    fn parse_call(pcx: &mut Pcx) -> compile::Result<ObjRef<CALLX>> {
        todo!()
    }

    fn begin_emit(_: &mut Ccx) -> compile::Result<Self> {
        Ok(Default::default())
    }

}
