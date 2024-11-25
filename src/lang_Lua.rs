//! Lua language support.

use crate::compile;
use crate::lang::Language;
use crate::parser::Pcx;

pub struct Lua;

impl Language for Lua {
    const NAME: &'static [u8] = b"Lua";
    type ObjData = ();
    type EmitData = ();
    type ImageData = ();

    fn graph_data() -> Self::ObjData {
        ()
    }

    fn parse_call(data: &mut Self::ObjData, pcx: &mut Pcx) -> compile::Result {
        todo!()
    }
}
