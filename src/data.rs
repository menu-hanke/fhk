//! Data files baked into the binary.

// TODO: add option (build.rs?) to compile lua files to bytecode.

#[cfg(any(feature="host-Lua", feature="lang-Lua"))]
pub const TENSOR_LUA: &[u8] = include_bytes!("../data/tensor.lua");

#[cfg(feature="host-Lua")]
pub const HOST_LUA: &[u8] = include_bytes!("../data/host.lua");

#[cfg(feature="lang-Lua")]
pub const CALL_LUA: &[u8] = include_bytes!("../data/call.lua");
