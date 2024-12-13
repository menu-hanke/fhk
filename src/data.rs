//! Data files baked into the binary.

// TODO: add option (build.rs?) to compile lua and R files to bytecode.

#[cfg(any(feature="host-Lua", feature="lang-Lua"))]
pub const TENSOR_LUA: &[u8] = include_bytes!("../data/tensor.lua");

#[cfg(feature="host-Lua")]
pub const HOST_LUA: &[u8] = include_bytes!("../data/host.lua");

#[cfg(feature="lang-Lua")]
pub const CALL_LUA: &[u8] = include_bytes!("../data/call.lua");

// this must be null-terminated because the R API doesn't take a length.
#[cfg(feature="lang-R")]
pub const CALL_R: &[u8] = &crate::concat::concat_slices!(u8; include_bytes!("../data/call.R"), b"\0");
