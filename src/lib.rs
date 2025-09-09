#![allow(nonstandard_style)]
#![no_std]

extern crate alloc;

mod array;
mod bitmap;
mod bump;
mod compile;
mod concat;
mod controlflow;
mod data;
mod dl;
mod dump;
mod emit;
mod finalize;
mod hash;
mod image;
mod index;
mod intern;
mod ir;
mod layout;
mod lex;
mod lower;
mod mcode;
mod mem;
mod mmap;
mod obj;
mod parse;
mod parser;
mod relation;
mod schedule;
mod support;
mod trace;
mod translate;
mod typeinfer;
mod typestate;
mod typing;
mod zerocopy_union;

/* ---- Optimizer ----------------------------------------------------------- */

mod opt_control;
mod opt_fold;
mod opt_inline;
mod optimize;

/* ---- Host support -------------------------------------------------------- */

#[cfg_attr(feature="host-Lua", path="host_Lua.rs")]
mod host;

/* ---- Language support ---------------------------------------------------- */

mod lang;

macro_rules! foreach_lang {
    ($mac:path $(,$($extra:tt)*)?) => {
        $mac! {
            $($($extra)*)?
            #[cfg(feature="lang-C")]     lang_C::C;
            #[cfg(feature="lang-Lua")]   lang_Lua::Lua;
            #[cfg(feature="lang-R")]     lang_R::R;
            #[cfg(feature="lang-Table")] lang_Table::Table;
        }
    };
}

pub(crate) use foreach_lang;

macro_rules! define_lang_mods {
    ($($(#[$($meta:tt)*])? $module:ident::$name:ident;)*) => {
        $(
            $(#[$($meta)*])?
            mod $module;
        )*
    };
}

foreach_lang!(define_lang_mods);

/* -------------------------------------------------------------------------- */

pub const FHK_VERSION_STRING: &[u8] = &concat::concat_slices!(u8;
    match option_env!("FHK_GITHASH") { Some(v) => v.as_bytes(), None => b"(unknown version)" },
    #[cfg(feature="host-Lua")]   b" Lua",
    b" [",
    #[cfg(feature="lang-C")]     b" C",
    #[cfg(feature="lang-Lua")]   b" Lua",
    #[cfg(feature="lang-R")]     b" R",
    #[cfg(feature="lang-Table")] b" Table",
    #[cfg(all(feature="lang-Table", feature="csv"))] b"(+csv)",
    b" ]",
    b"\0"
);

#[repr(transparent)] struct Version(*const core::ffi::c_char);
unsafe impl Sync for Version {}

#[unsafe(no_mangle)]
static fhk_VERSION: Version = Version(FHK_VERSION_STRING.as_ptr().cast());
