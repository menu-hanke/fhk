#![allow(nonstandard_style)]
#![no_std]

extern crate alloc;

mod bitmap;
mod bump;
mod compile;
mod concat;
mod controlflow;
mod data;
mod dataflow;
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
mod link;
mod lower;
mod mcode;
mod mem;
mod mmap;
mod obj;
mod parse;
mod parser;
mod schedule;
mod support;
mod trace;
mod translate;
mod typeinfer;
mod typestate;
mod typing;

/* ---- Optimizer ----------------------------------------------------------- */

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
            #[cfg(feature="lang-C")] lang_C::C;
            #[cfg(feature="lang-Lua")] lang_Lua::Lua;
//            #[cfg(feature="lang-R")] lang_R::R;
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
