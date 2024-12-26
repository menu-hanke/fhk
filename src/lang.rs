//! Language support.

use core::iter::zip;
use core::mem::MaybeUninit;
use core::ptr::NonNull;

use alloc::boxed::Box;
use enumset::EnumSet;

use crate::compile::{self, Ccx};
use crate::emit::{Ecx, Emit, InsValue};
use crate::foreach_lang;
use crate::ir::{Func, InsId};
use crate::lower::CLcx;
use crate::obj::{ObjRef, CALLX};
use crate::parser::Pcx;

pub trait Language: Sized {
    fn parse(pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALLX>>;
    fn lower(lcx: &mut CLcx, ctr: InsId, obj: ObjRef<CALLX>, func: &Func, inputs: &[InsId]) -> InsId;
    fn begin_emit(ccx: &mut Ccx) -> compile::Result<Self>;
    fn emit(ecx: &mut Ecx, id: InsId, lop: u8) -> compile::Result<InsValue>;
    #[allow(unused_variables)]
    fn finish_emit(self, ccx: &mut Ccx<Emit>) -> compile::Result { Ok(()) }
}

macro_rules! define_langs {
    ( $($(#[$($meta:tt)*])? $module:ident::$name:ident;)* ) => {
        #[derive(enumset::EnumSetType)]
        #[repr(u8)]
        pub enum Lang {
            $($name),*
        }

        impl Lang {

            pub fn from_name(name: &[u8]) -> Option<Self> {
                $(
                    $(#[$($meta)*])?
                    const $name: &[u8] = stringify!($name).as_bytes();
                )*
                match name {
                    $(
                        $(#[$($meta)*])?
                        $name => Some(Lang::$name),
                    )*
                        _ => None
                }
            }

            pub fn name(self) -> &'static str {
                match self {
                    $(
                        $(#[$($meta)*])?
                        Self::$name => stringify!($name),
                    )*
                }
            }

        }

        #[repr(C)]
        union AnyLang {
            $(
                $(#[$($meta)*])?
                $name: core::mem::ManuallyDrop<$crate::$module::$name>,
            )*
        }

        impl LangState {
            $(
                $(#[$($meta)*])?
                #[allow(dead_code)]
                pub fn $name(&mut self) -> &mut $crate::$module::$name {
                    unsafe { &mut self.get_mut(Lang::$name).$name }
                }
            )*
        }

        macro_rules! dispatch {
            ($discrim:expr, $lang:ty => $value:expr) => {
                match $discrim {
                    $(
                        $(#[$($meta)*])?
                        Lang::$name => { type Lang = $crate::$module::$name; $value },
                    )*
                }
            }
        }
    };
}

foreach_lang!(define_langs);

impl Lang {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn parse(self, pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALLX>> {
        dispatch!(self, Lang => Lang::parse(pcx, n))
    }

    pub fn lower(
        self,
        lcx: &mut CLcx,
        ctr: InsId,
        obj: ObjRef<CALLX>,
        func: &Func,
        inputs: &[InsId]
    ) -> InsId {
        dispatch!(self, Lang => Lang::lower(lcx, ctr, obj, func, inputs))
    }

    pub fn emit(self, ecx: &mut Ecx, id: InsId, lop: u8) -> compile::Result<InsValue> {
        dispatch!(self, Lang => Lang::emit(ecx, id, lop))
    }

}

// note: this intentionally does *not* implement Drop. you "drop" it by calling `finish`.
pub struct LangState {
    present: EnumSet<Lang>,
    data: NonNull<AnyLang>
}

impl Default for LangState {
    fn default() -> Self {
        Self {
            present: EnumSet::empty(),
            data: NonNull::dangling()
        }
    }
}

impl LangState {

    pub fn new(ccx: &mut Ccx, langs: EnumSet<Lang>) -> compile::Result<Self> {
        let num = langs.len();
        if num == 0 {
            return Ok(Default::default());
        }
        // XXX: replace this with try_collect() when it stabilizes.
        let mut mem: Box<[MaybeUninit<AnyLang>]> = Box::new_uninit_slice(num);
        for (ptr,lang) in zip(mem.iter_mut(), langs.into_iter()) {
            dispatch!(lang, Lang => {
                let l = Lang::begin_emit(ccx)?;
                unsafe { ptr.as_mut_ptr().cast::<Lang>().write(l) }
            });
        }
        Ok(Self {
            present: langs,
            data: unsafe { NonNull::new_unchecked(Box::leak(mem) as *mut _ as *mut _) }
        })
    }

    pub fn finish(self, ccx: &mut Ccx<Emit>) -> compile::Result {
        let mut mem = unsafe {
            Box::from_raw(
                core::ptr::slice_from_raw_parts_mut(self.data.as_ptr(), self.present.len())
            )
        };
        let mut result = Ok(());
        for (ptr,lang) in zip(mem.iter_mut(), self.present) {
            dispatch!(lang, Lang => {
                let l = unsafe { (ptr as *mut AnyLang).cast::<Lang>().read() };
                result = result.and(Lang::finish_emit(l, ccx));
            });
        }
        result
    }

    fn get_mut(&mut self, lang: Lang) -> &mut AnyLang {
        assert!(self.present.contains(lang));
        let idx = (self.present.as_u64_truncated() & ((1 << lang as u8) - 1)).count_ones();
        unsafe { &mut *self.data.as_ptr().add(idx as usize) }
    }

}
