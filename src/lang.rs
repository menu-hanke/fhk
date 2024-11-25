//! Language support.

use core::alloc::Layout;
use core::convert::Infallible;
use core::marker::PhantomData;
use core::mem::{forget, ManuallyDrop};
use core::ptr::{copy_nonoverlapping, NonNull};

use alloc::vec::Vec;
use enumset::EnumSet;

use crate::parser::Pcx;
use crate::{compile, foreach_lang};

pub trait Language {
    const NAME: &'static [u8];
    type ObjData;
    type EmitData;
    type ImageData;
    fn graph_data() -> Self::ObjData;
    fn parse_call(data: &mut Self::ObjData, pcx: &mut Pcx) -> compile::Result;
    // need type_call?
    // fn lower_call(ccx: &mut Ccx<Lower>, call: ExprId) -> compile::Result;
    // need sink_call?
}

macro_rules! define_lang_enum {
    ($($(#[$($meta:tt)*])? $module:ident::$name:ident;)*) => {
        #[derive(enumset::EnumSetType, Debug)]
        #[repr(u8)]
        pub enum Lang {
            $($name,)*
        }

        impl Lang {
            pub fn for_name(name: &[u8]) -> Option<Self> {
                match name {
                    $(
                        $(#[$($meta)*])?
                        <crate::$module::$name as Language>::NAME => Some(Lang::$name),
                    )*
                    _ => None
                }
            }
        }
    };
}

foreach_lang!(define_lang_enum);

// more or less equivalent to the rust enum corresponding to the union `T`,
// with a variant for each language.
pub struct Tagged<T> {
    lang: Lang,
    value: T
}

impl<T> Tagged<T> {

    pub fn lang(&self) -> Lang {
        self.lang
    }

}

macro_rules! define_union {
    (
        pub union $name:ident(Language::$field:ident)
        $($(#[$($attr:tt)*])? $module:ident::$lang:ident;)*
    ) => {
        pub union $name {
            $(
                $(#[$($attr)*])?
                $lang: core::mem::ManuallyDrop<<crate::$module::$lang as Language>::$name>,
            )*
        }
        impl ULang for $name {
            fn drop_in_place(e: Tagged<&mut Self>) {
                match e.lang {
                    $(
                        $(#[$($attr)*])?
                        Lang::$lang => unsafe { core::ptr::drop_in_place(&mut e.value.$lang) },
                    )*
                }
            }
        }
    };
}

foreach_lang!(define_union, pub union ObjData(Language::ObjData));
foreach_lang!(define_union, pub union EmitData(Language::EmitData));
foreach_lang!(define_union, pub union ImageData(Language::ImageData));

macro_rules! define_dispatch {
    ($($(#[$($attr:tt)*])? $module:ident::$lang:ident;)*) => {
        macro_rules! dispatch {
            ($discrim:expr => $value:ident) => {
                match $discrim {
                    $(
                        $(#[$($attr)*])?
                        Lang::$lang => $value!($module::$lang),
                    )*
                }
            }
        }
    };
}

foreach_lang!(define_dispatch);

impl Lang {

    pub fn name(self) -> &'static [u8] {
        macro_rules! value {
            ($module:ident::$lang:ident) => { <crate::$module::$lang as Language>::NAME };
        }
        dispatch!(self => value)
    }

    pub fn graph_data(self) -> Tagged<ObjData> {
        macro_rules! value {
            ($module:ident::$lang:ident) => {
                ObjData {
                    $lang: core::mem::ManuallyDrop::new(
                        <crate::$module::$lang as Language>::graph_data())
                }
            };
        }
        Tagged { lang: self, value: dispatch!(self => value) }
    }

}

impl Tagged<&mut ObjData> {

    pub fn parse_call(self, pcx: &mut Pcx) -> compile::Result {
        macro_rules! value {
            ($module:ident::$lang:ident) => {
                <crate::$module::$lang as Language>::parse_call(
                    unsafe { &mut self.value.$lang }, pcx
                )
            };
        }
        dispatch!(self.lang => value)
    }

}

pub trait ULang {
    fn drop_in_place(v: Tagged<&mut Self>);
}

pub struct LangMap<U: ULang> {
    mask: EnumSet<Lang>,
    ptr: NonNull<u8>, // untyped so that new etc. don't get copied
    _type: PhantomData<U>
}

impl<U: ULang> LangMap<U> {

    #[cold]
    unsafe fn _new(&mut self, lang: Lang, size: usize) -> *mut u8 {
        let mask = self.mask.as_u64_truncated();
        let tail = (mask >> (lang as usize)).count_ones() as usize;
        let head = mask.count_ones() as usize - tail;
        let total = head + tail + 1;
        let ptr = NonNull::new(if mask == 0 {
            alloc::alloc::alloc(Layout::from_size_align_unchecked(total*size, 8))
        } else {
            alloc::alloc::realloc(
                self.ptr.as_ptr(),
                Layout::from_size_align_unchecked((head+tail)*size, 8),
                total*size
            )
        }).unwrap();
        if tail > 0 {
            core::ptr::copy(ptr.as_ptr().add(head*size), ptr.as_ptr().add((head+1)*size), tail*size);
        }
        self.mask.insert(lang);
        self.ptr = ptr;
        ptr.as_ptr().add(head*size)
    }

    unsafe fn new(&mut self, lang: Lang) -> NonNull<U> {
        NonNull::new_unchecked(self._new(lang, size_of::<U>()).cast())
    }

    fn data_ptr(&self) -> *mut U {
        self.ptr.as_ptr() as _
    }

    fn get_ptr(&self, lang: Lang) -> Option<NonNull<U>> {
        let mask = self.mask.as_u64_truncated();
        if (mask & (1 << lang as u64)) != 0 {
            let idx = (mask & ((1 << lang as u64) - 1)).count_ones() as usize;
            Some(unsafe { NonNull::new_unchecked(self.data_ptr().add(idx)) })
        } else {
            None
        }
    }

    pub fn insert(&mut self, entry: Tagged<U>) {
        let ptr = match self.get_ptr(entry.lang) {
            Some(ptr) => ptr,
            None => unsafe { self.new(entry.lang) }
        };
        *unsafe { &mut *ptr.as_ptr() } = entry.value;
    }

    pub fn contains(&self, lang: Lang) -> bool {
        self.mask.contains(lang.into())
    }

    pub fn get_mut(&mut self, lang: Lang) -> Option<Tagged<&mut U>> {
        match self.get_ptr(lang) {
            Some(ptr) => Some(Tagged { lang, value: unsafe { &mut *ptr.as_ptr() } }),
            None      => None
        }
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item=Tagged<&mut U>> {
        self.mask.iter()
            .enumerate()
            .map(|(idx,lang)| Tagged { lang, value: unsafe { &mut *self.data_ptr().add(idx) }})
    }

    // not trait because i can't be bothered trying to type out the return type
    pub fn into_iter(self) -> impl Iterator<Item=Tagged<U>> {
        let this = ManuallyDrop::new(self);
        this.mask
            .iter()
            .enumerate()
            .map(move |(idx,lang)| Tagged {
                lang,
                value: unsafe { core::ptr::read(this.data_ptr().add(idx))
            }})
    }

    pub fn try_from_iter<I,E>(iter: I) -> Result<Self, E>
        where I: Iterator<Item=Result<Tagged<U>, E>>
    {
        // needless allocation here that could easily be eliminated but not worth any effort
        // since this function is called like twice during the entire compiler pipeline.
        let mut buf: Vec<Tagged<U>> = Default::default();
        let mut mask: EnumSet<Lang> = Default::default();
        buf.reserve_exact(iter.size_hint().0);
        for e in iter {
            let e = e?;
            mask |= e.lang;
            buf.push(e);
        }
        Ok(if mask.is_empty() {
            Default::default()
        } else {
            let ptr = unsafe {
                alloc::alloc::alloc(Layout::from_size_align_unchecked(mask.len()*size_of::<U>(), 8))
            };
            let mask64 = mask.as_u64_truncated();
            for e in &buf {
                unsafe {
                    copy_nonoverlapping(
                        &e.value,
                        ptr.cast::<U>().add(
                            (mask64 & ((1 << (e.lang as usize))-1)).count_ones() as usize
                        ),
                        1
                    );
                }
            }
            forget(buf);
            Self {
                mask,
                ptr: unsafe { NonNull::new_unchecked(ptr) },
                _type: PhantomData
            }
        })
    }

    pub fn from_iter<I>(iter: I) -> Self
        where I: Iterator<Item=Tagged<U>>
    {
        Self::try_from_iter::<_, Infallible>(iter.map(Ok)).unwrap()
    }

}

impl<U: ULang> Default for LangMap<U> {
    fn default() -> Self {
        Self {
            mask: EnumSet::empty(),
            ptr: NonNull::dangling(),
            _type: PhantomData
        }
    }
}

impl<U: ULang> Drop for LangMap<U> {
    fn drop(&mut self) {
        for e in self.iter_mut() {
            U::drop_in_place(e)
        }
    }
}
