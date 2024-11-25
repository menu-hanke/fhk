//! Intrinsic function definitions.

use enumset::EnumSetType;

use crate::typing::{scheme, Scheme, PRI_IDX, PRI_NUM};

macro_rules! define_intrinsics {
    (@scheme [$($scheme:tt)*]) => { &scheme!($($scheme)*) };
    (@scheme $v:expr) => { $v };
    ( $( $name:ident $($func:literal)? :: $scheme:tt;)* ) => {
        #[derive(EnumSetType)]
        #[repr(u8)]
        pub enum Intrinsic { $($name),* }

        const INTRINSIC_SCHEME: &[&Scheme] = &[
            $(define_intrinsics!(@scheme $scheme)),*
        ];

        impl Intrinsic {
            pub fn from_func(name: &[u8]) -> Option<Intrinsic> {
                match name {
                    $($($func => Some(Intrinsic::$name),)?)*
                    _ => None
                }
            }
        }
    };
}

// x

const FPMATH: &Scheme = scheme![t.PRI_NUM n : [(Tensor t n)] -> (Tensor t n)];

define_intrinsics! {
    UNM             :: [t.PRI_NUM n : [(Tensor t n)] -> (Tensor t n)];
    EXP    b"exp"   :: FPMATH;
    LOG    b"log"   :: FPMATH;
    NOT             :: [t.B1 n : [(Tensor t n)] -> (Tensor t n)];
    SUM    b"sum"   :: [t n : [(Tensor t n)] -> t];
    WHICH  b"which" :: [t.B1 u.PRI_IDX n : [(Tensor t n)] -> (Tensor u n)];
    CONV   b"conv"  :: [t u n : [(Tensor t n)] -> (Tensor u n)];
    REP    b"rep"   :: [t n m : [(Tensor t n)] -> (Tensor t m)];
    SPREAD          :: [t : [t] -> t];
}

impl Intrinsic {

    pub fn scheme(self) -> &'static Scheme {
        INTRINSIC_SCHEME[self as usize]
    }

    pub fn from_u8(raw: u8) -> Intrinsic {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Intrinsic as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn is_annotation(self) -> bool {
        // SPLAT also
        self == Intrinsic::SPREAD
    }

    pub fn is_broadcast(self) -> bool {
        use Intrinsic::*;
        (OR|AND|ADD|SUB|MUL|DIV|POW|EQ|NE|LT|LE|UNM|EXP|LOG|NOT|CONV).contains(self)
    }

}
