//! Intrinsic function definitions.

use enumset::EnumSetType;

use crate::typing::{scheme, Scheme};

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

        const INTRINSIC_FUNC: phf::Map<&[u8], Intrinsic> = phf::phf_map! {
            $( $( $func => Intrinsic::$name, )? )*
        };
    };
}

const LOGIC: &Scheme = scheme![t.PriBool : [t t] -> t];
const CMP: &Scheme = scheme![t n b.PriBool : [(Tensor t n) (Tensor t n)] -> (Tensor b n)];
const ARITH: &Scheme = scheme![t.PriNum n : [(Tensor t n) (Tensor t n)] -> (Tensor t n)];
const FPMATH: &Scheme = scheme![t.PriNum n : [(Tensor t n)] -> (Tensor t n)];

define_intrinsics! {
    // binary operators ORDER BINOP
    OR             :: LOGIC;
    AND            :: LOGIC;
    ADD            :: ARITH;
    SUB            :: ARITH;
    MUL            :: ARITH;
    DIV            :: ARITH;
    POW            :: [t.PriNum u.PriNum n : [(Tensor t n) (Tensor u n)] -> (Tensor t n)];
    EQ             :: CMP;
    NE             :: CMP;
    LT             :: CMP;
    LE             :: CMP;
    // unary math
    UNM            :: [t.PriNum n : [(Tensor t n)] -> (Tensor t n)];
    EXP    b"exp"  :: FPMATH;
    LOG    b"log"  :: FPMATH;
    // unary logic
    NOT            :: [t.PriBool n : [(Tensor t n)] -> (Tensor t n)];
    // logic
    // SELECT      :: [(T:{B1}, U) : (Func U T U U)];
    // vector math
    SUM    b"sum"  :: [t n : [(Tensor t n)] -> t];
    // types
    CONV   b"conv" :: [t u n : [(Tensor t n)] -> (Tensor u n)];
    // SPLAT          :: [];
    REP            :: [t n m : [(Tensor t n)] -> (Tensor t m)];
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

    pub fn from_func(name: &[u8]) -> Option<Intrinsic> {
        INTRINSIC_FUNC.get(name).cloned()
    }

    pub fn is_broadcast(self) -> bool {
        use Intrinsic::*;
        (OR|AND|ADD|SUB|MUL|DIV|POW|EQ|NE|LT|LE|UNM|EXP|LOG|NOT|CONV).contains(self)
    }

}
