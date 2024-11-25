//! Intrinsic function definitions.

use enumset::EnumSetType;

use crate::typing::{scheme, Primitive, Scheme};

macro_rules! define_intrinsics {
    (@scheme [$($scheme:tt)*]) => { &scheme!($($scheme)*) };
    (@scheme $v:expr) => { $v };
    ( $( $name:ident $($func:literal)? :: $scheme:tt;)* ) => {
        #[derive(EnumSetType)]
        #[repr(u8)]
        pub enum Intrinsic { $($name),* }

        const INTRINSIC_SCHEME: &'static [&'static Scheme] = &[
            $(define_intrinsics!(@scheme $scheme)),*
        ];

        const INTRINSIC_FUNC: phf::Map<&'static [u8], Intrinsic> = phf::phf_map! {
            $( $( $func => Intrinsic::$name, )? )*
        };
    };
}

const LOGIC: &'static Scheme = scheme![(T:{B1}) : (Func T T T)];

const CMP: &'static Scheme = scheme![
    (T, N, B:{B1}) : (Func (Tensor B N) (Tensor T N) (Tensor T N))
];

const NUM: u16 = {
    use Primitive::*;
    (1 << I8 as u8) | (1 << I16 as u8) | (1 << I32 as u8) | (1 << I64 as u8)
        | (1 << U8 as u8) | (1 << U16 as u8) | (1 << U32 as u8) | (1 << U64 as u8)
        | (1 << F32 as u8) | (1 << F64 as u8)
};

const FP: u16 = {
    use Primitive::*;
    (1 << F32 as u8) | (1 << F64 as u8)
};

const ARITH: &'static Scheme = scheme![
    (T:NUM, N) : (Func (Tensor T N) (Tensor T N) (Tensor T N))
];

const FPMATH: &'static Scheme = scheme![
    (T:FP, N) : (Func (Tensor T N) (Tensor T N))
];

define_intrinsics! {
    // binary operators ORDER BINOP
    OR             :: LOGIC;
    AND            :: LOGIC;
    ADD            :: ARITH;
    SUB            :: ARITH;
    MUL            :: ARITH;
    DIV            :: ARITH;
    POW            :: [(T:NUM, U:NUM, N) : (Func (Tensor T N) (Tensor T N) (Tensor U N))];
    EQ             :: CMP;
    NE             :: CMP;
    LT             :: CMP;
    LE             :: CMP;
    // unary math
    UNM            :: [(T:NUM, N) : (Func (Tensor T N) (Tensor T N))];
    EXP    b"exp"  :: FPMATH;
    LOG    b"log"  :: FPMATH;
    // unary logic
    NOT            :: [(T:{B1}, N) : (Func (Tensor T N) (Tensor T N))];
    // logic
    // SELECT      :: [(T:{B1}, U) : (Func U T U U)];
    // types
    CONV   b"conv" :: [(T, U, N) : (Func (Tensor T N) (Tensor U N))];
    SPLAT          :: [(T, N) : (Func (Tensor T N) (Splat T))];
    REP            :: [(T, N, M) : (Func (Tensor T N) (Tensor T M))];
    // vector math
    SUM    b"sum"  :: [(T, N) : (Func T (Tensor T N))];
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
