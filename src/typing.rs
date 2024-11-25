//! Type system.

use enumset::EnumSetType;

use crate::ir::Type;

#[derive(EnumSetType, Debug)]
#[repr(u8)]
pub enum Primitive {
    // ORDER PRI
    // numeric types first, in order of assignment preference
    F64, F32,
    I64, I32, I16, I8,
    U64, U32, U16, U8,
    B1,
    PTR,
    STR,
}

impl Primitive {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn to_ir(self) -> Type {
        const PRI2IR: &'static [Type] = {
            use Type::*;
            // ORDER PRI
            &[F64, F32, I64, I32, I16, I8, I64, I32, I16, I8, B1, PTR]
        };
        PRI2IR[self as usize]
    }

    pub fn is_unsigned(self) -> bool {
        use Primitive::*;
        (U8|U16|U32|U64).contains(self)
    }

}

#[derive(EnumSetType)]
pub enum Constructor {
    Tensor, // (elem dim)
    Pair,   // (left right)
    Func,   // (arg ret)
    Unit,   // ()
    // NOTE: if more constructors are needed, typeinfer::Type needs another tag bit
}

impl Constructor {

    pub const TENSOR: u8 = Self::Tensor as _;
    pub const PAIR: u8 = Self::Pair as _;
    pub const UNIT: u8 = Self::Unit as _;

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn arity(self) -> u8 {
        use Constructor::*;
        match self {
            Tensor | Pair | Func => 2,
            Unit => 0
        }
    }

}

#[derive(Clone, Copy)]
pub enum SchemeBytecode {
    Con(Constructor),  // [-n, +1] apply constructor
    PriNum,            // [-1], apply PRI_NUM constraint
    PriBool,           // [-1], apply PRI_B1 constraint
    Gen(u8)            // [+1], push generic
}

impl SchemeBytecode {

    pub const fn encode(self) -> u8 {
        use SchemeBytecode::*;
        // FIXME replace with core::mem::variant_count when it stabilizes
        const CON_VARIANT_COUNT: u8 = <Constructor as enumset::__internal::EnumSetTypePrivate>
            ::VARIANT_COUNT as _;
        match self {
            Con(con) => con as u8,
            PriNum   => CON_VARIANT_COUNT,
            PriBool  => CON_VARIANT_COUNT+1,
            Gen(i)   => CON_VARIANT_COUNT+2+i
        }
    }

    pub fn decode(raw: u8) -> Self {
        use SchemeBytecode::*;
        // FIXME replace with core::mem::variant_count when it stabilizes
        const CON_VARIANT_COUNT: u8 = <Constructor as enumset::__internal::EnumSetTypePrivate>
            ::VARIANT_COUNT as _;
        if raw < CON_VARIANT_COUNT {
            Con(unsafe { core::mem::transmute(raw)} )
        } else if raw == CON_VARIANT_COUNT {
            PriNum
        } else if raw == CON_VARIANT_COUNT+1 {
            PriBool
        } else {
            Gen(raw - CON_VARIANT_COUNT-2)
        }
    }

}

// syntax:
//   (Con a b c)   push a; push b; push c; apply Con;
//   [...] -> b    emit (Func [...] b)
//   []            emit (Unit)
//   [a]           emit (Pair a (Unit))
//   [a b]         emit (Pair a (Pair b (Unit)))
macro_rules! scheme {
    (@generics $idx:expr; ) => {};
    (@generics $idx:expr; $generic:ident $($rest:ident)*) => {
        const $generic: u8 = $idx;
        $crate::typing::scheme!(@generics $idx+1; $($rest)*);
    };
    (@emit ($con:ident $($x:tt)*)) => {
        $crate::concat::concat_slices!(
            u8;
            $( &$crate::typing::scheme!(@emit $x), )*
            &[ $crate::typing::SchemeBytecode::Con($crate::typing::Constructor::$con).encode() ]
        )
    };
    (@emit [$($arg:tt)*] -> $ret:tt) => {
        $crate::typing::scheme!(@emit (Func [$($arg)*] $ret))
    };
    (@emit [$first:tt $($rest:tt)*]) => {
        $crate::typing::scheme!(@emit (Pair $first [$($rest)*]))
    };
    (@emit []) => {
        [ $crate::typing::SchemeBytecode::Con($crate::typing::Constructor::Unit).encode() ]
    };
    (@emit $generic:ident) => {
        [ $crate::typing::SchemeBytecode::Gen($generic).encode() ]
    };
    ( $( $generic:ident $(.$bound:ident)? )* : $($type:tt)* ) => {{
        $crate::typing::scheme!(@generics 0; $($generic)*);
        const BYTECODE: &[u8] = &$crate::concat::concat_slices!(
            u8;
            &[ 0 $(+ {const $generic: u8 = 1; $generic})* ],
            $(
                $(
                    &[
                        $crate::typing::SchemeBytecode::Gen($generic).encode(),
                        $crate::typing::SchemeBytecode::$bound.encode()
                    ],
                )?
            )*
            &$crate::typing::scheme!(@emit $($type)*)
        );
        unsafe {
            core::mem::transmute::<&[u8], &$crate::typing::Scheme>(BYTECODE)
        }
    }};
}

pub(crate) use scheme;

#[repr(transparent)]
pub struct Scheme([u8]);

impl Scheme {

    pub fn num_generics(&self) -> u8 {
        self.0[0]
    }

    pub fn bytecode(&self) -> &[u8] {
        &self.0[1..]
    }

}
