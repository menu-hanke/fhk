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
            &[F64, F32, I64, I32, I16, I8, I64, I32, I16, I8, B1]
        };
        PRI2IR[self as usize]
    }

    pub fn is_unsigned(self) -> bool {
        use Primitive::*;
        (U8|U16|U32|U64).contains(self)
    }

}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Constructor {
    Tensor, // (T N)
    Tuple,  // (T U V ...)
    Splat,  // (T)
    Func,   // (R P1 ... PN)
    //Var,    // (V T)
    Tab     // (N M P ...)
}

impl Constructor {
    pub const TENSOR: u8 = Self::Tensor as _;
}

/*
 * first byte: number of generic arguments
 * rest: instantiation bytecode
 *
 *        byte 1             byte 2        stack        comment
 * +--------+-----------+ +----------+
 * |  7..6  |    5..0   | |   7..0   |
 * +========+===========+ +==========+
 * | BC_PRI | high bits | | low bits |     [-1]         apply pri constraint
 * | BC_CON |    con    | | num args |     [-n, +1]     apply constructor
 * | BC_GEN |    idx    | +----------+     [+1]         push generic
 * +--------+-----------+
 */
#[repr(transparent)]
pub struct Scheme([u8]);

impl Scheme {

    pub const BC_PRI: u8 = 0;
    pub const BC_CON: u8 = 1;
    pub const BC_GEN: u8 = 2;

    pub const DATA_BITS: usize = 6;

    // TODO: just replace this with a BC_NEW [n], that inits the generics
    pub fn num_generics(&self) -> u8 {
        self.0[0]
    }

    pub fn bytecode(&self) -> &[u8] {
        &self.0[1..]
    }
}

macro_rules! scheme {
    (@ignore $v:expr; $($_:tt)*) => { $v };
    (@defgenerics ($value:expr) $name:ident $($rest:ident)*) => {
        const $name: u8 = ($crate::typing::Scheme::BC_GEN << $crate::typing::Scheme::DATA_BITS)
            | $value;
        $crate::typing::scheme!(@defgenerics ($value+1) $($rest)*);
    };
    (@defgenerics ($_:expr)) => {};
    (
        @munch ($($buf:tt)*)
        @emit $v:expr; $($tail:tt)*
    ) => {
        $crate::typing::scheme!(@munch ($($buf)*, $v) $($tail)*)
    };
    (
        @munch ($($buf:tt)*)
        @pri $name:ident : {$($bound:ident)|*}; $($tail:tt)*
    ) => {
        $crate::typing::scheme!(@munch (
                $($buf)*,
                $name,
                // NOTE: BC_PRI = 0
                (($((1u16<<($crate::typing::Primitive::$bound as u8)))|*)>>8) as u8,
                ($((1u16<<($crate::typing::Primitive::$bound as u8)))|*) as u8
            )
            $($tail)*
        )
    };
    (
        @munch ($($buf:tt)*)
        @pri $name:ident : $bound:expr; $($tail:tt)*
    ) => {
        $crate::typing::scheme!(@munch (
                $($buf)*,
                $name,
                // NOTE: BC_PRI = 0
                ($bound>>8) as u8,
                $bound as u8
            )
            $($tail)*
        )
    };
    (
        @munch ($($buf:tt)*)
        $opcode:ident $($tail:tt)*
    ) => {
        $crate::typing::scheme!(@munch ($($buf)*, $opcode as u8) $($tail)*)
    };
    (
        @munch ($($buf:tt)*)
        ($constructor:ident $($args:tt)*) $($tail:tt)*
    ) => {
        $crate::typing::scheme!(@munch ($($buf)*)
            $($args)*
            @emit (($crate::typing::Scheme::BC_CON << $crate::typing::Scheme::DATA_BITS)
                | ($crate::typing::Constructor::$constructor as u8));
            @emit (0u8 $(+$crate::typing::scheme!(@ignore 1u8; $args))*);
            $($tail)*
        )
    };
    (@munch ($($buf:tt)*)) => {
        [$($buf)*]
    };
    (($($generic:ident $(:$bound:tt)?),*) : $($signature:tt)*) => {
        {
            $crate::typing::scheme!(@defgenerics (0u8) $($generic)*);
            const SCHEME: &'static [u8] = &$crate::typing::scheme![
                @munch
                (0u8 $(+$crate::typing::scheme!(@ignore 1u8; $generic))*)
                $($(@pri $generic :$bound;)?)*
                $($signature)*
            ];
            const SCHEME_: &'static $crate::typing::Scheme = unsafe { core::mem::transmute(SCHEME) };
            SCHEME_
        }
    }
}

pub(crate) use scheme;
