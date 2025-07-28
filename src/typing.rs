//! Type system.

use enumset::EnumSetType;

use crate::ir::{self, Type};

macro_rules! define_primitives {
    ($($name:ident $lname:literal;)*) => {
        #[derive(EnumSetType, Debug)]
        #[repr(u8)]
        pub enum Primitive {
            $($name),*
        }
        impl Primitive {
            pub fn from_name(name: &[u8]) -> Option<Self> {
                match name {
                    $($lname => Some(Self::$name),)*
                    _ => None
                }
            }
        }
    };
}

// ORDER PRI
// numeric types first, in order of assignment preference
define_primitives! {
    F64 b"f64";
    F32 b"f32";
    I64 b"i64";
    I32 b"i32";
    I16 b"i16";
    I8  b"i8";
    U64 b"u64";
    U32 b"u32";
    U16 b"u16";
    U8  b"u8";
    B1  b"b1";
    PTR b"ptr";
    STR b"str";
}

impl Primitive {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub const fn to_ir(self) -> Type {
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

    pub fn size(self) -> usize {
        self.to_ir().size()
    }

}

#[derive(EnumSetType)]
pub enum Constructor {
    Tensor, // (elem dim)
    Pair,   // (left right)
    Func,   // (arg ret)
    Next,   // (prev)
    Unit,   // ()
    Never,  // !
}

impl Constructor {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn arity(self) -> u8 {
        use Constructor::*;
        match self {
            Tensor | Pair | Func => 2,
            Next => 1,
            Unit | Never => 0
        }
    }

}

// use signed int here so that -1 can be used as a dummy (and checked via "<0")
pub const PRI_IDX: Primitive = Primitive::I32;
pub const IRT_IDX: ir::Type = PRI_IDX.to_ir();

// for rust code dealing with indices coming from compiled code (note the sign difference)
pub type Idx = u32;
