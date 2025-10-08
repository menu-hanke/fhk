//! Intermediate representation.

use core::fmt::Debug;
use core::mem::transmute;
use core::ops::Range;
use core::slice;
use enumset::{EnumSet, EnumSetType};

use crate::bitmap::BitmapWord;
use crate::foreach_lang;
use crate::index::{index, IndexValueVec, IndexVec, InvalidValue};
use crate::intern::Interned;
use crate::lang::Lang;
use crate::mem::{ChunkId, ParamId, QueryId, ResetId, SizeClass};
use crate::obj::ObjRef;

index!(pub struct FuncId(u16)  invalid(!0) debug("f{}"));
index!(pub struct InsId(u16)   invalid(!0) debug("{:04}"));
index!(pub struct PhiId(u16)   invalid(!0) debug("ϕ{}"));

/* ---- Types --------------------------------------------------------------- */

macro_rules! define_types {
    ($(
        $name:ident $size:literal;
    )*) => {

        #[derive(EnumSetType)]
        #[repr(u8)]
        pub enum Type {
            $($name),*
        }

        impl Type {

            pub const NAME: &'static str = concat!($(stringify!($name)),*);
            pub const NAME_OFS: &'static [u8] = {
                let mut ofs = 0;
                $( let $name = ofs; ofs += stringify!($name).len() as u8; )*
                &[$($name,)* ofs]
            };

            pub fn size(self) -> usize {
                // 4 bits per variant (fits at most 16 types)
                let magic = $( (($size as u64) << (4 * Type::$name as usize)) )|*;
                ((magic >> (4 * self as usize)) & 0xf) as usize
            }

        }

    };
}

// tl;dr of type semantics:
//   * i8, i16, i32, i64, f32, f64 are exactly what you'd expect. in particular they are just dumb
//     values and any instruction taking one of these must *not* care about where the value came
//     from, eg. it's always correct to replace an instruction producing one of these with
//     a MOV, or any other instruction sequence that produces the same value.
//   * b1 is also a dumb value, but it has funny semantics when stored to memory. sometimes (eg.
//     chunk bitmaps) it's stored as a 1-bit value with a mask, colocated with other b1's.
//     in a register it's just a normal int. zero=false, any nonzero=true.
//   * fx is also a dumb value. however, it has no machine representation, it just represent that
//     "something happened". but because it's a dumb value, it can be replaced with any other
//     instruction sequence that makes the same thing happen. eg. STORE -> LOAD can be replaced
//     with STORE -> MOVF -> LOAD. any instruction using an FX value must *not* care about the
//     instruction sequence that produced the FX value. (but it of course can assume that whatever
//     "something happens" represented by the FX value has happened).
//   * lsv is the only type that is *not* a dumb value. it's *not* ok to replace lsv instruction
//     sequences with eg. MOVs. the instruction consuming an lsv value *can* look at the
//     instruction sequence that produced the lsv. however, lsv instructions, like any other
//     instructions, are still subject to dce and cse. lsv is intended for embedding
//     language-specific data into the IR, eg. call argument structure for scripting languages.
//     lsv instructions are not compiled by the clif translator. their interpretation is left
//     up to the language-specific instructions. however, they are scheduled like any other
//     instruction. lsv-producing generic instructions (eg. arithmetic) are subject to normal
//     fold rules. language-specific instructions (LO*) are not subject to any fold rules.
define_types! {
    FX   0;  // side effect
    LSV  0;  // language-specific value
    PTR  8;
    I8   1;
    I16  2;
    I32  4;
    I64  8;
    F32  4;
    F64  8;
    B1   1;
}

impl Type {

    pub fn name(self) -> &'static str {
        &Self::NAME[Self::NAME_OFS[self as usize] as usize
            ..Self::NAME_OFS[self as usize+1] as usize]
    }

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

    pub fn is_fp(self) -> bool {
        use Type::*;
        (F32|F64).contains(self)
    }

    pub fn is_int(self) -> bool {
        use Type::*;
        (I8|I16|I32|I64).contains(self)
    }

}

#[derive(Clone, Copy)]
pub enum Conv {
    Signed,
    Unsigned
}

impl Conv {

    pub const SIGNED: u16 = Self::Signed as _;
    pub const UNSIGNED: u16 = Self::Unsigned as _;

    pub fn from_u16(raw: u16) -> Self {
        if raw == Self::SIGNED {
            Self::Signed
        } else {
            Self::Unsigned
        }
    }

}

/* ---- Opcodes ------------------------------------------------------------- */

#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
pub struct LangOp {
    pub lang: u8,
    pub op: u8
}

impl LangOp {

    // XXX: consider making op an enum as well and have it be an associated type in trait Language.
    // this makes it easy to have op names for debug dumps.
    pub fn new(lang: Lang, op: u8) -> Self {
        Self { lang: lang as _, op }
    }

}

impl Debug for LangOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // TODO: also put opname here (add an opname() in trait language?)
        write!(f, " {}.{}", Lang::from_u8(self.lang).name(), self.op)
    }
}

macro_rules! langop_constructor {
    ( $($(#[$($meta:tt)*])? $module:ident::$name:ident;)* ) => {
        impl LangOp {
            $(
                $(#[$($meta)*])?
                pub fn $name(op: u8) -> Self {
                    Self::new($crate::lang::Lang::$name, op)
                }
            )*
        }
    };
}

foreach_lang!(langop_constructor);

macro_rules! define_operands {
    ($(
        $name:ident: $type:ty $(,$debugprefix:literal)? $(,$debugsign:ty)?;
    )*) => {

        #[derive(EnumSetType)]
        pub enum Operand {
            $($name),*
        }

        #[derive(Clone, Copy)]
        pub enum OperandData {
            $($name($type)),*
        }

        mod mode_type {
            use super::*;
            $(pub type $name = $type;)*
        }

        impl Ins {
            pub fn operands(&self) -> impl Iterator<Item=OperandData> + '_ {
                let raw = self.0;
                self.opcode().operands().iter().enumerate().map(move |(i,&o)| {
                    let raw = if o == Operand::XX { raw>>32 } else { raw>>(16*(i+1)) };
                    match o {
                        $(Operand::$name => {
                            let value: [$type; size_of::<Ins>()/size_of::<$type>()]
                                = zerocopy::transmute!(raw);
                            OperandData::$name(value[0])
                        }),*
                    }
                })
            }
        }

        impl Debug for OperandData {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                match *self {
                    $(OperandData::$name(v) => {
                        $( write!(f, $debugprefix)?; )?
                        $( let v = v as $debugsign; )?
                        v.fmt(f)
                    }),*
                }
            }
        }

    };
}

define_operands! {
    V:  InsId;          // value
    C:  InsId,  "->";   // control
    P:  PhiId;          // phi
    F:  FuncId;         // function
    Q:  ParamId;        // query parameter
    L:  LangOp;         // language-specific opcode
    X:  u16,    i16;    // 16-bit literal
    XX: u32,    i32;    // 32-bit literal
}

macro_rules! encode_at {
    ($value:expr, $_:expr, $(XX)*) => {{
        let v: u32 = zerocopy::transmute!($value);
        (v as u64) << 32
    }};
    ($value:expr, $offset:expr, $_:ident) => {{
        let v: u16 = zerocopy::transmute!($value);
        (v as u64) << $offset
    }};
}

macro_rules! decode_at {
    ($ins:expr, $_:ident, $(XX)*) => { zerocopy::transmute!($ins.bc()) };
    ($ins:expr, $field:ident, $_:ident) => { zerocopy::transmute!($ins.$field()) };
}

macro_rules! decode_fn {
    ($vis:vis fn -> $($rest:tt)*) => { /* workaround for nested repetition in define_opcodes */ };
    ($vis:vis fn $name:ident $($check:ident)? -> $($field:ident=$mode:ident)*) => {
        #[allow(unused_parens)]
        $vis fn $name(self) -> ( $(mode_type::$mode),* ) {
            $( debug_assert!(self.opcode() == Opcode::$check); )?
            ( $(decode_at!(self, $field, $mode)),* )
        }
    };
    ($vis:vis fn $name:ident $($check:ident)? -> $($a:ident $($b:ident $($c:ident)?)?)?) => {
        decode_fn!($vis fn $name $($check)? -> $(a=$a $(b=$b $(c=$c)?)?)?);
    };
}

macro_rules! define_opcodes {
    (@set $ins:expr, $set:ident $_:ident $v:expr) => { $ins.$set($v) };
    (
        @new $name:ident
        ($($typearg:ident)?; $($_:tt)*) ($typeval:expr; $($__:tt)*)
        $($mode1:ident $($mode2:ident $($mode3:ident)?)?)?
    ) => {
        pub const fn $name(
            $($typearg: Type,)?
            $( v1: mode_type::$mode1, $( v2: mode_type::$mode2, $( v3: mode_type::$mode3, )?)?)?
        ) -> Ins {
            #[allow(unused_mut)]
            let mut ins = Ins::new(Opcode::$name, $typeval);
            $( ins.0 |= encode_at!(v1, 16, $mode1);
            $( ins.0 |= encode_at!(v2, 32, $mode2);
            $( ins.0 |= encode_at!(v3, 48, $mode3);
            )?)?)?
            ins
        }
    };
    ($(
        $name:ident $(.$type:ident)?
        $($mode:ident)*
        $(, $decoder:ident)?
        ;
    )*) => {

        #[derive(EnumSetType)]
        #[repr(u8)]
        pub enum Opcode {
            $($name),*
        }

        impl Opcode {
            pub const NAME: &'static str = concat!($(stringify!($name)),*);
            pub const NAME_OFS: &'static [u16] = {
                let mut ofs = 0;
                $( let $name = ofs; ofs += stringify!($name).len() as u16; )*
                &[$($name,)* ofs]
            };
            const OPERANDS: &'static [Operand] = &[ $( $(Operand::$mode,)* )* ];
            const OPERANDS_OFS: &'static [u8] = {
                let mut ofs = 0;
                $( let $name = ofs; $(let $mode = 1; ofs += $mode; )* )*
                &[$($name,)* ofs]
            };
            const INPUTS_V: &'static [u8] = &[$(count_operands(Opcode::$name, Operand::V) as _),*];
            const INPUTS_C: &'static [u8] = &[$(count_operands(Opcode::$name, Operand::C) as _),*];
        }

        impl Ins {
            $(
                define_opcodes!(
                    @new $name
                    ( $(;$type)? type_; )
                    ( $(Type::$type;)? type_; )
                    $($mode)*
                );
                decode_fn!(pub fn $($decoder $name)? -> $($mode)*);
            )*
        }

    };
}

// NOTE:
// * value inputs (V) must be placed first
// * control inputs (C) must be placed right after value inputs
define_opcodes! {

    NOP;

/* -- Control instructions ---------- */

    JMP.FX    V C P, decode_JMP;  // value dest phi
    GOTO.FX   C,     decode_GOTO;
    IF.FX     V C C, decode_IF;   // cond tru fal
    RET.FX;
    UB.FX;
    ABORT.FX; // (add reason/message here if needed)

/* -- Data instructions --------------*/

    PHI       C P,   decode_PHI;  // control id

    KINT      XX;
    KINT64    XX;
    KFP64     XX;
    KSTR      XX;
    KREF.LSV  XX;

    MOV       V;
    MOVB      V;
    MOVF      V V;
    CMOV      V V V, decode_CMOV;      // cond tru fal
    CONV      V X,   decode_CONV;

    ADD       V V;
    SUB       V V;
    MUL       V V;
    DIV       V V;
    UDIV      V V;
    POW       V V;
    NEG       V;

    ADDP.PTR  V V;

    EQ.B1     V V;
    NE.B1     V V;
    LT.B1     V V;
    LE.B1     V V;
    ULT.B1    V V;
    ULE.B1    V V;

    ALLOC.PTR V V C;                   // size align control
    STORE.FX  V V;                     // ptr value
    LOAD      V;                       // ptr

    QLOAD     Q X,   decode_QLOAD;

    BOX.LSV   V;
    ABOX.LSV  C X X, decode_ABOX;      // control size align
    BREF.PTR  V;

    CALL.FX   V F,   decode_CALL;      // args func
    CALLC.FX  V V F;                   // idx fx chunk  (NOT inlineable)
    CALLCI.FX V V F;                   // idx fx chunk  (inlineable)
    CARG.LSV  V V,   decode_CARG;      // arg next
    RES       V P,   decode_RES;       // call phi

    CINIT.FX  V F,   decode_CINIT;     // size chunk

    LO;
    LOV       V L,   decode_LOV;
    LOVV      V V L, decode_LOVV;
    LOVX      V X L, decode_LOVX;
    LOX       L X,   decode_LOX;
    LOXX      L XX,  decode_LOXX;

}

impl Opcode {

    pub fn name(self) -> &'static str {
        &Self::NAME[Self::NAME_OFS[self as usize] as usize
            ..Self::NAME_OFS[self as usize+1] as usize]
    }

    pub fn operands(self) -> &'static [Operand] {
        &Self::OPERANDS[Self::OPERANDS_OFS[self as usize] as usize
            ..Self::OPERANDS_OFS[self as usize+1] as usize]
    }

    pub fn is_control(self) -> bool {
        use Opcode::*;
        (JMP|GOTO|IF|RET|UB|ABORT).contains(self)
    }

    pub fn is_data(self) -> bool {
        !self.is_control()
    }

    pub fn is_lang(self) -> bool {
        use Opcode::*;
        (LO|LOV|LOVV|LOVX|LOX|LOXX).contains(self)
    }

    pub fn is_pinned(self) -> bool {
        use Opcode::*;
        (PHI|ALLOC|ABOX).contains(self)
    }

    pub fn is_cse(self) -> bool {
        use Opcode::*;
        !(ALLOC|ABOX).contains(self)
    }

    pub fn is_const(self) -> bool {
        use Opcode::*;
        (KINT|KINT64|KFP64|KSTR|KREF).contains(self)
    }

    pub fn is_call(self) -> bool {
        use Opcode::*;
        (CALL|CALLC|CALLCI).contains(self)
    }

    pub fn num_v(self) -> usize {
        Self::INPUTS_V[self as usize] as _
    }

    pub fn num_c(self) -> usize {
        Self::INPUTS_C[self as usize] as _
    }

    pub fn num_vc(self) -> usize {
        self.num_v() + self.num_c()
    }

}

const fn count_operands(opcode: Opcode, opr: Operand) -> usize {
    let mut num = 0;
    let mut i = Opcode::OPERANDS_OFS[opcode as usize];
    let OPERANDS: &'static [u8] = unsafe {
        slice::from_raw_parts(Opcode::OPERANDS.as_ptr().cast(), Opcode::OPERANDS.len())
    };
    while i < Opcode::OPERANDS_OFS[opcode as usize + 1] {
        if OPERANDS[i as usize] == opr as u8 {
            num += 1;
        }
        i += 1;
    }
    num
}

/* ---- Instructions -------------------------------------------------------- */

/*
 * +--------+--------+--------+--------+-------+--------+
 * | 63..48 | 47..32 | 31..16 | 15..12 | 11..8 |  7..0  |
 * +--------+--------+--------+--------+-------+--------+
 * |   C    |    B   |    A   |  type  | ----- | opcode |
 * +--------+--------+--------+--------+-------+--------+
 *
 * NOTE: do not derive FromBytes. opcode and type must always be valid.
 */
#[derive(Clone, Copy, PartialEq, Eq, Hash, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct Ins(u64);

// everything here assumes little endian.
// note that archs in the set (supported by cranelift) ∩  (supported by luajit) are all LE.
// swap ABC and reimplement accessors if you ever want to run fhk on s390x with a non-lua host,
// I guess.
#[cfg(target_endian="little")]
impl Ins {

    pub const NOP_FX: Ins = Ins::NOP(Type::FX);

    pub const fn new(op: Opcode, ty: Type) -> Self {
        Self((op as u64) | ((ty as u64) << 12))
    }

    pub const fn opcode(self) -> Opcode {
        unsafe { transmute(self.0 as u8) }
    }

    pub const fn set_opcode(self, opcode: Opcode) -> Self {
        Self((self.0 & !0xff) | (opcode as u64))
    }

    pub const fn type_(self) -> Type {
        unsafe { transmute(((self.0 as u16) >> 12) as u8) }
    }

    pub const fn a(self) -> u16 {
        (self.0 >> 16) as _
    }

    pub const fn b(self) -> u16 {
        (self.0 >> 32) as _
    }

    pub const fn c(self) -> u16 {
        (self.0 >> 48) as _
    }

    pub const fn bc(self) -> u32 {
        (self.0 >> 32) as _
    }

    pub const fn set_a(self, a: u16) -> Self {
        Self((self.0 & 0xffffffff0000ffff) | ((a as u64) << 16))
    }

    pub const fn set_b(self, b: u16) -> Self {
        Self((self.0 & 0xffff0000ffffffff) | ((b as u64) << 32))
    }

    pub const fn set_c(self, c: u16) -> Self {
        Self((self.0 & 0x0000ffffffffffff) | ((c as u64) << 48))
    }

    pub const fn set_bc(self, bc: u32) -> Self {
        Self((self.0 & 0x00000000ffffffff) | ((bc as u64) << 32))
    }

    pub fn abc_mut(&mut self) -> &mut [u16; 3] {
        unsafe { &mut *(self as *mut Ins as *mut u16).add(1).cast() }
    }

    pub fn abc(&self) -> [u16; 3] {
        let mut this = *self;
        *this.abc_mut()
    }

    pub fn set_abc(mut self, abc: [u16; 3]) -> Self {
        *self.abc_mut() = abc;
        self
    }

    pub fn inputs(&self) -> &[InsId] {
        unsafe {
            slice::from_raw_parts(
                (self as *const Ins as *const InsId).add(1),
                self.opcode().num_v()
            )
        }
    }

    pub fn inputs_mut(&mut self) -> &mut [InsId] {
        unsafe {
            slice::from_raw_parts_mut(
                (self as *mut Ins as *mut InsId).add(1),
                self.opcode().num_v()
            )
        }
    }

    pub fn controls(&self) -> &[InsId] {
        let opcode = self.opcode();
        unsafe {
            slice::from_raw_parts(
                (self as *const Ins as *const InsId).add(1 + opcode.num_v()),
                opcode.num_c()
            )
        }
    }

    pub fn controls_mut(&mut self) -> &mut [InsId] {
        let opcode = self.opcode();
        unsafe {
            slice::from_raw_parts_mut(
                (self as *mut Ins as *mut InsId).add(1 + opcode.num_v()),
                opcode.num_c()
            )
        }
    }

    pub fn inputs_and_controls(&self) -> &[InsId] {
        unsafe {
            slice::from_raw_parts(
                (self as *const Ins as *const InsId).add(1),
                self.opcode().num_vc()
            )
        }
    }

    pub fn inputs_and_controls_mut(&mut self) -> &mut [InsId] {
        unsafe {
            slice::from_raw_parts_mut(
                (self as *mut Ins as *mut InsId).add(1),
                self.opcode().num_vc()
            )
        }
    }

    pub fn phi_mut(&mut self) -> Option<&mut PhiId> {
        use Opcode::*;
        match self.opcode() {
            JMP => Some(zerocopy::transmute_mut!(&mut self.abc_mut()[2])),
            PHI|RES => Some(zerocopy::transmute_mut!(&mut self.abc_mut()[1])),
            _ => None
        }
    }

    // same as controls()[0], but without the bound check
    // returns a garbage (but not uninitialized) value for non-C opcodes
    // note: this becomes unsound if a `V V V` opcode is added.
    pub fn decode_C(self) -> InsId {
        debug_assert!(self.opcode().num_c() > 0);
        let ofs = self.opcode().num_v();
        unsafe { *(&self as *const Ins as *const InsId).add(1+ofs) }
    }

    pub fn decode_F(self) -> FuncId {
        use Opcode::*;
        debug_assert!((CALL|CALLC|CALLCI|CINIT).contains(self.opcode()));
        let abc = self.abc();
        zerocopy::transmute!(abc[match self.opcode() { CALL|CINIT => 1, _ => 2 }])
    }

    // it's a bit ugly but oh well
    pub fn decode_L(self) -> LangOp {
        use Opcode::*;
        match self.opcode() {
            LOV => zerocopy::transmute!(self.b()),
            LOVV | LOVX => zerocopy::transmute!(self.c()),
            _ /* LO | LOX | LOXX */ => {
                debug_assert!((LO|LOX|LOXX).contains(self.opcode()));
                zerocopy::transmute!(self.a())
            }
        }
    }

    decode_fn!(pub fn decode_V -> V);
    decode_fn!(pub fn decode_VV -> V V);
    decode_fn!(pub fn decode_CALLC -> V V F); // CALLC and CALLCI

    pub fn decode__V(self) -> InsId {
        zerocopy::transmute!(self.b())
    }

}

impl Debug for Ins {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:-3} {:-6}", self.type_().name(), self.opcode().name())?;
        for op in self.operands() { write!(f, " {:?}", op)?; }
        Ok(())
    }
}

/* ---- Instruction matching ------------------------------------------------ */

// instruction matching mini-language:
//   `_`                   matches anything
//   `const`               matches constants
//   number                matches small integer constants (KINT)
//   (opcode [pattern]*)   matches instructions

macro_rules! value_matches {
    ($code:expr, $value:expr; _) => {
        true
    };
    ($code:expr, $value:expr; const) => {
        $code.raw[$value as usize].opcode().is_const()
    };
    ($code:expr, $value:expr; $kint:literal) => {
        {
            let ins = $code.raw[$value as usize];
            ins.opcode() == Opcode::KINT && $kint == ins.bc() as _
        }
    };
    ($code:expr, $value:expr; ($($t:tt)*)) => {
        {
            let ins = $code.raw[$value as usize];
            $crate::ir::ins_matches!($code, ins; $($t)*)
        }
    };
}

macro_rules! ins_matches {
    ($code:expr, $ins:expr; _ $a:tt $($b:tt $($c:tt)? )? ) => {
        $crate::ir::value_matches!($code, $ins.a(); $a)
            $( && $crate::ir::value_matches!($code, $ins.b(); $b)
                $( && $crate::ir::value_matches!($code, $ins.c(); $c) )?)?
    };
    ($code:expr, $ins:expr; $opcode:tt $( $a:tt $($rest:tt)* )? ) => {
        {
            #[allow(unused_imports)]
            use $crate::ir::Opcode::*;
            let opcode: enumset::EnumSet<$crate::ir::Opcode> = $opcode.into();
            opcode.contains($ins.opcode())
                $( && $crate::ir::ins_matches!($code, $ins; _ $a $($rest)*) )?
        }
    };
}

pub(crate) use {ins_matches, value_matches};

/* ---- IR ------------------------------------------------------------------ */

#[derive(Clone, Copy)]
pub struct Phi {
    pub type_: Type
}

#[derive(Clone, Copy)]
pub enum FuncKind {
    User,
    Query(QueryId),
    Chunk(ChunkId)
}

#[derive(EnumSetType)]
#[enumset(repr="u8")]
pub enum DebugFlag {
    INIT,
    VALUE
}

// +--------+-------+------+
// |  31..2 |   1   |   0  |
// +--------+-------+------+
// | objref | value | init |
// +--------+-------+------+
#[derive(Clone, Copy, Default)]
pub struct DebugSource(u32);

pub struct Func {
    pub code: IndexValueVec<InsId, Ins>,
    pub entry: InsId,
    pub ret: PhiId, // one past last return value
    pub arg: PhiId, // one past last argument
    pub phis: IndexValueVec<PhiId, Phi>,
    pub kind: FuncKind,
    pub scl: SizeClass,
    pub reset: Interned<[BitmapWord<ResetId>]>,
    pub source: DebugSource
}

#[derive(Default)]
pub struct IR {
    pub funcs: IndexVec<FuncId, Func>,
}

impl Phi {

    pub fn new(type_: Type) -> Self {
        Self { type_ }
    }

}

impl Func {

    fn new(kind: FuncKind, scl: SizeClass, source: DebugSource) -> Self {
        Self {
            kind,
            scl,
            source,
            code: Default::default(),
            entry: InsId::INVALID.into(),
            ret: 0.into(),
            arg: 0.into(),
            phis: Default::default(),
            reset: Interned::EMPTY
        }
    }

    pub fn user(source: DebugSource) -> Self {
        Self::new(FuncKind::User, SizeClass::GLOBAL, source)
    }

    pub fn query(id: QueryId, source: DebugSource) -> Self {
        Self::new(FuncKind::Query(id), SizeClass::GLOBAL, source)
    }

    pub fn chunk(scl: SizeClass, source: DebugSource) -> Self {
        // chunk id is allocated at layout time
        Self::new(FuncKind::Chunk(ChunkId::INVALID.into()), scl, source)
    }

    pub fn returns(&self) -> Range<PhiId> {
        0.into() .. self.ret
    }

    pub fn params(&self) -> Range<PhiId> {
        self.ret .. self.arg
    }

}

impl DebugSource {

    pub fn new<T: ?Sized>(obj: ObjRef<T>, flags: impl Into<EnumSet<DebugFlag>>) -> Self {
        let obj: u32 = zerocopy::transmute!(obj);
        Self((obj<<2) | flags.into().as_repr() as u32)
    }

    pub fn obj(self) -> ObjRef {
        zerocopy::transmute!(self.0>>2)
    }

    pub fn flags(self) -> EnumSet<DebugFlag> {
        unsafe { EnumSet::from_repr_unchecked((self.0 & 3) as _) }
    }

}
