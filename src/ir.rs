//! Intermediate representation.

use core::marker::PhantomData;
use core::mem::transmute;
use core::ops::Range;
use core::slice;
use enumset::{EnumSet, EnumSetType};

use crate::bump::BumpRef;
use crate::foreach_lang;
use crate::index::{index, IndexValueVec, IndexVec, InvalidValue};
use crate::lang::Lang;
use crate::mcode::MCodeData;
use crate::mem::{Offset, ResetId, ResetSet, SizeClass, Slot};
use crate::obj::{ObjRef, QUERY};
use crate::support::DynSlot;

index!(pub struct FuncId(u16) invalid(!0) debug("f{}"));
index!(pub struct InsId(u16)  invalid(!0) debug("{:04}"));
index!(pub struct PhiId(u16)  invalid(!0) debug("ϕ{}"));

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
        $name:ident: $type:ty;
    )*) => {

        #[derive(EnumSetType)]
        pub enum Operand {
            $($name),*
        }

        mod mode_type {
            use super::*;
            $(pub type $name = $type;)*
        }

    };
}

define_operands! {
    V:  InsId;  // value
    C:  InsId;  // control
    P:  PhiId;  // phi
    F:  FuncId; // function
    L:  LangOp; // language-specific opcode
    X:  u16;    // 16-bit literal
    XX: u32;    // 32-bit literal
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
    TRET.FX   V F;                // args func
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
    CONV      V X;

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
        (JMP|GOTO|IF|RET|TRET|UB|ABORT).contains(self)
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
 * |   C    |    B   |    A   |  type  |  mark | opcode |
 * +--------+--------+--------+--------+-------+--------+
 *
 * NOTE: do not derive FromBytes. opcode and type must always be valid.
 */
#[derive(Clone, Copy, PartialEq, Eq, Hash, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct Ins(u64);

#[derive(EnumSetType)]
#[enumset(repr="u64")]
pub enum Mark {
    Mark1 = 8,
    Mark2 = 9,
    Mark3 = 10,
    Mark4 = 11
}

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

    pub fn get_mark(self, mark: impl Into<EnumSet<Mark>>) -> EnumSet<Mark> {
        unsafe { EnumSet::from_repr_unchecked(self.0 & mark.into().as_repr()) }
    }

    pub fn is_marked(self, mark: impl Into<EnumSet<Mark>>) -> bool {
        !self.get_mark(mark).is_empty()
    }

    pub fn set_mark(mut self, mark: impl Into<EnumSet<Mark>>) -> Self {
        self.0 |= mark.into().as_repr();
        self
    }

    pub fn clear_mark(mut self, mark: impl Into<EnumSet<Mark>>) -> Self {
        self.0 &= !mark.into().as_repr();
        self
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

    // pub fn func_mut(&mut self) -> Option<&mut FuncId> {
    //     use Opcode::*;
    //     match self.opcode() {
    //         CALLC|CALLCI => Some(zerocopy::transmute_mut!(&mut self.abc_mut()[2])),
    //         CINIT => Some(zerocopy::transmute_mut!(&mut self.abc_mut()[1])),
    //         CALL|TRET => { todo!(); /* TODO: nothing produces these yet. */ },
    //         _ => None
    //     }
    // }

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

}

/* ---- IR ------------------------------------------------------------------ */

pub struct Chunk {
    pub scl: SizeClass,
    pub check: Slot,
    pub slots: BumpRef<Slot>, // slot info in ccx.bump, one for each ret phi
    pub dynslots: MCodeData<DynSlot>
}

pub struct Query {
    pub obj: ObjRef<QUERY>,
    pub offsets: BumpRef<Offset> // return offsets in ccx.bump, one for each ret phi
}

#[derive(Clone, Copy)]
pub struct Phi {
    pub type_: Type
}

pub type Code = IndexValueVec<InsId, Ins>;

pub enum FuncKind {
    User(/*TODO*/),
    Query(Query),
    Chunk(Chunk)
}

pub struct Func {
    pub code: Code,
    pub entry: InsId,
    pub ret: PhiId, // one past last return value
    pub arg: PhiId, // one past last argument
    pub phis: IndexValueVec<PhiId, Phi>,
    pub kind: FuncKind,
    pub reset: ResetSet,
}

#[derive(Default)]
pub struct IR {
    pub funcs: IndexVec<FuncId, Func>,
}

impl IR {

    pub fn compact(&mut self) {
        todo!()
    }

}

impl Phi {

    pub fn new(type_: Type) -> Self {
        Self { type_ }
    }

}

impl Func {

    pub fn new(kind: FuncKind) -> Self {
        Self {
            kind,
            entry: InsId::INVALID.into(),
            code: Default::default(),
            phis: Default::default(),
            ret: 0.into(),
            arg: 0.into(),
            reset: ResetSet::default() | ResetId::GLOBAL,
        }
    }

    pub fn build_signature(&mut self) -> SignatureBuilder<'_, Returns> {
        debug_assert!(self.phis.is_empty());
        SignatureBuilder { func: self, _marker: PhantomData }
    }

    pub fn returns(&self) -> Range<PhiId> {
        0.into() .. self.ret
    }

    pub fn params(&self) -> Range<PhiId> {
        self.ret .. self.arg
    }

    fn clear_mark_(&self, marks: EnumSet<Mark>) {
        for (id,ins) in self.code.pairs() {
            self.code.set(id, ins.clear_mark(marks));
        }
    }

    pub fn clear_mark(&self, mark: impl Into<EnumSet<Mark>>) {
        self.clear_mark_(mark.into());
    }

}

impl Chunk {

    pub fn new(scl: SizeClass) -> Self {
        Self {
            scl,
            check: Default::default(),
            slots: BumpRef::zero(),
            dynslots: BumpRef::zero()
        }
    }

}

impl Query {

    pub fn new(obj: ObjRef<QUERY>) -> Self {
        Self {
            obj,
            offsets: BumpRef::zero()
        }
    }

}

pub struct Returns;
pub struct Args;
pub struct SignatureBuilder<'a, State> {
    pub func: &'a mut Func,
    _marker: PhantomData<fn(&State)>
}

impl<'a> SignatureBuilder<'a, Returns> {

    pub fn add_return(self, ty: Type) -> Self {
        self.func.phis.push(Phi::new(ty));
        self
    }

    pub fn finish_returns(self) -> SignatureBuilder<'a, Args> {
        self.func.ret = self.func.phis.end();
        SignatureBuilder { func: self.func, _marker: PhantomData }
    }

}

impl<'a> SignatureBuilder<'a, Args> {

    pub fn add_arg(self, ty: Type) -> Self {
        self.func.phis.push(Phi::new(ty));
        self
    }

    pub fn finish_args(self) {
        self.func.arg = self.func.phis.end();
    }

}
