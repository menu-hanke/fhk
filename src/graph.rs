//! Graph and AST representation.

use enumset::EnumSetType;
use hashbrown::HashTable;

use crate::compile::{Ccx, SeqRef};
use crate::index::{index, IndexOption, IndexVec};
use crate::lang;
use crate::lang::LangMap;

index!(pub struct ObjRef(u32) invalid(!0));

impl ObjRef {
    // ORDER OBJ
    pub const NIL: Self = Self(0);
    pub const FALSE: Self = Self(1);
    pub const TRUE: Self = Self(2);
    pub const GLOBAL: Self = Self(3+1);
}

macro_rules! define_ops {
    ($($name:ident;)*) => {

        #[derive(EnumSetType)]
        #[repr(u8)]
        pub enum Operator {
            $($name),*
        }

        impl Operator {
            pub const NAME: &'static str = concat!($(stringify!($name)),*);
            pub const NAME_OFS: &'static [u16] = {
                let mut ofs = 0;
                $( let $name = ofs; ofs += stringify!($name).len() as u16; )*
                &[$($name,)* ofs]
            };
            pub fn name(self) -> &'static str {
                &Self::NAME[Self::NAME_OFS[self as usize] as usize
                    ..Self::NAME_OFS[self as usize+1] as usize]
            }
            fn datasize(self) -> usize {
                todo!()
            }
        }

    };
}

define_ops! {

    // objects
    THDR;   // [BODY]
    TBODY;  // [(VALUE...)]
    VAR;    // [TAB]
    MOD;    // [TAB (OUT...)]
    OUT;    // [MOD VAR VALUE (SUBSET)]
    QUERY;  // [TAB VALUE]
    FHDR;   // [BODY]
    FBODY;  // [(VALUE...)]
    LABEL;  // [#REF]    (always names the following object)

    // constants
    NIL;    // []
    KBOOL;  // [#BOOL]
    KSTR;   // [#REF]
    KINT;   // [#NUM]
    KINT64; // [#REF]
    KFP64;  // [#REF]

    // binary operators. ORDER BINOP.
    OR;     // [LEFT RIGHT]
    AND;    // [LEFT RIGHT]
    ADD;    // [LEFT RIGHT]
    SUB;    // [LEFT RIGHT]
    MUL;    // [LEFT RIGHT]
    DIV;    // [LEFT RIGHT]
    POW;    // [LEFT RIGHT]
    EQ;     // [LEFT RIGHT]
    NE;     // [LEFT RIGHT]
    LT;     // [LEFT RIGHT]
    LE;     // [LEFT RIGHT]

    // unary operators.
    NOT;    // [VALUE]
    UNM;    // [VALUE]
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ObjMode {
    Data,
    Ref
}

#[derive(EnumSetType)]
#[repr(u8)]
pub enum Primitive {
    NIL,
    B1,
    I8, I16, I32, I64,
    U8, U16, U32, U64,
    F32, F64,
    STR
}

// dimension: 4
// irt: 4
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct Type(u8);

impl Type {

    pub const INFER: Self = Self(!0);

    pub fn new(pri: Primitive, dim: usize) -> Self {
        todo!()
    }

    pub fn scalar(pri: Primitive) -> Self {
        Self::new(pri, 0)
    }

    pub fn unpack(self) -> Option<(u8, Primitive)> {
        todo!()
    }

}

#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C,align(4))]
pub struct Obj {
    pub op: u8,
    pub ty: Type,
    pub n: u8,
    pub mark: u8, // must be last
}

impl Obj {

    pub fn operator(self) -> Operator {
        todo!()
    }

    pub fn size(self) -> usize {
        self.n as usize + self.operator().datasize()
    }

}

pub struct Graph {
    objs: IndexVec<ObjRef, u32>,
    labels: HashTable<ObjRef>,
    lang: LangMap<lang::GraphData>
}

impl Graph {

    // pub fn get(&self, name: SeqRef, ns: Operator) -> IndexOption<ObjRef> {
    //     todo!()
    // }

    pub fn tab(&mut self, name: SeqRef) -> ObjRef {
        todo!()
    }

    pub fn var(&mut self, table: ObjRef, name: SeqRef) -> ObjRef {
        todo!()
    }

    pub fn add(&mut self, op: Operator, ty: Type, data: bool, args: &[u32]) -> ObjRef {
        let obj = self.objs.push(zerocopy::transmute!(Obj::new(op, ty, data as _, args.len() as _)));
        self.objs.raw.extend_from_slice(args);
        obj
    }

    pub fn addv(&mut self, op: Operator, ty: Type, args: &[ObjRef]) -> ObjRef {
        self.add(
            op,
            ty,
            false,
            unsafe { core::slice::from_raw_parts(args.as_ptr().cast(), args.len()) }
        )
    }

    pub fn addk(&mut self, op: Operator, ty: Type, data: u32) -> ObjRef {
        self.add(op, ty, true, &[data])
    }

    pub fn get_obj(&self, idx: ObjRef) -> Obj {
        zerocopy::transmute!(self.objs[idx])
    }

    pub fn get_input(&self, idx: ObjRef) -> ObjRef {
        zerocopy::transmute!(self.objs[idx])
    }

    pub fn inputs(&self, o: ObjRef) -> &[ObjRef] {
        todo!()
    }

    pub fn pairs(&self) -> impl Iterator<Item=(ObjRef,Obj)> {
        todo!()
    }

    pub fn pairs_mut(&mut self) -> impl Iterator<Item=(ObjRef, &mut Obj)> {
        todo!()
    }

}

impl core::ops::Index<ObjRef> for Graph {
    type Output = u32;
    fn index(&self, index: ObjRef) -> &u32 {
        &self.objs[index]
    }
}

impl core::ops::IndexMut<ObjRef> for Graph {
    fn index_mut(&mut self, index: ObjRef) -> &mut u32 {
        &mut self.objs[index]
    }
}

impl Default for Graph {

    fn default() -> Self {
        let mut graph = Graph {
            objs: Default::default(),
            labels: Default::default(),
            lang: Default::default()
        };
        // ORDER OBJ
        graph.addk(Operator::NIL, Type::scalar(Primitive::NIL), 0);
        graph.addk(Operator::KBOOL, Type::scalar(Primitive::B1), 0);
        graph.addk(Operator::KBOOL, Type::scalar(Primitive::B1), 1);
        graph.addv(Operator::LIST, Type::scalar(Primitive::NIL), &[]);
        graph.add(
            Operator::TAB,
            Type::scalar(Primitive::NIL),
            true,
            &[zerocopy::transmute!(Ccx::SEQ_GLOBAL), zerocopy::transmute!(ObjRef::GLOBAL-1)]
        );
        graph
    }

}
