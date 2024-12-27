//! Object definitions.

use core::fmt::Debug;
use core::hash::{Hash, Hasher};
use core::iter::zip;
use core::ops::{Index, IndexMut};
use core::slice;
use core::str;

use enumset::EnumSetType;
use hashbrown::hash_table::{Entry, VacantEntry};
use hashbrown::HashTable;
use zerocopy::Unalign;

use crate::bump::{self, Aligned, Bump, BumpRef};
use crate::compile::Ccx;
use crate::hash::fxhash;
use crate::intern::IRef;
use crate::mcode::MCodeOffset;
use crate::typing::Primitive;

// must have ALIGN=4
pub unsafe trait ObjType: Aligned {}

// layout must match macros below, and host
#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C,align(4))]
pub struct Obj {
    pub n: u8,
    pub op: u8,
    pub mark: u8,
    pub data: u8,
}

unsafe impl ObjType for Obj {}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
pub struct ObjRef<T:?Sized=Obj> { raw: BumpRef<T> }

impl<T: ?Sized> Clone for ObjRef<T> {
    fn clone(&self) -> Self {
        Self { raw: self.raw }
    }
}

impl<T: ?Sized> Copy for ObjRef<T> {}

impl<T: ?Sized> PartialEq for ObjRef<T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<T: ?Sized> Eq for ObjRef<T> {}

impl<T: ?Sized> Hash for ObjRef<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state)
    }
}

impl<T: ?Sized> Debug for ObjRef<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let raw: u32 = zerocopy::transmute!(*self);
        write!(f, "{:#>4}", raw)
    }
}

impl<T: ?Sized> ObjRef<T> {

    pub fn cast<U: ?Sized + ObjType>(self) -> ObjRef<U> {
        zerocopy::transmute!(self)
    }

    pub fn erase(self) -> ObjRef {
        self.cast()
    }

    pub fn is_nil(self) -> bool {
        self.erase() == ObjRef::NIL
    }

}

pub fn cast_args<T: ?Sized, U: ?Sized>(args: &[ObjRef<T>]) -> &[ObjRef<U>] {
    // hopefully one day zerocopy::transmute_ref can do this
    unsafe { slice::from_raw_parts(args.as_ptr().cast(), args.len()) }
}

pub fn cast_args_raw<T: ?Sized>(args: &[u32]) -> &[ObjRef<T>] {
    // same as above
    unsafe { slice::from_raw_parts(args.as_ptr().cast(), args.len()) }
}

#[derive(EnumSetType)]
#[repr(u8)]
pub enum FieldType {
    // ORDER FIELDTYPE
    Spec,
    Lit,
    Ref,
    Name,
    VLit,
    VRef
}

#[repr(transparent)]
pub struct OpFields([u8]);

impl<'a> IntoIterator for &'a OpFields {
    type Item = (FieldType, &'a str);
    type IntoIter = OpFieldIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        OpFieldIter(&self.0)
    }
}

pub struct OpFieldIter<'a>(&'a [u8]);

impl<'a> Iterator for OpFieldIter<'a> {
    type Item = (FieldType, &'a str);
    fn next(&mut self) -> Option<Self::Item> {
        let desc = *self.0.get(0)?;
        // safety: opfields is only created by define_ops
        let fty = unsafe { core::mem::transmute(desc & 0x7) };
        let len = desc as usize >> 3;
        let name = unsafe { str::from_utf8_unchecked(&self.0[1..len+1]) };
        self.0 = &self.0[len+1..];
        Some((fty, name))
    }
}

// for define_ops macro:
type Name = IRef<[u8]>;

macro_rules! define_ops {
    (@meta ($($buf:expr,)*) ) => { crate::concat::concat_slices!(u8; $($buf),*) };
    (@meta ($($buf:expr,)*) , $($rest:tt)*) => {
        define_ops!(@meta ($($buf,)*) $($rest)*)
    };
    (@meta ($($buf:expr,)*) @skip $name:ident : $type:ty, $($rest:tt)*) => {
        define_ops!(@meta ($($buf,)*) $($rest)*)
    };
    (@meta ($($buf:expr,)*) @emit $fty:ident $name:ident $($rest:tt)*) => {
        define_ops!(@meta (
                $($buf,)*
                &[(FieldType::$fty as u8) | ((stringify!($name).len() as u8) << 3)],
                stringify!($name).as_bytes(),
        ) $($rest)*)
    };
    (@meta ($($buf:expr,)*) .$spec:ident $($rest:tt)*) => {
        define_ops!(@meta ($($buf,)*) @emit Spec $spec $($rest)*)
    };
    (@meta ($($buf:expr,)*) $name:ident : ObjRef $($rest:tt)*) => {
        define_ops!(@meta ($($buf,)*) @emit Ref $name @skip $name : ObjRef $($rest)*)
    };
    (@meta ($($buf:expr,)*) $name:ident : Name $($rest:tt)*) => {
        define_ops!(@meta ($($buf,)*) @emit Name $name @skip $name : Name $($rest)*)
    };
    (@meta ($($buf:expr,)*) $name:ident : $type:ty, $($rest:tt)*) => {
        define_ops!(@meta ($($buf,)*) @emit Lit $name $($rest)*)
    };
    (@meta ($($buf:expr,)*) $name:ident : [ObjRef $($_:tt)*]) => {
        define_ops!(@meta ($($buf,)*) @emit VRef $name)
    };
    (@meta ($($buf:expr,)*) $name:ident : [$type:ty]) => {
        define_ops!(@meta ($($buf,)*) @emit VLit $name)
    };
    (
        @new $name:ident
        ($($def:ident=$defval:expr;)* @stop $($_:tt)*)
        $(,)* $($field:ident:$ty:ty $(,)+)*
    ) => {
        #[allow(dead_code)]
        pub fn new($($field:$ty),*) -> Self {
            $name { $($def:$defval,)* $($field,)* }
        }
    };
    (@struct ($name:ident $($field:ident:$ty:ty),*;) ($data:ident $($_:tt)*)) => {
        // layout must match struct Obj
        #[allow(dead_code)]
        #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
        #[repr(C,align(4))]
        pub struct $name {
            pub n: u8,
            pub op: u8,
            pub mark: u8,
            pub $data: u8,
            $(pub $field : $ty,)*
        }
        unsafe impl ObjType for $name {}
    };
    (@struct ($name:ident $($field:ident:$ty:ty),*; $vla:ident:$vty:ty) ($data:ident $($_:tt)*)) => {
        // layout must match struct Obj
        bump::vla_struct! {
            #[allow(dead_code)]
            #[repr(align(4))]
            pub struct $name {
                pub n: u8,
                pub op: u8,
                pub mark: u8,
                pub $data: u8,
                $(pub $field : $ty,)*
            } pub $vla: [$vty; |x| x.n as usize - $name::FIXARGS]
        }
        impl $name {
            // note: includes the obj itself, too
            const FIXARGS: usize = size_of::<$name<[$vty; 0]>>()/size_of::<u32>();
        }
        unsafe impl<const K: usize> ObjType for $name<[$vty; K]> {}
        unsafe impl ObjType for $name {}
    };
    (
        $(
            $operator:ident
            $(.$data:ident)?
            { $($fields:tt)* } $($vla:ident : [$($vty:tt)*])?
            ;
        )*
    ) => {
        #[derive(EnumSetType)]
        #[repr(u8)]
        pub enum Operator { $($operator),* }
        impl Obj {
            $(pub const $operator: u8 = Operator::$operator as _;)*
        }
        impl Operator {
            pub const NAME: &'static str = concat!($(stringify!($operator)),*);
            pub const NAME_OFS: &'static [u16] = {
                let mut ofs = 0;
                $( let $operator = ofs; ofs += stringify!($operator).len() as u16; )*
                &[$($operator,)* ofs]
            };
            pub const FIELDS: (&'static [u8], &'static [u16]) = {
                $(
                    const $operator: &[u8] = &define_ops!(@meta () $(.$data)? $($fields)*, $($vla:[$($vty)*])?);
                )*
                const DESC: &'static [u8] = &$crate::concat::concat_slices!(u8; $($operator),*);
                const OFS: &'static [u16] = &{
                    let mut ofs = [$($operator.len() as u16,)* 0];
                    let mut i = 0;
                    let mut cursor = 0;
                    while i < ofs.len() {
                        let n = ofs[i];
                        ofs[i] = cursor;
                        cursor += n;
                        i += 1;
                    }
                    ofs
                };
                (DESC, OFS)
            };
        }
        $(
            define_ops!(@struct ($operator $($fields)*; $($vla:$($vty)*)?) ($($data)? data));
            impl $operator $(<[$($vty)*; 0]>)? {
                define_ops!(
                    @new $operator
                    (op=Operator::$operator as _; n=0; mark=0; $($vla=[];)? $(@stop $data)? data=0; @stop)
                    $($data:u8,)?
                    $($fields)*,
                );
            }
        )*
        #[allow(dead_code)]
        #[derive(Clone, Copy)]
        #[repr(C,u8)]
        pub enum ObjectRef<'a> {
            $($operator(&'a $operator)),*
        }
        impl Objects {
            pub fn get(&self, idx: ObjRef) -> ObjectRef {
                match self.bump[idx.raw].operator() {
                    $( Operator::$operator => ObjectRef::$operator(&self.bump[idx.raw.cast()]) ),*
                }
            }
        }
    };
}

// note: all fields here must be 4 byte POD types.
define_ops! {
    // named objects. name must be first. tab must be second for VAR and MOD.
    // ORDER NAMEDOBJ
    VAR         { name: Name, tab: ObjRef<TAB>, ann: ObjRef/*TY*/};
    MOD         { name: Name, tab: ObjRef<TAB>, guard: ObjRef<EXPR> } value: [ObjRef<VSET>];
    TAB         { name: Name, shape: ObjRef<TUPLE> };
    FUNC        { name: Name, value: ObjRef<EXPR> };
    // non-named objects.
    QUERY       { tab: ObjRef<TAB>, mcode: MCodeOffset } value: [ObjRef<EXPR>];
    RESET.id    { mlo: u32, mhi: u32 } objs: [ObjRef/*VAR|MOD*/];
    FNI         { func: ObjRef<FUNC> } generics: [ObjRef/*TY*/];
    VSET.flat   { var: ObjRef<VAR>, value: ObjRef<EXPR> } idx: [ObjRef<EXPR>];
    // types
    TVAR        {};
    TPRI.ty     {};
    TTEN.dim    { elem: ObjRef/*TY*/ };
    TTUP        {} elems: [ObjRef/*TY*/];
    // (TFUNC for functions + generic type annotations TPAR/TCON etc)
    // expressions. ann must be first.
    NIL         { ann: ObjRef<TTUP> };
    SPLAT       { ann: ObjRef/*TY*/, value: ObjRef<EXPR> };
    KINT        { ann: ObjRef/*TY*/, k: i32 };
    KINT64      { ann: ObjRef/*TY*/, k: BumpRef<Unalign<i64>> };
    KFP64       { ann: ObjRef/*TY*/, k: BumpRef<Unalign<f64>> };
    KSTR        { ann: ObjRef/*TY*/, k: IRef<[u8]> };
    DIM.axis    { ann: ObjRef/*TPRI.IDX*/ };
    LEN.axis    { ann: ObjRef/*TPRI.IDX*/, value: ObjRef<EXPR> };
    TUPLE       { ann: ObjRef/*TY*/ } fields: [ObjRef<EXPR>];
    VGET.flat   { ann: ObjRef/*TY*/, var: ObjRef<VAR> } idx: [ObjRef<EXPR>];
    CAT         { ann: ObjRef/*TY*/ } elems: [ObjRef<EXPR>];
    IDX         { ann: ObjRef/*TY*/, value: ObjRef<EXPR> } idx: [ObjRef<EXPR>];
    BINOP.binop { ann: ObjRef/*TY*/, left: ObjRef<EXPR>, right: ObjRef<EXPR> };
    INTR.func   { ann: ObjRef/*TY*/ } args: [ObjRef<EXPR>];
    LOAD        { ann: ObjRef/*TY*/, addr: ObjRef<EXPR> } shape: [ObjRef<EXPR>];
    NEW         { ann: ObjRef/*TY*/ } shape: [ObjRef<EXPR>];
    GET.idx     { ann: ObjRef/*TY*/, value: ObjRef<EXPR> };
    FREF        { ann: ObjRef/*TY*/, func: ObjRef/*FUNC|FNI*/ };
    CALL        { ann: ObjRef/*TY*/, func: ObjRef<EXPR> } args: [ObjRef<EXPR>];
    CALLX.lang  { ann: ObjRef/*TY*/, func: u32 } inputs: [ObjRef<EXPR>];
}

define_ops!(@struct (EXPR ann:ObjRef;) (data));

macro_rules! obj_index_of {
    ($obj:ident $(<$generic:ty>)?, $field:ident) => {
        core::mem::offset_of!($crate::obj::$obj $(<$generic>)?, $field) / core::mem::size_of::<u32>()
    };
}

pub(crate) use obj_index_of;

impl Operator {

    pub fn name(self) -> &'static str {
        &Self::NAME[Self::NAME_OFS[self as usize] as usize
            ..Self::NAME_OFS[self as usize+1] as usize]
    }

    pub fn fields(self) -> &'static OpFields {
        let (desc, ofs) = Self::FIELDS;
        let bcode = &desc[ofs[self as usize] as usize .. ofs[self as usize + 1] as usize];
        unsafe { core::mem::transmute(bcode) }
    }

    pub fn is_expr_raw(op: u8) -> bool {
        op >= Self::KINT as u8
    }

    pub fn is_type_raw(op: u8) -> bool {
        use Operator::*;
        (TVAR|TPRI|TTEN|TTUP).as_u64_truncated() & (1 << op) != 0
    }

    // depends on ORDER NAMEDOBJ
    fn has_name_and_tab_raw(op: u8) -> bool {
        op <= Self::MOD as u8
    }

    // depends on ORDER NAMEDOBJ
    pub fn is_func_raw(op: u8) -> bool {
        op <= Self::QUERY as u8
    }

}

impl Obj {

    pub fn operator(self) -> Operator {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(self.op < <Operator as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(self.op) }
    }

    pub fn ref_params(self) -> RefParamIter {
        RefParamIter { n: (self.n-1) as _, cur: 0, iter: self.operator().fields().into_iter() }
    }

}

// ORDER BINOP
#[derive(EnumSetType)]
pub enum BinOp {
    OR,
    AND,
    ADD,
    SUB,
    MUL,
    DIV,
    POW,
    EQ,
    NE,
    LT,
    LE,
}

impl BinOp {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

}

macro_rules! define_intrinsics {
    ( $( $name:ident $($func:literal)? ;)* ) =>{
        #[derive(EnumSetType)]
        pub enum Intrinsic {
            $($name),*
        }

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

define_intrinsics! {
    UNM;
    NOT;
    EXP     b"exp";
    LOG     b"log";
    SUM     b"sum";
    WHICH   b"which";
    ANY     b"any";
    ALL     b"all";
    CONV    b"conv";
    REP     b"rep";
}

impl Intrinsic {

    pub fn from_u8(raw: u8) -> Intrinsic {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Intrinsic as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

     pub fn is_broadcast(self) -> bool {
         use Intrinsic::*;
         (UNM|NOT|EXP|LOG|CONV).contains(self)
     }

}

// TODO: put fieldtype and fieldname in separate arrays so this can just be implemented as
// enumerate+filter on the fieldtype array
pub struct RefParamIter {
    n: usize,
    cur: usize,
    iter: OpFieldIter<'static>
}

impl Iterator for RefParamIter {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        loop {
            match self.iter.next() {
                Some((FieldType::Spec, _)) => continue,
                Some((FieldType::VLit, _)) => return None,
                ft => {
                    let i = self.cur;
                    if i >= self.n { return None };
                    self.cur += 1;
                    if matches!(ft, None|Some((FieldType::Ref|FieldType::VRef, _))) {
                        return Some(i);
                    }
                }
            }
        }
    }
}

pub struct Objects {
    bump: Bump<u32>,
    lookup: HashTable<ObjRef>
}

fn fixupn(bump: &mut Bump<u32>, start: ObjRef) {
    bump[start.raw].n = (bump.end().align_index() - start.raw.align_index()) as _;
}

fn pushobj<T>(bump: &mut Bump<u32>, obj: T) -> ObjRef<T>
    where T: ObjType + bump::FromBytes + bump::IntoBytes
{
    let p = ObjRef { raw: bump.push(obj) };
    fixupn(bump, p.erase());
    p
}

fn checkvalidobj(o: Obj) {
    // FIXME replace with core::mem::variant_count when it stabilizes
    debug_assert!(o.op < <Operator as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
}

impl Objects {

    pub fn push<T>(&mut self, obj: T) -> ObjRef<T>
        where T: ObjType + bump::FromBytes + bump::IntoBytes
    {
        pushobj(&mut self.bump, obj)
    }

    pub fn push_args<T>(&mut self, head: T::Head, items: &[T::Item]) -> ObjRef<T>
        where T: ?Sized + ObjType + bump::PackedSliceDst,
              T::Head: bump::FromBytes + bump::IntoBytes,
              T::Item: zerocopy::FromBytes + zerocopy::IntoBytes
    {
        let p = ObjRef { raw: self.bump.push(head) };
        self.bump.write(items);
        fixupn(&mut self.bump, p.erase());
        p.cast()
    }

    pub fn push_extend<T,I>(&mut self, head: T::Head, items: I) -> ObjRef<T>
        where T: ?Sized + ObjType + bump::PackedSliceDst,
              T::Head: bump::FromBytes + bump::IntoBytes,
              T::Item: bump::FromBytes + bump::IntoBytes,
              I: Iterator<Item=T::Item>
    {
        let p = ObjRef { raw: self.bump.push(head) };
        self.bump.extend(items);
        fixupn(&mut self.bump, p.erase());
        p.cast()
    }

    pub fn push_reserve_dst<T>(&mut self, len: usize) -> (ObjRef<T>, &mut T)
        where T: ?Sized + ObjType + Aligned + bump::PackedSliceDst,
              T::Head: bump::FromBytes + bump::IntoBytes,
              T::Item: bump::FromBytes + bump::IntoBytes
    {
        let (raw, ptr) = self.bump.reserve_dst(len);
        let n = size_of_val(ptr) / T::ALIGN;
        unsafe { (*(ptr as *mut T as *mut Obj)).n = n as _; }
        (ObjRef { raw }, ptr)
    }

    pub fn get_raw(&self, idx: ObjRef) -> &[u32] {
        let o = self.bump[idx.raw];
        checkvalidobj(o);
        &self.bump.as_slice()[idx.raw.align_index() .. idx.raw.align_index() + o.n as usize]
    }

    pub fn get_raw_mut(&mut self, idx: ObjRef) -> &mut [u32] {
        let o = self.bump[idx.raw];
        checkvalidobj(o);
        &mut self.bump.as_mut_slice()[idx.raw.align_index() .. idx.raw.align_index() + o.n as usize]
    }

    pub fn end(&self) -> ObjRef {
        zerocopy::transmute!(self.bump.end())
    }

    pub fn dim(&self, tab: ObjRef<TAB>) -> usize {
        self[self[tab].shape].fields.len()
    }

    pub fn as_mut_ptr(&mut self) -> *mut u32 {
        self.bump.as_mut_slice().as_mut_ptr()
    }

    pub fn equal(&self, a: ObjRef, b: ObjRef) -> bool {
        if a == b { return true; }
        if a.is_nil() || b.is_nil() { return false; }
        let ao = self[a];
        let bo = self[b];
        if ao.op != bo.op { return false; }
        if Operator::is_expr_raw(ao.op)
            && !self.equal(self[a.cast::<EXPR>()].ann, self[b.cast::<EXPR>()].ann)
        {
            return false;
        }
        use ObjectRef::*;
        // note: this only does types and expressions. add other objects if needed.
        match (self.get(a.erase()), self.get(b.erase())) {
            (TVAR(_),  TVAR(_))   => false,
            (TPRI(a),  TPRI(b))   => a.ty == b.ty,
            (TTEN(a),  TTEN(b))   => a.dim == b.dim && self.equal(a.elem, b.elem),
            (TTUP(a),  TTUP(b))   => self.allequal(cast_args(&a.elems), cast_args(&b.elems)),
            (KINT(a),  KINT(b))   => a.k == b.k,
            (KINT64(a),KINT64(b)) => a.k == b.k,
            (KFP64(a), KFP64(b))  => a.k == b.k,
            (KSTR(a),  KSTR(b))   => a.k == b.k,
            (DIM(a),   DIM(b))    => a.axis == b.axis,
            (TUPLE(a), TUPLE(b))  => self.allequal(cast_args(&a.fields), cast_args(&b.fields)),
            (VGET(a),  VGET(b))   => a.var == b.var
                && self.allequal(cast_args(&a.idx), cast_args(&b.idx)),
            (CAT(a),   CAT(b))    => self.allequal(cast_args(&a.elems), cast_args(&b.elems)),
            (IDX(a),   IDX(b))    => self.equal(a.value.erase(), b.value.erase())
                && self.allequal(cast_args(&a.idx), cast_args(&b.idx)),
            (BINOP(a), BINOP(b))  => a.binop == b.binop
                && self.equal(a.left.erase(), b.left.erase())
                && self.equal(a.right.erase(), b.right.erase()),
            (INTR(a), INTR(b))    => a.func == b.func
                && self.allequal(cast_args(&a.args), cast_args(&b.args)),
            (LOAD(a),  LOAD(b))   => a.addr == b.addr
                && self.allequal(cast_args(&a.shape), cast_args(&b.shape)),
            (NEW(a),   NEW(b))    => self.allequal(cast_args(&a.shape), cast_args(&b.shape)),
            (GET(a),   GET(b))    => a.idx == b.idx && self.equal(a.value.erase(), b.value.erase()),
            (FREF(_),  FREF(_))   => todo!(),
            (CALL(_),  CALL(_))   => todo!(),
            (CALLX(_), CALLX(_))  => todo!(),
            _ => false
        }
    }

    pub fn allequal(&self, xs: &[ObjRef], ys: &[ObjRef]) -> bool {
        xs.len() == ys.len() && zip(xs.iter(), ys.iter()).all(|(&x, &y)| self.equal(x, y))
    }

    pub fn totype(&self, x: ObjRef) -> ObjRef {
        let op = self[x].op;
        if Operator::is_type_raw(op) {
            x
        } else if op == Obj::VAR {
            self[x.cast::<VAR>()].ann
        } else {
            debug_assert!(Operator::is_expr_raw(op));
            self[x.cast::<EXPR>()].ann
        }
    }

    pub fn annotate(&mut self, idx: ObjRef<EXPR>, ann: ObjRef) {
        if !ann.is_nil() {
            if self[idx].ann.is_nil() {
                self[idx].ann = ann;
            } else {
                // TODO: unify annotations. either do it right here, or leave a hint for type
                // inference.
                todo!()
            }
        }
    }

}

pub struct ObjKeys<'a> {
    objs: &'a Objects,
    idx: Option<ObjRef>
}

impl<'a> Iterator for ObjKeys<'a> {
    type Item = ObjRef;
    fn next(&mut self) -> Option<ObjRef> {
        let idx = self.idx?;
        self.idx = self.objs.next(idx);
        Some(idx)
    }
}

impl Objects {

    pub fn keys(&self) -> ObjKeys {
        ObjKeys { objs: self, idx: Some(ObjRef::NIL) }
    }

    pub fn pairs(&self) -> impl Iterator<Item=(ObjRef, ObjectRef)> {
        self.keys().map(|idx| (idx, self.get(idx)))
    }

    pub fn next(&self, idx: ObjRef) -> Option<ObjRef> {
        let o = self.bump[idx.raw];
        checkvalidobj(o);
        let raw = idx.raw.add_align(o.n as _);
        if raw.align_index() < self.bump.end().align_index() {
            Some(ObjRef { raw })
        } else {
            None
        }
    }

}

fn lookupkey(data: &[u32], idx: usize) -> (u32, IRef<[u8]>) {
    let obj: Obj = zerocopy::transmute!(data[idx]);
    let name: IRef<[u8]> = zerocopy::transmute!(data[idx+1]);
    let mut namespace = obj.op as u32;
    if Operator::has_name_and_tab_raw(obj.op) {
        namespace |= data[idx+2] << 3;
    }
    (namespace, name)
}

fn entry<'lookup, 'data>(
    lookup: &'lookup mut HashTable<ObjRef>,
    data: &'data [u32],
    key: (u32, IRef<[u8]>)
) -> Entry<'lookup, ObjRef> {
    lookup.entry(
        fxhash(key),
        |idx| lookupkey(data, idx.raw.align_index()) == key,
        |idx| fxhash(lookupkey(data, idx.raw.align_index()))
    )
}

pub struct VacantLookupEntry<'a, F> {
    entry: VacantEntry<'a, ObjRef>,
    create: F
}

impl<'a, T: ?Sized + ObjType, F: FnOnce() -> ObjRef<T>> VacantLookupEntry<'a, F> {

    pub fn create(self) -> ObjRef<T> {
        let o = (self.create)();
        self.entry.insert(o.erase());
        o
    }

}

pub enum LookupEntry<'a, T: ?Sized + ObjType, F> {
    Occupied(ObjRef<T>),
    Vacant(VacantLookupEntry<'a, F>)
}

impl<'a, T: ?Sized + ObjType, F: FnOnce() -> ObjRef<T>> LookupEntry<'a, T, F> {

    pub fn get_or_create(self) -> ObjRef<T> {
        match self {
            Self::Occupied(idx) => idx,
            Self::Vacant(e)     => e.create()
        }
    }

    pub fn get(self) -> Option<ObjRef<T>> {
        match self {
            Self::Occupied(idx) => Some(idx),
            Self::Vacant(_)     => None
        }
    }

}

impl Objects {

    pub fn tab(
        &mut self,
        name: IRef<[u8]>
    ) -> LookupEntry<'_, TAB, impl FnMut() -> ObjRef<TAB> + '_> {
        match entry(&mut self.lookup, self.bump.as_slice(), (Operator::TAB as _, name)) {
            Entry::Occupied(e) => LookupEntry::Occupied(e.get().cast()),
            Entry::Vacant(entry) => {
                let bump = &mut self.bump;
                let create = move || pushobj(bump, TAB::new(name, ObjRef::NIL.cast()));
                LookupEntry::Vacant(VacantLookupEntry { entry, create })
            }
        }
    }

    pub fn var(
        &mut self,
        tab: ObjRef<TAB>,
        name: IRef<[u8]>
    ) -> LookupEntry<'_, VAR, impl FnMut() -> ObjRef<VAR> + '_> {
        let raw: u32 = zerocopy::transmute!(tab);
        match entry(
            &mut self.lookup,
            self.bump.as_slice(),
            ((raw<<3) | Operator::VAR as u32, name)
        ) {
            Entry::Occupied(e) => LookupEntry::Occupied(e.get().cast()),
            Entry::Vacant(entry) => {
                let bump = &mut self.bump;
                let create = move || pushobj(bump, VAR::new(name, tab, ObjRef::NIL));
                LookupEntry::Vacant(VacantLookupEntry { entry, create })
            }
        }
    }

}

impl<T> Index<ObjRef<T>> for Objects
    where T: ?Sized + ObjType + bump::Get
{
    type Output = T;
    fn index(&self, idx: ObjRef<T>) -> &T {
        checkvalidobj(self.bump[idx.erase().raw]);
        &self.bump[idx.raw]
    }
}

impl<T> IndexMut<ObjRef<T>> for Objects
    where T: ?Sized + ObjType + bump::Get + bump::GetMut
{
    fn index_mut(&mut self, idx: ObjRef<T>) -> &mut T {
        checkvalidobj(self.bump[idx.erase().raw]);
        &mut self.bump[idx.raw]
    }
}

macro_rules! default_objs {
    ( $( $vis:vis $name:ident $(: $type:ident)? ($idx:literal) = $new:expr;)* ) => {

        impl ObjRef {
            $( $vis const $name: ObjRef $(<$type>)? = zerocopy::transmute!($idx); )*
        }

        fn insert_default_objs(objs: &mut Objects) {
            $(
                {
                    let o = objs.push($new);
                    debug_assert!(o.erase() == ObjRef::$name.erase());
                }
            )*
        }

    };
}

default_objs! {
    pub NIL           (0)  = NIL::new(ObjRef::UNIT);
        UNIT:   TTUP  (2)  = TTUP::new();
    pub B1:     TPRI  (3)  = TPRI::new(Primitive::B1 as _);
    pub PTR:    TPRI  (4)  = TPRI::new(Primitive::PTR as _);
    pub FALSE:  KINT  (5)  = KINT::new(ObjRef::B1.erase(), 0);
    pub TRUE:   KINT  (8)  = KINT::new(ObjRef::B1.erase(), 1);
        EMPTY:  TUPLE (11) = TUPLE::new(ObjRef::NIL);
    pub GLOBAL: TAB   (13) = TAB::new(Ccx::SEQ_GLOBAL, ObjRef::EMPTY);
}

impl Default for Objects {

    fn default() -> Self {
        let mut objs = Objects {
            bump: Default::default(),
            lookup: Default::default()
        };
        insert_default_objs(&mut objs);
        objs.lookup.insert_unique(
            fxhash((Operator::TAB as u32, Ccx::SEQ_GLOBAL)),
            ObjRef::GLOBAL.erase(),
            |_| unreachable!()
        );
        objs
    }

}
