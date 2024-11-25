//! Type inference.

use core::hash::Hasher;
use core::iter::zip;

use alloc::collections::vec_deque::VecDeque;
use enumset::{enum_set, EnumSet};
use hashbrown::{hash_map, hash_table, HashTable};
use rustc_hash::FxHasher;

use crate::compile::{self, Ccx, Phase};
use crate::dump::trace_objs;
use crate::hash::HashMap;
use crate::index::{index, IndexSlice, IndexVec};
use crate::obj::{obj_index_of, BinOp, Intrinsic, Obj, ObjRef, ObjectRef, Objects, Operator, BINOP, CALLX, EXPR, GET, INTR, KFP64, KINT, KINT64, LOAD, MOD, NEW, QUERY, TAB, TPRI, TTEN, TTUP, TUPLE, VAR, VGET, VSET};
use crate::trace::trace;
use crate::typestate::{Absent, Access, R};
use crate::typing::{Constructor, Primitive, PRI_IDX};

index!(struct TypeVar(u32) debug("t{}"));

/*
 *        +--------+--------+-------+------+
 *        | 31..29 | 28..16 | 15..8 | 7..0 |
 *        +========+========+=======+======+
 * Var    |    0   |        typevar        |
 *        +--------+----------------+------+
 * Dim    |    1   |                |  dim |
 *        +--------+--------+-------+------+
 * Pri    |    2   |        |  pri enumset |
 *        +--------+--------+--------------+
 * Never  |    2   |           0           |
 *        +--------+-----------------------+
 * Con    |  3+con |         base          |
 *        +--------+-----------------------+
 */
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct Type(u32);

impl Type {

    const NEVER: Self = Self(2 << 29); // empty pri
    const UNIT: Self = Self::con(Constructor::Unit as _, zerocopy::transmute!(0));

    fn var(tvar: TypeVar) -> Self {
        zerocopy::transmute!(tvar)
    }

    fn dim(dim: u8) -> Self {
        Self((1 << 29) | (dim as u32))
    }

    fn pri<P: Into<EnumSet<Primitive>>>(pri: P) -> Self {
        Self((2 << 29) | pri.into().as_u32_truncated())
    }

    const fn con(con: u8, base: TypeVar) -> Self {
        let base: u32 = zerocopy::transmute!(base);
        Self(((3+con as u32) << 29) | base)
    }

    fn unpack(self) -> TypeRepr {
        use TypeRepr::*;
        match self.0 >> 29 {
            0 => Var(zerocopy::transmute!(self.0)),
            1 => Dim(self.0 as _),
            2 => Pri(EnumSet::from_u16_truncated(self.0 as _)),
            c => Con((c-3) as _, zerocopy::transmute!(self.0 & 0x1fffffff))
        }
    }

}

#[derive(Clone, Copy, Debug)]
enum TypeRepr {
    Var(TypeVar),
    Con(u8, TypeVar),
    Dim(u8),
    Pri(EnumSet<Primitive>),
}

enum Constraint {
    BinOp(TypeVar, TypeVar, TypeVar), // a:dim, b:dim, c:dim :: a = b ∘ c
    Index(TypeVar, Type, TypeVar),    // b:tensor, c:dim :: a = b[c]
    Splat(TypeVar, TypeVar, u8),      // a:dim, b:dim :: a = b + n
}

pub struct TypeInfer {
    sub: IndexVec<TypeVar, Type>,
    con: VecDeque<Constraint>,
    tobj: HashTable<ObjRef>,
    ann: HashMap<ObjRef, Type>,
    tab: ObjRef<TAB>
}

type Tcx<'a> = Ccx<TypeInfer, R<'a>>;

const PRI_INT: EnumSet<Primitive> = {
    use Primitive::*;
    enum_set!(I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64)
};

const PRI_NUM: EnumSet<Primitive> = {
    use Primitive::*;
    enum_set!(PRI_INT | F32 | F64)
};

fn kintpri(v: i64) -> EnumSet<Primitive> {
    use Primitive::*;
    let mut pri = U64 | I64;
    if v >= 0 { pri |= PTR }
    if v == v as i8  as i64 { pri |= U8 | I8 };
    if v == v as i16 as i64 { pri |= U16 | I16 };
    if v == v as i32 as i64 { pri |= U32 | I32 };
    if v == v as f32 as i64 { pri |= F32 };
    if v == v as f64 as i64 { pri |= F64 };
    pri
}

fn kfpri(f: f64) -> EnumSet<Primitive> {
    use Primitive::*;
    let mut pri = F32 | F64;
    if f == f as i8  as f64 { pri |= U8 | I8 };
    if f == f as i16 as f64 { pri |= U16 | I16 };
    if f == f as i32 as f64 { pri |= U32 | I32 };
    if f == f as i64 as f64 { pri |= U64 | I64; if f >= 0.0 { pri |= PTR } };
    pri
}

fn newtypevar(sub: &mut IndexVec<TypeVar, Type>) -> TypeVar {
    sub.push(Type::var(sub.end()))
}

fn newcontype(sub: &mut IndexVec<TypeVar, Type>, con: Constructor, par: &[Type]) -> Type {
    let base = sub.end();
    sub.raw.extend_from_slice(par);
    Type::con(con as _, base)
}

fn newpairtype(tvar: &mut IndexVec<TypeVar, Type>, left: Type, right: Type) -> Type {
    newcontype(tvar, Constructor::Pair, &[left, right])
}

fn newshapetype(sub: &mut IndexVec<TypeVar, Type>, dims: u8) -> Type {
    let mut ty = Type::UNIT;
    for _ in 0..dims {
        let base = sub.end();
        sub.push(Type::pri(PRI_IDX)); // elem
        newtypevar(sub); // dim
        ty = newpairtype(sub, Type::con(Constructor::Tensor as _, base), ty);
    }
    ty
}

fn unifyvar(sub: &mut IndexSlice<TypeVar, Type>, a: TypeVar, b: Type) {
    use TypeRepr::*;
    trace!(TYPE "unify {:?}:{:?} = {:?}", a, sub[a].unpack(), b.unpack());
    match (sub[a].unpack(), b.unpack()) {
        (Var(i), _) if i == a => sub[a] = b,
        (_, Var(j)) if j == a => { /* ok */ },
        (Var(i), _) => unifyvar(sub, i, b),
        (Pri(_), Pri(_)) => sub[a].0 &= b.0,
        (Pri(_), Var(j)) if matches!(sub[j].unpack(), Pri(_)) => {
            sub[j].0 &= sub[a].0;
            sub[a] = b;
        },
        (Pri(_), Var(j)) => unifyvar(sub, j, Type::var(a)),
        (Pri(_), Con(Constructor::TENSOR, b0)) => {
            unifyvar(sub, b0, Type::var(a));
            unifyvar(sub, b0+1, Type::dim(0));
        },
        _ => {
            // TODO: set sub[a] = NEVER if problems
            unify(sub, sub[a], b);
        }
    }
}

fn unify(sub: &mut IndexSlice<TypeVar, Type>, a: Type, b: Type) {
    use TypeRepr::*;
    match (a.unpack(), b.unpack()) {
        (Var(i), _) => unifyvar(sub, i, b),
        (_, Var(j)) => unifyvar(sub, j, a),
        (Pri(p), Pri(q)) if !(p&q).is_empty() => { /* ok */ },
        (Dim(i), Dim(j)) if i == j => { /* ok */ },
        (Con(Constructor::TENSOR, d), Pri(p)) | (Pri(p), Con(Constructor::TENSOR, d)) => {
            unifyvar(sub, d, Type::pri(p));
            unifyvar(sub, d+1, Type::dim(0));
        },
        (Con(ca, ba), Con(cb, bb)) if ca == cb => {
            for i in 0..Constructor::from_u8(ca).arity() as isize {
                unifyvar(sub, ba+i, Type::var(bb+i));
            }
        },
        _ => {
            // TODO: type error
            todo!()
        }
    }
}

fn unpacktensor(sub: &mut IndexVec<TypeVar, Type>, ten: Type) -> (TypeVar, TypeVar) {
    let elem = newtypevar(sub);
    let dim = newtypevar(sub);
    let tt = newcontype(sub, Constructor::Tensor, &[Type::var(elem), Type::var(dim)]);
    unify(sub, ten, tt);
    (elem, dim)
}

fn substitution(sub: &IndexSlice<TypeVar, Type>, tv: TypeVar) -> Option<Type> {
    let ty = sub[tv];
    if let TypeRepr::Var(i) = ty.unpack() {
        if i == tv {
            return None;
        }
        return substitution(sub, i);
    }
    Some(ty)
}

fn dimension(sub: &IndexSlice<TypeVar, Type>, ty: Type) -> Option<u8> {
    use TypeRepr::*;
    match ty.unpack() {
        Var(i) if sub[i] == ty => None,
        Var(i) => dimension(sub, sub[i]),
        Con(Constructor::TENSOR, base) => dimension(sub, Type::var(base+1)),
        Dim(d) => Some(d),
        _ => Some(0)
    }
}

fn simplify_binop_operand(
    sub: &mut IndexSlice<TypeVar, Type>,
    a: TypeVar,
    b: TypeVar,
    c: TypeVar
) -> bool {
    match dimension(sub, Type::var(b)) {
        Some(0) => {
            // lhs is scalar => result dimension is rhs dimension
            unifyvar(sub, a, Type::var(c));
            true
        },
        Some(_) => {
            // lhs is vector => result dimension is lhs dimension
            unifyvar(sub, a, Type::var(b));
            true
        },
        None => {
            // lhs is unknown
            false
        }
    }
}

fn simplify_binop(
    sub: &mut IndexSlice<TypeVar, Type>,
    a: TypeVar,
    b: TypeVar,
    c: TypeVar
) -> bool {
    match dimension(sub, Type::var(a)) {
        Some(0) => {
            // scalar result => both operands are scalar.
            unifyvar(sub, a, Type::var(b));
            unifyvar(sub, a, Type::var(c));
            true
        },
        _ => {
            // vector or unknown result => check operands.
            simplify_binop_operand(sub, a, b, c) || simplify_binop_operand(sub, a, c, b)
        }
    }
}

fn simplify_index(
    sub: &mut IndexVec<TypeVar, Type>,
    a: TypeVar,
    b: Type,
    c: TypeVar
) -> bool {
    let tb = match b.unpack() {
        TypeRepr::Var(i) => match substitution(sub, i) {
            Some(t) => t,
            None => return false
        },
        _ => b
    };
    let TypeRepr::Con(Constructor::TENSOR, base) = tb.unpack() else { unreachable!() };
    let Some(tdim) = substitution(sub, base+1) else { return false };
    let TypeRepr::Dim(d) = tdim.unpack() else { unreachable!() };
    let aty = match dimension(sub, Type::var(c)) {
        // scalar index => result type is one dimension lower than array type
        Some(0) => match d {
            1 => Type::var(base),
            _ => newcontype(sub, Constructor::Tensor, &[Type::var(base), Type::dim(d-1)])
        },
        // vector index => result type is same as array type
        Some(_) => tb,
        None => return false
    };
    unifyvar(sub, a, aty);
    true
}

fn simplify_splat(sub: &mut IndexVec<TypeVar, Type>, a: TypeVar, b: TypeVar, n: u8) -> bool {
    use TypeRepr::*;
    match (substitution(sub, a).map(Type::unpack), substitution(sub, b).map(Type::unpack)) {
        (Some(Dim(a)), None) => {
            unifyvar(sub, b, Type::dim(a-n));
            true
        },
        (None, Some(Dim(b))) => {
            unifyvar(sub, a, Type::dim(b+n));
            true
        },
        (Some(Dim(a)), Some(Dim(b))) => {
            if a != b {
                // TODO: type error
                todo!()
            }
            true
        },
        (None, None) => false,
        _ => unreachable!()
    }
}

fn constraint(ctx: &mut TypeInfer, con: Constraint) -> bool {
    if match con {
        Constraint::BinOp(a, b, c) => simplify_binop(&mut ctx.sub, a, b, c),
        Constraint::Index(a, b, c) => simplify_index(&mut ctx.sub, a, b, c),
        Constraint::Splat(a, b, n) => simplify_splat(&mut ctx.sub, a, b, n)
    } {
        true
    } else {
        ctx.con.push_back(con);
        false
    }
}

fn simplify(ctx: &mut TypeInfer) {
    'fixpointloop: loop {
        for _ in 0..ctx.con.len() {
            let c = ctx.con.pop_front().unwrap();
            if constraint(ctx, c) {
                continue 'fixpointloop;
            }
        }
        // fixpoint
        return;
    }
}

fn createtypeobj(objs: &mut Objects, ty: TypeRepr, work: &[u32]) -> ObjRef {
    use TypeRepr::*;
    match ty {
        Pri(p) => match p.into_iter().next() {
            Some(ty) => objs.push(TPRI::new(ty as _)).erase(),
            None => {
                // TODO: allow this and return ObjRef::NIL.
                // after creating all type objs, check that all *reachable* expressions
                // have a non-nil type.
                todo!();
            }
        }
        Con(Constructor::TENSOR, _) => {
            debug_assert!(work[1] > 0); // dim 0 tensor should be canonicalized to scalar
            objs.push(TTEN::new(work[1] as _, zerocopy::transmute!(work[0]))).erase()
        },
        Con(Constructor::UNIT|Constructor::PAIR, _) => {
            // XXX replace with zerocopy::transmute when it can do that
            let work: &[ObjRef] = unsafe {
                core::slice::from_raw_parts(work.as_ptr().cast(), work.len())
            };
            objs.push_args::<TTUP>(TTUP::new(), work).erase()
        }
        _ => unreachable!()
    }
}

fn isconcretetype(tvar: &IndexSlice<TypeVar, Type>, ty: Type) -> bool {
    use TypeRepr::*;
    match ty.unpack() {
        Var(j) if ty == Type::var(j) => false,
        Var(j) => isconcretetype(tvar, tvar[j]),
        Con(c, base) => (0..Constructor::from_u8(c).arity() as isize)
            .all(|i| isconcretetype(tvar, tvar[base+i])),
        Pri(p) => p.len() <= 1,
        Dim(_) => true
    }
}

fn createtype(tcx: &mut Tcx, idx: ObjRef) -> Type {
    if let Some(&ty) = tcx.data.ann.get(&idx) {
        return ty;
    }
    let objs = Access::borrow(&tcx.objs);
    let o = objs.get(idx);
    let ty = match o {
        ObjectRef::TVAR(_) => Type::var(newtypevar(&mut tcx.data.sub)),
        ObjectRef::TPRI(&TPRI { ty, .. }) => Type::pri(EnumSet::from_u16_truncated(1 << ty)),
        ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
            let e = createtype(tcx, elem);
            newcontype(&mut tcx.data.sub, Constructor::Tensor, &[e, Type::dim(dim)])
        },
        ObjectRef::TTUP(&TTUP { ref elems, .. }) => {
            let mut ty = Type::UNIT;
            for &e in elems.iter().rev() {
                let ety = createtype(tcx, e);
                ty = newpairtype(&mut tcx.data.sub, ety, ty);
            }
            ty
        },
        _ => unreachable!()
    };
    if isconcretetype(&tcx.data.sub, ty) {
        let hash = hashtypeobj(o);
        if let hash_table::Entry::Vacant(e) = tcx.data.tobj.entry(
            hash,
            |&t| objs.equal(t, idx),
            |&t| hashtypeobj(objs.get(t))
        ) {
            e.insert(idx);
        }
    }
    tcx.data.ann.insert_unique_unchecked(idx, ty);
    ty
}

fn sametype(a: ObjectRef, b: TypeRepr, work: &[u32]) -> bool {
    match (a, b) {
        (ObjectRef::TPRI(&TPRI { ty, .. }), TypeRepr::Pri(p)) => p.as_u16_truncated() == 1 << ty,
        (ObjectRef::TTEN(&TTEN { elem, dim, .. }), TypeRepr::Con(Constructor::TENSOR, _))
            => work == &[zerocopy::transmute!(elem), dim as _],
        (ObjectRef::TTUP(TTUP { elems, .. }), TypeRepr::Con(Constructor::PAIR|Constructor::UNIT, _))
            => work.len() == elems.len()
            && zip(work.iter(), elems.iter()).all(|(&ea,&eb)| ea == zerocopy::transmute!(eb)),
        _ => false
    }
}

fn typeobj(ccx: &mut Ccx<TypeInfer>, ty: Type) -> ObjRef {
    match ty.unpack() {
        TypeRepr::Var(tv) => return typeobj(ccx, ccx.data.sub[tv]),
        type_ => {
            let base = ccx.tmp.end();
            let hash = hashtype(ccx, type_);
            let tx = &mut *ccx.data;
            let args: &[u32] = &ccx.tmp[base.cast_up()..];
            let o = match tx.tobj.entry(
                hash,
                |&t| sametype(ccx.objs.get(t), type_, args),
                |&t| hashtypeobj(ccx.objs.get(t))
            ) {
                hash_table::Entry::Vacant(e)
                    => *e.insert(createtypeobj(&mut ccx.objs, type_, args)).get(),
                hash_table::Entry::Occupied(e) => *e.get()
            };
            ccx.tmp.truncate(base);
            o
        }
    }
}

// must match hashtypeobj
// stores type params in ccx.tmp
fn hashtype(ccx: &mut Ccx<TypeInfer>, ty: TypeRepr) -> u64 {
    use TypeRepr::*;
    let mut hash = FxHasher::default();
    match ty {
        Pri(p) => hash.write_u16(p.as_u16_truncated()),
        Con(Constructor::TENSOR, base) => {
            let elem = typeobj(ccx, Type::var(base));
            let TypeRepr::Dim(dim) = ccx.data.sub[base+1].unpack() else { unreachable!() };
            hash.write_u32(zerocopy::transmute!(elem));
            hash.write_u8(dim);
            ccx.tmp.push(elem);
            ccx.tmp.push(dim as u32);
        },
        Con(Constructor::PAIR, mut t) => {
            loop {
                let e = typeobj(ccx, Type::var(t));
                hash.write_u32(zerocopy::transmute!(e));
                ccx.tmp.push(e);
                let TypeRepr::Con(c, tt) = ccx.data.sub[t+1].unpack() else { unreachable!() };
                if c == Constructor::UNIT { break }
                t = tt;
            }
        },
        Con(Constructor::UNIT, _) => { /* NOP */ },
        _ => unreachable!()
    }
    hash.finish()
}

// must match hashtype
fn hashtypeobj(o: ObjectRef) -> u64 {
    let mut hash = FxHasher::default();
    match o {
        ObjectRef::TPRI(&TPRI { ty, .. }) => hash.write_u16(1 << ty),
        ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
            hash.write_u32(zerocopy::transmute!(elem));
            hash.write_u8(dim);
        },
        ObjectRef::TTUP(TTUP { elems, ..  }) => {
            for &e in elems {
                hash.write_u32(zerocopy::transmute!(e));
            }
        },
        _ => unreachable!()
    }
    hash.finish()
}

fn vartype(tcx: &mut Tcx, var: ObjRef<VAR>) -> TypeVar {
    let ts = &mut *tcx.data;
    let tv = match ts.ann.entry(var.erase()) {
        hash_map::Entry::Occupied(e) => return zerocopy::transmute!(*e.get()),
        hash_map::Entry::Vacant(e) => {
            let tv = newtypevar(&mut ts.sub);
            e.insert(Type::var(tv));
            tv
        }
    };
    let ann = tcx.objs[var].ann;
    if !ann.is_nil() {
        let ty = createtype(tcx, ann);
        unifyvar(&mut tcx.data.sub, tv, ty);
    }
    tv
}

fn visitvref(tcx: &mut Tcx, var: ObjRef<VAR>, idx: &[ObjRef<EXPR>]) -> Type {
    let need = tcx.objs.dim(tcx.objs[var].tab);
    let mut have = idx.len();
    if have < need {
        // not enough indices mentioned, insert current expression's index.
        // these are scalar indices, so they don't increase the dimension.
        // if this results in too many indices being mentioned, it's a type error.
        have += tcx.objs.dim(tcx.data.tab);
    }
    if have > need {
        // too many indices mentioned.
        return Type::NEVER;
    }
    let vty = Type::var(vartype(tcx, var));
    if idx.is_empty() {
        // no explicit indices mentioned, so we know the exact arity at this point.
        if have < need {
            newcontype(&mut tcx.data.sub, Constructor::Tensor, &[vty, Type::dim((need-have) as _)])
        } else {
            vty
        }
    } else {
        // explicit indices mentioned.
        // here the dimensionality depends on the dimension of the index expressions.
        // what we do here is:
        // * start from `v_0 = tensor(T, N)`, where `T` is the type of the variable and `N` is the
        //   dimension of its table.
        // * every explicit index `e_0, ..., e_k` gets a constraint:
        //     Index(v_{j+1}, v_j, e_j)
        let mut v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[vty, Type::dim(need as _)]);
        for &e in idx {
            let ety = exprtype(tcx, e);
            let (elem, dim) = unpacktensor(&mut tcx.data.sub, Type::var(ety));
            unifyvar(&mut tcx.data.sub, elem, Type::pri(PRI_IDX));
            let vnext = newtypevar(&mut tcx.data.sub);
            constraint(&mut tcx.data, Constraint::Index(vnext, v, dim));
            v = Type::var(vnext);
        }
        // insert splats for missing indices
        if have < need {
            let vdim = newtypevar(&mut tcx.data.sub);
            let vten = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[vty, Type::var(vdim)]);
            unify(&mut tcx.data.sub, vten, v);
            let rdim = newtypevar(&mut tcx.data.sub);
            let res = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[vty, Type::var(rdim)]);
            constraint(&mut tcx.data, Constraint::Splat(rdim, vdim, (need-have) as _));
            v = res;
        }
        v
    }
}

macro_rules! instantiate {
    (@type pri $v:expr ; $($_:tt)*) => {
        Type::pri($v)
    };
    (@type $con:ident $($t:expr)+ ; $tcx:expr) => {
        newcontype(&mut $tcx.data.sub, Constructor::$con, &[$(zerocopy::transmute!($t)),+])
    };
    (@type $v:tt ; $($_:tt)*) => {
        $v
    };
    (
        $tcx:expr,
        $args:expr;
        $($unpack:ident)*
        $(, $($new:ident)*)?
        $(
            ::
            $( $lhs:ident [$($rhs:tt)*] ),*
        )?
        =>
        $($ret:tt)*
    ) => {{
        let &[ $($unpack),* ] = $args else { unreachable!() };
        $( $( let $new = newtypevar(&mut $tcx.data.sub); )* )?
        $(
            $(
                {
                    let rhs = instantiate!(@type $($rhs)* ; $tcx);
                    unifyvar(&mut $tcx.data.sub, $lhs, rhs);
                }
            )*
        )?
        zerocopy::transmute!(instantiate!(@type $($ret)* ; $tcx))
    }};
}

fn visitintrinsic(tcx: &mut Tcx, func: Intrinsic, args: &[ObjRef<EXPR>]) -> Type {
    use Intrinsic::*;
    let base = tcx.tmp.end();
    for &a in args {
        let ety = exprtype(tcx, a);
        tcx.tmp.push(ety);
    }
    let aty: &[TypeVar] = &tcx.tmp[base.cast_up()..];
    macro_rules! I { ($($t:tt)*) => { instantiate!(tcx, aty; $($t)*) }; }
    let ty = match func {
        UNM | EXP | LOG => I!(a,e n :: a[Tensor e n], e[pri PRI_NUM] => a),
        NOT => I!(a,n :: a[Tensor Type::pri(Primitive::B1) n] => a),
        SUM => I!(a,e n :: a[Tensor e n], e[pri PRI_NUM] => e),
        // TODO (?): generalize WHICH to return tuples.
        WHICH => I!(a :: a[Tensor Type::pri(Primitive::B1) Type::dim(1)]
            => Tensor Type::pri(PRI_IDX) Type::dim(1)),
        CONV => I!(a,b e n :: a[Tensor e n] => Tensor b n),
        REP => I!(a,e n m :: a[Tensor e n] => Tensor e m),
    };
    tcx.tmp.truncate(base);
    ty
}

fn visitexpr(tcx: &mut Tcx, idx: ObjRef<EXPR>) -> Option<Type> {
    let objs = Access::borrow(&tcx.objs);
    match objs.get(idx.erase()) {
        ObjectRef::KINT(&KINT { k, .. }) => Some(Type::pri(kintpri(k as _))),
        ObjectRef::KINT64(&KINT64 { k, .. }) => Some(Type::pri(kintpri(tcx.intern.bump()[k].get()))),
        ObjectRef::KFP64(&KFP64 { k, .. }) => Some(Type::pri(kfpri(tcx.intern.bump()[k].get()))),
        ObjectRef::KSTR(_) => Some(Type::pri(Primitive::STR)),
        ObjectRef::DIM(_) => Some(Type::pri(PRI_IDX)),
        ObjectRef::TUPLE(TUPLE { fields, .. }) => {
            let mut ty = Type::UNIT;
            for &e in fields.iter().rev() {
                let ety = exprtype(tcx, e);
                ty = newpairtype(&mut tcx.data.sub, Type::var(ety), ty);
            }
            Some(ty)
        },
        ObjectRef::VGET(&VGET { var, ref idx, .. }) => Some(visitvref(tcx, var, idx)),
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(&LOAD { addr, ref shape, .. }) => {
            let aty = exprtype(tcx, addr);
            unify(&mut tcx.data.sub, Type::var(aty), Type::pri(Primitive::PTR));
            for &d in shape {
                // TODO: this should support all types of integers, but currently lower
                // assumes all lengths are IRT_IDX (this is hardcoded in return slots).
                // this should probably convert to IRT_IDX because there's not much benefit
                // in supporting other length sizes.
                let dty = exprtype(tcx, d);
                unify(&mut tcx.data.sub, Type::var(dty), Type::pri(PRI_IDX));
            }
            // result type annotation is generated by parser
            None
        },
        ObjectRef::NEW(NEW { shape, .. }) => {
            for &s in shape {
                // nb. see TODO comment in LOAD
                let sty = exprtype(tcx, s);
                unify(&mut tcx.data.sub, Type::var(sty), Type::pri(PRI_IDX));
            }
            let elem = newtypevar(&mut tcx.data.sub);
            Some(newcontype(&mut tcx.data.sub, Constructor::Tensor,
                &[Type::var(elem), Type::dim(shape.len() as _)]))
        },
        ObjectRef::GET(&GET { value, mut idx, .. }) => {
            let mut vty = Type::var(exprtype(tcx, value));
            loop {
                let e = newtypevar(&mut tcx.data.sub);
                let next = newtypevar(&mut tcx.data.sub);
                let repr = newpairtype(&mut tcx.data.sub, Type::var(e), Type::var(next));
                unify(&mut tcx.data.sub, vty, repr);
                match idx {
                    0 => break Some(Type::var(e)),
                    _ => {
                        idx -= 1;
                        vty = repr;
                    }
                }
            }
        },
        ObjectRef::BINOP(&BINOP { binop, left, right, .. }) => {
            use BinOp::*;
            let td = newtypevar(&mut tcx.data.sub);
            let lty = exprtype(tcx, left);
            let rty = exprtype(tcx, right);
            let (le, ld) = unpacktensor(&mut tcx.data.sub, Type::var(lty));
            let (re, rd) = unpacktensor(&mut tcx.data.sub, Type::var(rty));
            unify(&mut tcx.data.sub, Type::var(le), Type::var(re));
            constraint(&mut tcx.data, Constraint::BinOp(td, ld, rd));
            let res = match BinOp::from_u8(binop) {
                OR | AND => {
                    unify(&mut tcx.data.sub, Type::var(le), Type::pri(Primitive::B1));
                    Type::pri(Primitive::B1)
                },
                EQ | NE => {
                    Type::pri(Primitive::B1)
                },
                LT | LE => {
                    unify(&mut tcx.data.sub, Type::var(le), Type::pri(PRI_NUM));
                    Type::pri(Primitive::B1)
                },
                ADD | SUB | MUL | DIV => {
                    Type::var(le)
                },
                POW => todo!(),
            };
            Some(newcontype(&mut tcx.data.sub, Constructor::Tensor, &[res, Type::var(td)]))
        },
        ObjectRef::INTR(&INTR { func, ref args, .. })
            => Some(visitintrinsic(tcx, Intrinsic::from_u8(func), args)),
        ObjectRef::FREF(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLX(CALLX { inputs, .. }) => {
            for &input in inputs {
                exprtype(tcx, input);
            }
            None
        },
        _ => unreachable!()
    }
}

fn exprtype(tcx: &mut Tcx, idx: ObjRef<EXPR>) -> TypeVar {
    let ts = &mut *tcx.data;
    let tv = match ts.ann.entry(idx.erase()) {
        hash_map::Entry::Occupied(e) => return zerocopy::transmute!(*e.get()),
        hash_map::Entry::Vacant(e) => {
            let tv = newtypevar(&mut ts.sub);
            e.insert(Type::var(tv));
            tv
        }
    };
    if let Some(ty) = visitexpr(tcx, idx) {
        tcx.data.sub[tv] = ty;
    }
    let ann = tcx.objs[idx.cast::<EXPR>()].ann;
    if !ann.is_nil() {
        let ty = createtype(tcx, ann);
        unifyvar(&mut tcx.data.sub, tv, ty);
    }
    tv
}

fn visitall(tcx: &mut Tcx) {
    let b1 = tcx.data.sub.push(Type::pri(Primitive::B1));
    tcx.data.ann.insert_unique_unchecked(ObjRef::TRUE.erase(), Type::var(b1));
    tcx.data.ann.insert_unique_unchecked(ObjRef::FALSE.erase(), Type::var(b1));
    let objs = Access::borrow(&tcx.objs);
    for (_, o) in objs.pairs() {
        match o {
            ObjectRef::TAB(&TAB { shape, .. }) => {
                tcx.data.tab = ObjRef::GLOBAL;
                let dims = tcx.objs[shape].fields.len();
                let ty = newshapetype(&mut tcx.data.sub, dims as _);
                let ety = exprtype(tcx, shape.cast());
                unifyvar(&mut tcx.data.sub, ety, ty);
            },
            ObjectRef::MOD(&MOD { tab, guard, ref value, .. }) => {
                tcx.data.tab = tab;
                if !guard.is_nil() {
                    let ety = exprtype(tcx, guard);
                    unifyvar(&mut tcx.data.sub, ety, Type::pri(Primitive::B1));
                }
                for &vset in value.iter() {
                    let &VSET { var, value, ref idx, .. } = &objs[vset];
                    let vty = visitvref(tcx, var, idx);
                    let ety = exprtype(tcx, value);
                    unifyvar(&mut tcx.data.sub, ety, vty);
                }
            },
            ObjectRef::FUNC(_) => todo!(),
            ObjectRef::QUERY(&QUERY { tab, ref value, .. }) => {
                tcx.data.tab = tab;
                for &v in value {
                    exprtype(tcx, v);
                }
            },
            _ => {}
        }
    }
}

// * eliminate type variables
// * multi pri => widest type
// * tensor<t, 0> => t
fn canonty(sub: &mut IndexSlice<TypeVar, Type>, tv: TypeVar) -> Type {
    use TypeRepr::*;
    let mut ty = sub[tv];
    ty = match ty.unpack() {
        // fresh type variable, ie. the type is completely unbounded.
        // treat this as equivalent to pri(all), which evaluates to f64.
        // (in other words, if there's nothing bounding a type, we choose it to be scalar f64).
        Var(i) if i == tv => Type::pri(Primitive::F64),
        Var(i) => canonty(sub, i),
        Pri(p) if p.len() > 1 => {
            let pri = (p & PRI_NUM).as_u16_truncated() as i16;
            Type::pri(EnumSet::from_u16_truncated((pri & -pri) as _))
        },
        Con(Constructor::TENSOR, base) => {
            canonty(sub, base);
            if sub[base+1] == Type::var(base+1) {
                sub[base+1] = Type::dim(0);
            }
            if canonty(sub, base+1) == Type::dim(0) {
                sub[base]
            } else {
                return ty;
            }
        },
        _ => return ty
    };
    sub[tv] = ty;
    ty
}

fn fixvars(tcx: &mut Tcx) {
    for idx in tcx.objs.keys() {
        if tcx.objs[idx].op == Obj::VAR {
            let ty = tcx.data.ann[&idx];
            canonty(&mut tcx.data.sub, zerocopy::transmute!(ty));
        }
    }
}

fn annotate(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    while let Some(i) = ccx.objs.next(idx) {
        idx = i;
        let op = ccx.objs[idx].op;
        if op == Obj::VAR || Operator::is_expr_raw(op) {
            let mut ann = ccx.data.ann[&idx];
            if op != Obj::VAR {
                ann = canonty(&mut ccx.data.sub, zerocopy::transmute!(ann));
            }
            let ann = typeobj(ccx, ann);
            let ofs = match op {
                Obj::VAR => obj_index_of!(VAR, ann),
                _ /* EXPR */ => obj_index_of!(EXPR, ann),
            };
            ccx.objs.get_raw_mut(idx)[ofs] = zerocopy::transmute!(ann);
        }
    }
}

impl Phase for TypeInfer {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(TypeInfer {
            sub: Default::default(),
            con: Default::default(),
            tobj: Default::default(),
            ann: Default::default(),
            tab: ObjRef::NIL.cast()
        })
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        ccx.freeze_graph(|ccx| {
            visitall(ccx);
            simplify(&mut ccx.data);
            fixvars(ccx);
            simplify(&mut ccx.data);
        });
        debug_assert!(ccx.data.con.is_empty());
        annotate(ccx);
        // TODO: check for errors
        if trace!(TYPE) {
            trace_objs(&ccx.intern, &ccx.objs, ObjRef::NIL);
        }
        Ok(())
    }

}

// use core::hash::Hasher;
// use core::iter::zip;
// 
// use alloc::vec::Vec;
// use enumset::EnumSet;
// use hashbrown::hash_table::Entry;
// use hashbrown::HashTable;
// use rustc_hash::FxHasher;
// 
// use crate::compile::{self, Ccx, Phase};
// use crate::dump::trace_objs;
// use crate::hash::HashMap;
// use crate::index::{self, index, IndexSlice, IndexVec};
// use crate::intrinsics::Intrinsic;
// use crate::obj::{obj_index_of, Obj, ObjRef, ObjectRef, Objects, Operator, CALLN, CALLX, EXPR, GET, KFP64, KINT, KINT64, LOAD, MOD, NEW, QUERY, TAB, TPRI, TTEN, TTUP, TUPLE, VAR, VGET, VSET};
// use crate::trace::trace;
// use crate::typestate::{Absent, Access, R};
// use crate::typing::{Constructor, Primitive, Scheme, SchemeBytecode, PRI_IDX, PRI_NUM};
// 
// index!(struct TypeVar(u32) debug("t{}"));
// 
// /*
//  *        +--------+--------+-------+------+
//  *        | 31..29 | 28..16 | 15..8 | 7..0 |
//  *        +========+========+=======+======+
//  * Var    |    0   |        typevar        |
//  *        +--------+----------------+------+
//  * Dim    |    1   |                |  dim |
//  *        +--------+--------+-------+------+
//  * Pri    |    2   |        |  pri enumset |
//  *        +--------+--------+--------------+
//  * Never  |    2   |           0           |
//  *        +--------+-----------------------+
//  * Con    |  3+con |         base          |
//  *        +--------+-----------------------+
//  */
// #[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
// #[repr(transparent)]
// struct Type(u32);
// 
// impl Type {
// 
//     const UNVISITED: Self = Self(!0);
//     const NEVER: Self = Self(2 << 29); // empty pri
//     const UNIT: Self = Self::con(Constructor::Unit as _, zerocopy::transmute!(0));
// 
//     fn var(tvar: TypeVar) -> Self {
//         zerocopy::transmute!(tvar)
//     }
// 
//     fn dim(dim: u8) -> Self {
//         Self((1 << 29) | (dim as u32))
//     }
// 
//     fn pri<P: Into<EnumSet<Primitive>>>(pri: P) -> Self {
//         Self((2 << 29) | pri.into().as_u32_truncated())
//     }
// 
//     const fn con(con: u8, base: TypeVar) -> Self {
//         let base: u32 = zerocopy::transmute!(base);
//         Self(((3+con as u32) << 29) | base)
//     }
// 
//     fn unpack(self) -> TypeRepr {
//         use TypeRepr::*;
//         debug_assert!(self != Self::UNVISITED);
//         match self.0 >> 29 {
//             0 => Var(zerocopy::transmute!(self.0)),
//             1 => Dim(self.0 as _),
//             2 => Pri(EnumSet::from_u16_truncated(self.0 as _)),
//             c => Con((c-3) as _, zerocopy::transmute!(self.0 & 0x1fffffff))
//         }
//     }
// 
// }
// 
// #[derive(Clone, Copy, Debug)]
// enum TypeRepr {
//     Var(TypeVar),
//     Con(u8, TypeVar),
//     Dim(u8),
//     Pri(EnumSet<Primitive>),
// }
// 
// pub struct TypeInfer {
//     tvar: IndexVec<TypeVar, Type>,
//     work: Vec<u32>, /* TypeVar, ObjRef */
//     typeobj: HashTable<ObjRef>,
//     tab: ObjRef<TAB> // table of current expression
// }
// 
// type Ctx<'a> = Ccx<TypeInfer, R<'a>>;
// 
// fn kintpri(v: i64) -> EnumSet<Primitive> {
//     use Primitive::*;
//     let mut pri = U64 | I64;
//     if v >= 0 { pri |= PTR }
//     if v == v as i8  as i64 { pri |= U8 | I8 };
//     if v == v as i16 as i64 { pri |= U16 | I16 };
//     if v == v as i32 as i64 { pri |= U32 | I32 };
//     if v == v as f32 as i64 { pri |= F32 };
//     if v == v as f64 as i64 { pri |= F64 };
//     pri
// }
// 
// fn kfpri(f: f64) -> EnumSet<Primitive> {
//     use Primitive::*;
//     let mut pri = F32 | F64;
//     if f == f as i8  as f64 { pri |= U8 | I8 };
//     if f == f as i16 as f64 { pri |= U16 | I16 };
//     if f == f as i32 as f64 { pri |= U32 | I32 };
//     if f == f as i64 as f64 { pri |= U64 | I64; if f >= 0.0 { pri |= PTR } };
//     pri
// }
// 
// fn newtypevar(tvar: &mut IndexVec<TypeVar, Type>) -> TypeVar {
//     tvar.push(Type::var(tvar.end()))
// }
// 
// fn newcontype(tvar: &mut IndexVec<TypeVar, Type>, con: Constructor, par: &[Type]) -> Type {
//     let base = tvar.end();
//     tvar.raw.extend_from_slice(par);
//     Type::con(con as _, base)
// }
// 
// fn newpairtype(tvar: &mut IndexVec<TypeVar, Type>, left: Type, right: Type) -> Type {
//     newcontype(tvar, Constructor::Pair, &[left, right])
// }
// 
// // must match hashtypeobj
// // stores type params in typeinfer.work
// fn hashtype(ccx: &mut Ccx<TypeInfer>, ty: TypeRepr) -> u64 {
//     use TypeRepr::*;
//     let mut hash = FxHasher::default();
//     match ty {
//         Pri(p) => hash.write_u16(p.as_u16_truncated()),
//         Con(Constructor::TENSOR, base) => {
//             let elem = typeobj(ccx, Type::var(base));
//             let TypeRepr::Dim(dim) = ccx.data.tvar[base+1].unpack() else { unreachable!() };
//             hash.write_u32(zerocopy::transmute!(elem));
//             hash.write_u8(dim);
//             ccx.data.work.push(zerocopy::transmute!(elem));
//             ccx.data.work.push(dim as _);
//         },
//         Con(Constructor::PAIR, mut t) => {
//             loop {
//                 let e = typeobj(ccx, Type::var(t));
//                 hash.write_u32(zerocopy::transmute!(e));
//                 ccx.data.work.push(zerocopy::transmute!(e));
//                 let TypeRepr::Con(c, tt) = ccx.data.tvar[t+1].unpack() else { unreachable!() };
//                 if c == Constructor::UNIT { break }
//                 t = tt;
//             }
//         },
//         Con(Constructor::UNIT, _) => { /* NOP */ },
//         _ => unreachable!()
//     }
//     hash.finish()
// }
// 
// // must match hashtype
// fn hashtypeobj(o: ObjectRef) -> u64 {
//     let mut hash = FxHasher::default();
//     match o {
//         ObjectRef::TPRI(&TPRI { ty, .. }) => hash.write_u16(1 << ty),
//         ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
//             hash.write_u32(zerocopy::transmute!(elem));
//             hash.write_u8(dim);
//         },
//         ObjectRef::TTUP(TTUP { elems, ..  }) => {
//             for &e in elems {
//                 hash.write_u32(zerocopy::transmute!(e));
//             }
//         },
//         _ => unreachable!()
//     }
//     hash.finish()
// }
// 
// fn sametype(a: ObjectRef, b: TypeRepr, work: &[u32]) -> bool {
//     match (a, b) {
//         (ObjectRef::TPRI(&TPRI { ty, .. }), TypeRepr::Pri(p)) => p.as_u16_truncated() == 1 << ty,
//         (ObjectRef::TTEN(&TTEN { elem, dim, .. }), TypeRepr::Con(Constructor::TENSOR, _))
//             => work == &[zerocopy::transmute!(elem), dim as _],
//         (ObjectRef::TTUP(TTUP { elems, .. }), TypeRepr::Con(Constructor::PAIR|Constructor::UNIT, _))
//             => work.len() == elems.len()
//             && zip(work.iter(), elems.iter()).all(|(&ea,&eb)| ea == zerocopy::transmute!(eb)),
//         _ => false
//     }
// }
// 
// fn createtypeobj(objs: &mut Objects, ty: TypeRepr, work: &[u32]) -> ObjRef {
//     use TypeRepr::*;
//     match ty {
//         Pri(p) => match p.into_iter().next() {
//             Some(ty) => objs.push(TPRI::new(ty as _)).erase(),
//             None => {
//                 // TODO: allow this and return ObjRef::NIL.
//                 // after creating all type objs, check that all *reachable* expressions
//                 // have a non-nil type.
//                 todo!();
//             }
//         }
//         Con(Constructor::TENSOR, _) => {
//             debug_assert!(work[1] > 0); // dim 0 tensor should be canonicalized to scalar
//             objs.push(TTEN::new(work[1] as _, zerocopy::transmute!(work[0]))).erase()
//         },
//         Con(Constructor::UNIT|Constructor::PAIR, _) => {
//             // XXX replace with zerocopy::transmute when it can do that
//             let work: &[ObjRef] = unsafe {
//                 core::slice::from_raw_parts(work.as_ptr().cast(), work.len())
//             };
//             objs.push_args::<TTUP>(TTUP::new(), work).erase()
//         }
//         _ => unreachable!()
//     }
// }
// 
// fn createtype(
//     objs: &Objects,
//     o2ty: &mut HashMap<ObjRef, Type>,
//     tvar: &mut IndexVec<TypeVar, Type>,
//     idx: ObjRef
// ) -> Type {
//     if let Some(&ty) = o2ty.get(&idx) {
//         return ty;
//     }
//     let ty = match objs.get(idx) {
//         ObjectRef::TVAR(_) => Type::var(newtypevar(tvar)),
//         ObjectRef::TPRI(&TPRI { ty, .. }) => Type::pri(EnumSet::from_u16_truncated(1 << ty)),
//         ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
//             let e = createtype(objs, o2ty, tvar, elem);
//             newcontype(tvar, Constructor::Tensor, &[e, Type::dim(dim)])
//         },
//         ObjectRef::TTUP(&TTUP { ref elems, .. }) => {
//             let mut ty = Type::UNIT;
//             for &e in elems.iter().rev() {
//                 let ety = createtype(objs, o2ty, tvar, e);
//                 ty = newpairtype(tvar, ety, ty);
//             }
//             ty
//         },
//         _ => unreachable!()
//     };
//     o2ty.insert_unique_unchecked(idx, ty);
//     ty
// }
// 
// fn totypevar(types: &mut IndexVec<TypeVar, Type>, ty: Type) -> TypeVar {
//     match ty.unpack() {
//         TypeRepr::Var(tv) => tv,
//         _ => types.push(ty)
//     }
// }
// 
// fn typeobj(ccx: &mut Ccx<TypeInfer>, ty: Type) -> ObjRef {
//     match ty.unpack() {
//         TypeRepr::Var(tv) => return typeobj(ccx, ccx.data.tvar[tv]),
//         type_ => {
//             let base = ccx.data.work.len();
//             let hash = hashtype(ccx, type_);
//             let tx = &mut *ccx.data;
//             let work = &tx.work[base..];
//             let o = match tx.typeobj.entry(
//                 hash,
//                 |&t| sametype(ccx.objs.get(t), type_, work),
//                 |&t| hashtypeobj(ccx.objs.get(t))
//             ) {
//                 Entry::Vacant(e) => *e.insert(createtypeobj(&mut ccx.objs, type_, work)).get(),
//                 Entry::Occupied(e) => *e.get()
//             };
//             tx.work.truncate(base);
//             o
//         }
//     }
// }
// 
// fn isconcretetype(tvar: &IndexSlice<TypeVar, Type>, ty: Type) -> bool {
//     use TypeRepr::*;
//     match ty.unpack() {
//         Var(j) if ty == Type::var(j) => false,
//         Var(j) => isconcretetype(tvar, tvar[j]),
//         Con(c, base) => (0..Constructor::from_u8(c).arity() as isize)
//             .all(|i| isconcretetype(tvar, tvar[base+i])),
//         Pri(p) => p.len() <= 1,
//         Dim(_) => true
//     }
// }
// 
// // set a=b
// fn unify(tvar: &mut IndexSlice<TypeVar, Type>, a: TypeVar, b: Type) {
//     use TypeRepr::*;
//     trace!(TYPE "unify {:?}:{:?} = {:?}", a, tvar[a].unpack(), b.unpack());
//     match (tvar[a].unpack(), b.unpack()) {
//         (Var(i), _) if i == a => tvar[a] = b,
//         (_, Var(j)) if j == a => { /* ok */ },
//         (Var(i), _) => unify(tvar, i, b),
//         (Pri(_), Pri(_)) => tvar[a].0 &= b.0,
//         (Pri(_), Var(j)) if matches!(tvar[j].unpack(), Pri(_)) => {
//             tvar[j].0 &= tvar[a].0;
//             tvar[a] = b;
//         },
//         (Pri(_), Var(j)) => unify(tvar, j, Type::var(a)),
//         (Pri(_), Con(Constructor::TENSOR, b0)) => {
//             unify(tvar, b0, Type::var(a));
//             unify(tvar, b0+1, Type::dim(0));
//         },
//         (Con(Constructor::TENSOR, a0), Pri(_)) => {
//             unify(tvar, a0, b);
//             unify(tvar, a0+1, Type::dim(0));
//         },
//         (Con(ca, ba), Con(cb, bb)) if ca == cb => {
//             for i in 0..Constructor::from_u8(ca).arity() as isize {
//                 unify(tvar, ba+i, Type::var(bb+i));
//             }
//         },
//         (Dim(i), Dim(j)) if i == j => { /* ok */ },
//         (_, Var(j)) => unify(tvar, j, tvar[a]),
//         _ => {
//             tvar[a] = Type::NEVER;
//             trace!(TYPE "***** {:?} = NEVER", a);
//         }
//     }
// }
// 
// #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
// #[repr(C)]
// struct ExprAnn {
//     expr: ObjRef<EXPR>,
//     ann: Type
// }
// 
// fn init(ccx: &mut Ccx<TypeInfer>) {
//     // pass 1: collect type objects
//     let mut o2ty: HashMap<ObjRef, Type> = Default::default();
//     for idx in ccx.objs.keys() {
//         if Operator::is_type_raw(ccx.objs[idx].op) {
//             let ty = createtype(&ccx.objs, &mut o2ty, &mut ccx.data.tvar, idx);
//             if isconcretetype(&ccx.data.tvar, ty) {
//                 if let Entry::Vacant(e) = ccx.data.typeobj.entry(
//                     hashtypeobj(ccx.objs.get(idx)),
//                     |&i| ccx.objs.equal(i, idx),
//                     |&i| hashtypeobj(ccx.objs.get(i))
//                 ) {
//                     e.insert(idx);
//                 }
//             }
//         }
//     }
//     // pass 2: patch type annotations
//     let mut idx = ObjRef::NIL;
//     let base = ccx.tmp.end();
//     while let Some(i) = ccx.objs.next(idx) {
//         idx = i;
//         match ccx.objs[idx].op {
//             op if Operator::is_expr_raw(op) => {
//                 let ann = ccx.objs[idx.cast::<EXPR>()].ann;
//                 let tv = ccx.data.tvar.push(Type::UNVISITED);
//                 trace!(TYPE "{:?} = {:?} EXPR", tv, idx);
//                 ccx.objs[idx.cast::<EXPR>()].ann = zerocopy::transmute!(tv);
//                 if !ann.is_nil() {
//                     // special case: TRUE and FALSE are KINT, but should get a boolean type
//                     // instead of a numeric type.
//                     if idx == ObjRef::TRUE.cast() || idx == ObjRef::FALSE.cast() {
//                         ccx.data.tvar[tv] = Type::pri(Primitive::B1);
//                     } else {
//                         ccx.tmp.push(ExprAnn { expr: idx.cast(), ann: o2ty[&ann] });
//                     }
//                 }
//             },
//             op if op == Operator::VAR as _ => {
//                 let ann = match ccx.objs[idx.cast::<VAR>()].ann {
//                     a if a == ObjRef::NIL => newtypevar(&mut ccx.data.tvar),
//                     a => totypevar(&mut ccx.data.tvar, o2ty[&a])
//                 };
//                 trace!(TYPE "{:?} = {:?} VAR", ann, idx);
//                 ccx.objs[idx.cast::<VAR>()].ann = zerocopy::transmute!(ann);
//             },
//             _ => {}
//         }
//     }
//     // apply annotations.
//     // this must be done only after all annotations are collected because unifyexpr depends
//     // on the annotation existing.
//     ccx.freeze_graph(|ctx| {
//         let mut ptr = base.cast_up();
//         let end = ctx.tmp.end().cast::<ExprAnn>();
//         while ptr < end {
//             let &ExprAnn { expr, ann } = &ctx.tmp[ptr];
//             unifyexpr(ctx, expr, ann);
//             ptr = ptr.add_size(1);
//         }
//     });
//     ccx.tmp.truncate(base);
// }
// 
// // set type(idx) = int|splat
// // return type(var[idx])
// fn vidxtype(ctx: &mut Ctx, var: ObjRef<VAR>, idx: &[ObjRef<EXPR>]) -> Type {
//     let need = ctx.objs.dim(ctx.objs[var].tab);
//     let mut have = idx.len();
//     if have < need {
//         // not enough indices mentioned, insert current expression's index.
//         // these are scalar indices, so they don't increase the dimension.
//         // if this results in too many indices being mentioned, it's a type error.
//         have += ctx.objs.dim(ctx.data.tab);
//     }
//     if have > need {
//         // too many indices mentioned.
//         return Type::NEVER;
//     }
//     // any missing dimension is an implicit splat
//     let mut dims = need - have;
//     for &i in idx.iter() {
//         let EXPR { op, data, .. } = ctx.objs[i];
//         let ity = if (op, data) == (Obj::CALLN, Intrinsic::SPREAD as _) {
//             dims += 1;
//             newcontype(&mut ctx.data.tvar, Constructor::Tensor, &[Type::pri(PRI_IDX), Type::dim(1)])
//         } else {
//             Type::pri(PRI_IDX)
//         };
//         unifyexpr(ctx, i, ity);
//     }
//     let mut vty: Type = zerocopy::transmute!(ctx.objs[var].ann);
//     if dims > 0 {
//         vty = newcontype(&mut ctx.data.tvar, Constructor::Tensor, &[vty, Type::dim(dims as _)]);
//     }
//     vty
// }
// 
// // note: this assumes Type::var and TypeVar have the same representation
// fn instantiate(scheme: &Scheme, tvar: &mut IndexVec<TypeVar, Type>, work: &mut Vec<u32>) -> Type {
//     let base = tvar.end();
//     for _ in 0..scheme.num_generics() {
//         newtypevar(tvar);
//     }
//     for &ins in scheme.bytecode() {
//         match SchemeBytecode::decode(ins) {
//             SchemeBytecode::Con(con) => {
//                 let base = tvar.end();
//                 let n = con.arity() as usize;
//                 tvar.raw.extend(work[work.len()-n..].iter().cloned().map(Type));
//                 work.truncate(work.len()-n);
//                 work.push(zerocopy::transmute!(Type::con(con as _, base)));
//             },
//             SchemeBytecode::Pri(pri) => {
//                 let tv: TypeVar = zerocopy::transmute!(work.pop().unwrap());
//                 unify(tvar, tv, Type::pri(pri));
//             },
//             SchemeBytecode::Gen(idx) => {
//                 work.push(zerocopy::transmute!(base + idx as isize));
//             }
//         }
//     }
//     debug_assert!(work.len() == 1);
//     zerocopy::transmute!(work.pop().unwrap())
// }
// 
// fn unifytuple(ctx: &mut Ctx, elems: &[ObjRef<EXPR>]) -> Type {
//     let mut ty = Type::UNIT;
//     for &e in elems.iter().rev() {
//         let t = Type::var(newtypevar(&mut ctx.data.tvar));
//         unifyexpr(ctx, e, t);
//         ty = newpairtype(&mut ctx.data.tvar, t, ty);
//     }
//     ty
// }
// 
// // set type(expr) = ty
// fn unifyexpr(ctx: &mut Ctx, idx: ObjRef<EXPR>, ty: Type) {
//     let objs = Access::borrow(&ctx.objs);
//     let tv: TypeVar = zerocopy::transmute!(objs[idx].ann);
//     if ctx.data.tvar[tv] != Type::UNVISITED {
//         unify(&mut ctx.data.tvar, tv, ty);
//         return;
//     }
//     trace!(TYPE "expr  {:?} = {:?}", tv, ty.unpack());
//     ctx.data.tvar[tv] = ty;
//     match objs.get(idx.erase()) {
//         ObjectRef::KINT(&KINT { k, .. }) => unify(&mut ctx.data.tvar, tv,
//             Type::pri(kintpri(k as _))),
//         ObjectRef::KINT64(&KINT64 { k, .. }) => unify(&mut ctx.data.tvar, tv,
//             Type::pri(kintpri(ctx.intern.bump()[k].get()))),
//         ObjectRef::KFP64(&KFP64 { k, .. }) => unify(&mut ctx.data.tvar, tv,
//             Type::pri(kfpri(ctx.intern.bump()[k].get()))),
//         ObjectRef::KSTR(_) => unify(&mut ctx.data.tvar, tv, Type::pri(Primitive::STR)),
//         ObjectRef::DIM(_) => unify(&mut ctx.data.tvar, tv, Type::pri(PRI_IDX)),
//         ObjectRef::TUPLE(&TUPLE { ref fields, .. }) => {
//             let tt = unifytuple(ctx, fields);
//             unify(&mut ctx.data.tvar, tv, tt);
//         },
//         ObjectRef::VGET(&VGET { var, ref idx, .. }) => {
//             let vty = vidxtype(ctx, var, idx);
//             unify(&mut ctx.data.tvar, tv, vty);
//         },
//         ObjectRef::CAT(_) => {
//             // TODO: this should produce an (n+1)-dimensional tensor from a list of n-dimensional
//             // tensors. but the current unification cannot express this.
//             // dims should be represented as constructors, ie.
//             //   dim1 = next(dim0),
//             //   dim2 = next(dim1),
//             // etc. which makes it possible to express
//             //   (t,n) : tensor(t, n) -> tensor(t, next(n))
//             todo!()
//         },
//         ObjectRef::IDX(_) => todo!(),
//         ObjectRef::LOAD(&LOAD { addr, ref shape, .. }) => {
//             unifyexpr(ctx, addr, Type::pri(Primitive::PTR));
//             for &d in shape {
//                 // TODO: this should support all types of integers, but currently lower
//                 // assumes all lengths are IRT_IDX (this is hardcoded in return slots).
//                 // this should probably convert to IRT_IDX because there's not much benefit
//                 // in supporting other length sizes.
//                 unifyexpr(ctx, d, Type::pri(PRI_IDX));
//             }
//             // result type annotation is generated by parser, no need to unify it here.
//         },
//         ObjectRef::NEW(NEW { shape, .. }) => {
//             for &s in shape {
//                 // nb. see TODO comment in LOAD
//                 unifyexpr(ctx, s, Type::pri(PRI_IDX));
//             }
//         },
//         ObjectRef::GET(&GET { value, idx, .. }) => {
//             let mut tt = newpairtype(&mut ctx.data.tvar, Type::var(tv), Type::UNIT);
//             for _ in 0..idx {
//                 let t = newtypevar(&mut ctx.data.tvar);
//                 tt = newpairtype(&mut ctx.data.tvar, Type::var(t), tt);
//             }
//             unifyexpr(ctx, value, tt);
//         },
//         ObjectRef::FREF(_) => todo!(),
//         ObjectRef::CALL(_) => todo!(),
//         ObjectRef::CALLN(&CALLN { func, ref args, .. }) => {
//             let tx = &mut *ctx.data;
//             let sig = instantiate(Intrinsic::from_u8(func).scheme(), &mut tx.tvar, &mut tx.work);
//             let TypeRepr::Con(_, base) = sig.unpack() else { unreachable!() };
//             let at = unifytuple(ctx, args);
//             unify(&mut ctx.data.tvar, base, at);
//             unify(&mut ctx.data.tvar, base+1, Type::var(tv));
//         },
//         ObjectRef::CALLX(&CALLX { ref inputs, .. }) => {
//             for &input in inputs {
//                 let ty: TypeVar = zerocopy::transmute!(objs[input].ann);
//                 if ctx.data.tvar[ty] == Type::UNVISITED {
//                     unifyexpr(ctx, input, Type::var(ty));
//                 }
//             }
//         },
//         _ => unreachable!()
//     }
// }
// 
// fn maketabtype(ctx: &mut Ctx, dims: u8) -> Type {
//     let tvar = &mut ctx.data.tvar;
//     let mut ty = Type::UNIT;
//     for _ in 0..dims {
//         let base = tvar.end();
//         tvar.push(Type::pri(PRI_IDX)); // elem
//         newtypevar(tvar); // dim
//         ty = newpairtype(tvar, Type::con(Constructor::Tensor as _, base), ty);
//     }
//     ty
// }
// 
// fn infertoplevel(ctx: &mut Ctx) {
//     let objs = Access::borrow(&ctx.objs);
//     for (_, o) in objs.pairs() {
//         match o {
//             ObjectRef::TAB(&TAB { shape, .. }) => {
//                 ctx.data.tab = ObjRef::GLOBAL;
//                 let dims = ctx.objs[shape].fields.len();
//                 let ty = maketabtype(ctx, dims as _);
//                 unifyexpr(ctx, shape.cast(), ty);
//             },
//             ObjectRef::MOD(&MOD { tab, guard, ref value, .. }) => {
//                 ctx.data.tab = tab;
//                 if !guard.is_nil() {
//                     unifyexpr(ctx, guard, Type::pri(Primitive::B1));
//                 }
//                 for &vset in value.iter() {
//                     let &VSET { var, value, ref idx, .. } = &objs[vset];
//                     let vty = vidxtype(ctx, var, idx);
//                     unifyexpr(ctx, value, vty);
//                 }
//             },
//             ObjectRef::FUNC(_) => todo!(),
//             ObjectRef::QUERY(&QUERY { tab, ref value, .. }) => for &v in value {
//                 ctx.data.tab = tab;
//                 let ann: TypeVar = zerocopy::transmute!(objs[v].ann);
//                 debug_assert!(ctx.data.tvar[ann] == Type::UNVISITED);
//                 unifyexpr(ctx, v, Type::var(ann));
//             },
//             _ => {}
//         }
//     }
// }
// 
// // * eliminate type variables
// // * multi pri => widest type
// // * tensor<t, 0> => t
// fn canonty(tvar: &mut IndexVec<TypeVar, Type>, tv: TypeVar) -> Type {
//     use TypeRepr::*;
//     let mut ty = tvar[tv];
//     ty = match ty {
//         Type::UNVISITED => {
//             // unvisited is ok here for orphaned expression (ie. those created from the api but
//             // never used in a query etc)
//             // their type doesn't matter because they don't get codegen'd.
//             // this assigns them to NEVER, ie. empty pri set.
//             // actually attempting to use them will assert later, just like other NEVER types.
//             Type::NEVER
//         },
//         ty => match ty.unpack() {
//             // fresh type variable, ie. the type is completely unbounded.
//             // treat this as equivalent to pri(all), which evaluates to f64.
//             // (in other words, if there's nothing bounding a type, we choose it to be scalar f64).
//             Var(i) if i == tv => Type::pri(Primitive::F64),
//             Var(i) => canonty(tvar, i),
//             Pri(p) if p.len() > 1 => {
//                 let pri = (p & PRI_NUM).as_u16_truncated() as i16;
//                 Type::pri(EnumSet::from_u16_truncated((pri & -pri) as _))
//             },
//             // hack: unset dim is canonicalized as f64, treat unset dim as zero here.
//             Con(Constructor::TENSOR, base) if {
//                 let c = canonty(tvar, base+1);
//                 c == Type::dim(0) || c == Type::pri(Primitive::F64)
//             } => canonty(tvar, base),
//             _ => return ty
//         }
//     };
//     tvar[tv] = ty;
//     ty
// }
// 
// fn canonicalize(types: &mut IndexVec<TypeVar, Type>) {
//     for tv in index::iter_span(types.end()) {
//         let ty = canonty(types, tv);
//         crate::trace::trace!(TYPE "canon {:?} = {:?}", tv, ty.unpack());
//     }
// }
// 
// fn setannotations(ccx: &mut Ccx<TypeInfer>) {
//     let mut idx = ObjRef::NIL;
//     while let Some(i) = ccx.objs.next(idx) {
//         idx = i;
//         let ofs = match ccx.objs[idx].op {
//             Obj::VAR => obj_index_of!(VAR, ann),
//             op if Operator::is_expr_raw(op) => obj_index_of!(EXPR, ann),
//             _ => continue
//         };
//         let ann: Type = zerocopy::transmute!(ccx.objs.get_raw(idx)[ofs]);
//         let ann = typeobj(ccx, ann);
//         ccx.objs.get_raw_mut(idx)[ofs] = zerocopy::transmute!(ann);
//     }
// }
// 
// impl Phase for TypeInfer {
// 
//     fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
//         Ok(TypeInfer {
//             tvar: Default::default(),
//             work: Default::default(),
//             typeobj: Default::default(),
//             tab: ObjRef::NIL.cast()
//         })
//     }
// 
//     fn run(ccx: &mut Ccx<Self>) -> compile::Result {
//         init(ccx);
//         ccx.freeze_graph(infertoplevel);
//         canonicalize(&mut ccx.data.tvar);
//         setannotations(ccx);
//         // TODO: check here that all reachable expressions have a non-NEVER type.
//         // (unreachable expressions will always have the NEVER type)
//         if trace!(TYPE) {
//             trace_objs(&ccx.intern, &ccx.objs, ObjRef::NIL);
//         }
//         Ok(())
//     }
// 
// }
