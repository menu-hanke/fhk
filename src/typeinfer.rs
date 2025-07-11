//! Type inference.

use core::cmp::min;
use core::fmt::Debug;
use core::hash::Hasher;
use core::iter::zip;
use core::mem::replace;

use alloc::collections::vec_deque::VecDeque;
use enumset::{enum_set, EnumSet};
use hashbrown::{hash_map, hash_table, HashTable};
use rustc_hash::FxHasher;

use crate::compile::{self, Ccx, Stage};
use crate::dump::trace_objs;
use crate::hash::HashMap;
use crate::index::{index, IndexSlice, IndexVec};
use crate::obj::{obj_index_of, BinOp, Intrinsic, LocalId, Obj, ObjRef, ObjectRef, Objects, Operator, BINOP, CALLX, CAT, EXPR, FLAT, GET, INTR, KFP64, KINT, KINT64, LEN, LET, LGET, LOAD, MOD, NEW, QUERY, SPEC, SPLAT, TAB, TPRI, TTEN, TTUP, TUPLE, VAR, VGET, VSET};
use crate::trace::trace;
use crate::typestate::{Absent, Access, R};
use crate::typing::{Constructor, Primitive, PRI_IDX};

index!(struct TypeVar(u32) debug("t{}"));

// ORDER BUILTINTYPE
impl TypeVar {
    const UNIT: Self = zerocopy::transmute!(0);
    const V1D: Self = zerocopy::transmute!(1);
}

/*
 *        +--------+--------+-------+------+
 *        | 31..29 | 28..16 | 15..8 | 7..0 |
 *        +========+========+=======+======+
 * Var    |    0   |        typevar        |
 *        +--------+--------+--------------+
 * Pri    |    1   |        |  pri enumset |
 *        +--------+--------+--------------+
 * Never  |    1   |           0           |
 *        +--------+-----------------------+
 * Con    |  2+con |         base          |
 *        +--------+-----------------------+
 */
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct Type(u32);

impl Type {

    const NEVER: Self = Self(1 << 29); // empty pri
    const UNIT: Self = Self::con(Constructor::Unit as _, TypeVar::UNIT);
    const V1D: Self = Self::con(Constructor::Next as _, TypeVar::UNIT);

    fn var(tvar: TypeVar) -> Self {
        zerocopy::transmute!(tvar)
    }

    fn pri<P: Into<EnumSet<Primitive>>>(pri: P) -> Self {
        Self((1 << 29) | pri.into().as_u32_truncated())
    }

    const fn con(con: u8, base: TypeVar) -> Self {
        let base: u32 = zerocopy::transmute!(base);
        Self(((2+con as u32) << 29) | base)
    }

    fn unpack(self) -> TypeRepr {
        use TypeRepr::*;
        match self.0 >> 29 {
            0 => Var(zerocopy::transmute!(self.0)),
            1 => Pri(EnumSet::from_u16_truncated(self.0 as _)),
            c => Con((c-2) as _, zerocopy::transmute!(self.0 & 0x1fffffff))
        }
    }

}

#[derive(Clone, Copy)]
enum TypeRepr {
    Var(TypeVar),
    Pri(EnumSet<Primitive>),
    Con(u8, TypeVar),
}

impl Debug for TypeRepr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use TypeRepr::*;
        match *self {
            Var(v) => v.fmt(f),
            Pri(p) => p.fmt(f),
            Con(Constructor::TENSOR, base) => write!(f, "{:?}[{:?}]", base, base+1),
            Con(Constructor::PAIR, base) => write!(f, "({:?}, {:?})", base, base+1),
            // Con(Constructor::FUNC, base) => write!(f, "{:?} -> {:?}", base, base+1),
            Con(Constructor::NEXT, base) => write!(f, "{:?}+1", base),
            Con(Constructor::UNIT, _) => f.write_str("()"),
            _ => unreachable!()
        }
    }
}

enum Constraint {
    BinOp(TypeVar, TypeVar, TypeVar), // a:dim, b:dim, c:dim :: a = b ∘ c
    Index(TypeVar, Type, TypeVar),    // b:tensor, c:dim :: a = b[c]
}

pub struct TypeInfer {
    sub: IndexVec<TypeVar, Type>,
    locals: IndexVec<LocalId, TypeVar>,
    con: VecDeque<Constraint>,
    tobj: HashTable<ObjRef>,
    tab: ObjRef<TAB>,
    dim: (TypeVar, u8)
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

fn newpairlist(sub: &mut IndexVec<TypeVar, Type>, fields: &[Type]) -> Type {
    let mut ty = Type::UNIT;
    for &f in fields.iter().rev() {
        ty = newpairtype(sub, f, ty);
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
            unifyvar(sub, b0+1, Type::UNIT);
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
        (Con(Constructor::TENSOR, d), Pri(p)) | (Pri(p), Con(Constructor::TENSOR, d)) => {
            unifyvar(sub, d, Type::pri(p));
            unifyvar(sub, d+1, Type::UNIT);
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

fn equal(sub: &IndexSlice<TypeVar, Type>, a: Type, b: Type) -> Option<bool> {
    use TypeRepr::*;
    if a == b { return Some(true) }
    match (a.unpack(), b.unpack()) {
        (Var(i), _) if sub[i] == a => None,
        (Var(i), _) => equal(sub, sub[i], b),
        (_, Var(j)) => equal(sub, sub[j], a),
        (Pri(p), Pri(q)) => match (p&q).len() {
            0 => Some(false),
            1 => Some(true),
            _ => None
        },
        (Con(Constructor::TENSOR, d), Pri(p)) | (Pri(p), Con(Constructor::TENSOR, d)) => {
            match equal(sub, Type::var(d), Type::pri(p)) {
                Some(true) => equal(sub, Type::var(d+1), Type::UNIT),
                r => r
            }
        },
        (Con(ca, ba), Con(cb, bb)) if ca == cb => {
            for i in 0..Constructor::from_u8(ca).arity() as isize {
                match equal(sub, Type::var(ba+i), Type::var(bb+i)) {
                    Some(true) => {},
                    r => return r
                }
            }
            Some(true)
        },
        _ => Some(false)
    }
}

fn unpacktensor(sub: &mut IndexVec<TypeVar, Type>, ten: Type) -> (TypeVar, TypeVar) {
    use TypeRepr::*;
    match ten.unpack() {
        Con(Constructor::TENSOR, base) => (base, base+1),
        Var(i) if sub[i] != Type::var(i) && !matches!(sub[i].unpack(), Pri(_))
            => unpacktensor(sub, sub[i]),
        _ => {
            let e = newtypevar(sub);
            let d = newtypevar(sub);
            unify(sub, ten, Type::con(Constructor::TENSOR, e));
            (e, d)
        }
    }
}

fn shallowdimension(sub: &IndexSlice<TypeVar, Type>, ty: Type) -> Option<Type> {
    use TypeRepr::*;
    match ty.unpack() {
        Var(i) if sub[i] == ty => None,
        Var(i) => shallowdimension(sub, sub[i]),
        Con(Constructor::TENSOR, base) => shallowdimension(sub, Type::var(base+1)),
        Con(Constructor::NEXT, _) => Some(ty),
        _ => Some(Type::UNIT)
    }
}

fn dimension(sub: &IndexSlice<TypeVar, Type>, ty: Type) -> Option<u8> {
    match shallowdimension(sub, ty) {
        Some(Type::UNIT) => Some(0),
        Some(next) => {
            let TypeRepr::Con(_, prev) = next.unpack() else { unreachable!() };
            match dimension(sub, sub[prev]) {
                Some(d) => Some(d+1),
                None => None
            }
        },
        None => None
    }
}

fn simplify_binop(
    sub: &mut IndexSlice<TypeVar, Type>,
    a: TypeVar,
    b: TypeVar,
    c: TypeVar
) -> bool {
    match (
        shallowdimension(sub, Type::var(a)),
        shallowdimension(sub, Type::var(b)),
        shallowdimension(sub, Type::var(c)),
    ) {
        (_, Some(Type::UNIT), _) => {
            // scalar lhs -> output is rhs
            unifyvar(sub, a, Type::var(c));
            true
        },
        (_, _, Some(Type::UNIT)) => {
            // scalar rhs -> output is lhs
            unifyvar(sub, a, Type::var(b));
            true
        },
        (Some(Type::UNIT), _, _) | (_, Some(_), Some(_)) => {
            // scalar output -> scalar inputs
            // two tensor inputs -> tensor output
            unifyvar(sub, a, Type::var(b));
            unifyvar(sub, a, Type::var(c));
            true
        }
        _ => false
    }
}

fn simplify_index(
    sub: &mut IndexVec<TypeVar, Type>,
    a: TypeVar,
    b: Type,
    c: TypeVar
) -> bool {
    match (
        shallowdimension(sub, Type::var(a)),
        shallowdimension(sub, b),
        shallowdimension(sub, Type::var(c))
    ) {
        (Some(Type::UNIT), _, _) => {
            // output is scalar -> we are indexing a 1-d tensor with a scalar
            let (e, d) = unpacktensor(sub, b);
            unifyvar(sub, e, Type::var(a));
            unifyvar(sub, d, Type::V1D);
            unifyvar(sub, c, Type::UNIT);
            true
        },
        (Some(_), _, Some(Type::UNIT)) => {
            // output is n-d tensor and index is scalar -> we are indexing an (n+1)-d tensor
            let (eb, db) = unpacktensor(sub, b);
            let (ea, da) = unpacktensor(sub, Type::var(a));
            unifyvar(sub, eb, Type::var(ea));
            unifyvar(sub, db, Type::con(Constructor::NEXT, da));
            true
        },
        (_, _, Some(d)) if d != Type::UNIT => {
            // index is tensor -> we are indexing an n-d tensor with a 1-d tensor
            unifyvar(sub, a, b);
            unifyvar(sub, c, Type::V1D);
            true
        },
        (Some(da), Some(db), _) if match equal(sub, da, db) {
            Some(true) => {
                // input and output have same dimension -> indexing with a 1-d tensor
                unifyvar(sub, a, b);
                unifyvar(sub, c, Type::V1D);
                true
            },
            Some(false) => {
                // input and output have different dimensions, and output is known to be a tensor
                // -> scalar index of n-d tensor (n>1) -> tensor result
                let (ea, da) = unpacktensor(sub, Type::var(a));
                let (eb, db) = unpacktensor(sub, b);
                unifyvar(sub, eb, Type::var(ea));
                unifyvar(sub, db, Type::con(Constructor::NEXT, da));
                unifyvar(sub, c, Type::UNIT);
                true
            },
            None => false
        } => true,
        (_, Some(db), Some(Type::UNIT)) if match shallowdimension(sub, db) {
            Some(ddb) => match shallowdimension(sub, ddb) {
                Some(Type::UNIT) => {
                    // scalar index of 1-d tensor -> scalar result.
                    let (eb, _) = unpacktensor(sub, b);
                    unifyvar(sub, a, Type::var(eb));
                    true
                },
                Some(_) => {
                    // scalar index of n-d tensor (n>1) -> tensor result.
                    let (ea, da) = unpacktensor(sub, Type::var(a));
                    let (eb, db) = unpacktensor(sub, b);
                    unifyvar(sub, eb, Type::var(ea));
                    unifyvar(sub, db, Type::con(Constructor::NEXT, da));
                    true
                },
                None => false
            },
            None => false
        } => true,
        _ => false
    }
}

fn constraint(ctx: &mut TypeInfer, con: Constraint) -> bool {
    if match con {
        Constraint::BinOp(a, b, c) => simplify_binop(&mut ctx.sub, a, b, c),
        Constraint::Index(a, b, c) => simplify_index(&mut ctx.sub, a, b, c),
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

fn createdimtype(ts: &mut TypeInfer, dim: u8) -> Type {
    let (mut tv, mut d) = ts.dim;
    while dim < d {
        let TypeRepr::Con(_, prev) = ts.sub[tv].unpack() else { unreachable!() };
        tv = prev;
        d -= 1;
    }
    while dim > d {
        tv = ts.sub.push(Type::con(Constructor::NEXT, tv));
        d += 1;
    }
    ts.dim = (tv, d);
    ts.sub[tv]
}

fn visitvref(tcx: &mut Tcx, var: ObjRef<VAR>, idx: &[ObjRef<EXPR>], mut have: usize) -> Type {
    let objs = Access::borrow(&tcx.objs);
    let axes = &objs[objs[objs[var].tab].shape].fields;
    let need = axes.len();
    if have > need {
        // too many indices mentioned.
        return Type::NEVER;
    }
    let prefix = min(objs.dim(tcx.data.tab), need-have);
    have += prefix;
    let mut ty = Type::var(zerocopy::transmute!(objs[var].ann));
    let mut dim = 0;
    if have < need {
        for i in (have..need).rev() {
            dim += 1;
            if i > 0 && axes[i-1].is_nil() {
                // vector axis or end of tail
                let d = createdimtype(&mut tcx.data, dim as _);
                ty = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, d]);
                dim = 0;
            }
        }
    }
    if idx.iter().all(|&i| objs[i].op == Obj::FLAT) {
        // special case: exact dimension known
        dim += idx.len();
        for &e in idx {
            visitexpr(tcx, e);
        }
        if dim > 0 {
            let d = createdimtype(&mut tcx.data, dim as _);
            ty = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, d]);
        }
        ty
    } else {
        // general case: index expression with non-flat indices.
        // here the dimensionality depends on the dimension of the non-flat index expressions.
        // what we do here is:
        // * start from `v_0 = tensor(T, N)`, where `T` is the type of the variable and `N` is the
        //   number of axes after the implicit prefix.
        // * every explicit index `e_0, ..., e_k` gets a constraint:
        //     Index(v_{j+1}, v_j, e_j)
        // * every flat index `(f_1, ..., f_m)` flattens the result type by `m-1` dimensions.
        debug_assert!(need > prefix);
        let d = createdimtype(&mut tcx.data, (need-prefix) as _);
        let mut v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, d]);
        for &e in idx {
            match objs[e].op {
                Obj::SPEC if objs[e].data == SPEC::NIL => continue,
                Obj::SPEC if objs[e].data == SPEC::SLURP => {
                    // dimension can't go to zero here because this is always followed by an
                    // explicit index, so we don't need a constraint.
                    let (_, dim) = unpacktensor(&mut tcx.data.sub, v);
                    let dim = newcontype(&mut tcx.data.sub, Constructor::Next, &[Type::var(dim)]);
                    v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, dim]);
                },
                Obj::FLAT => {
                    // dimension can't go to zero here because this behaves like a 1D tensor index,
                    // so we don't need a constraint.
                    visitexpr(tcx, e);
                    let m = objs[e.cast::<FLAT>()].idx.len();
                    if m > 1 {
                        let (_, dim) = unpacktensor(&mut tcx.data.sub, v);
                        let mut dim = Type::var(dim);
                        for _ in 1..m {
                            dim = newcontype(&mut tcx.data.sub, Constructor::Next, &[dim]);
                        }
                        v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, dim]);
                    }
                },
                _ => {
                    let ety = visitexpr(tcx, e);
                    let (elem, edim) = unpacktensor(&mut tcx.data.sub, Type::var(ety));
                    unifyvar(&mut tcx.data.sub, elem, Type::pri(PRI_IDX));
                    let vnext = newtypevar(&mut tcx.data.sub);
                    constraint(&mut tcx.data, Constraint::Index(vnext, v, edim));
                    v = Type::var(vnext);
                }
            }
        }
        // increment dimension if we have implicit dimensions
        if dim > 0 {
            let vdim = newtypevar(&mut tcx.data.sub);
            let vten = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, Type::var(vdim)]);
            unify(&mut tcx.data.sub, vten, v);
            let mut rdim = Type::con(Constructor::NEXT, vdim);
            for _ in 0..dim {
                rdim = newcontype(&mut tcx.data.sub, Constructor::Next, &[rdim]);
            }
            let rdim = tcx.data.sub.push(rdim);
            v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, Type::var(rdim)]);
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
        let ety = visitexpr(tcx, a);
        tcx.tmp.push(ety);
    }
    let aty: &[TypeVar] = &tcx.tmp[base.cast_up()..];
    macro_rules! I { ($($t:tt)*) => { instantiate!(tcx, aty; $($t)*) }; }
    let ty = match func {
        UNM | EXP | LOG => I!(a,e n :: a[Tensor e n], e[pri PRI_NUM] => a),
        NOT => I!(a,n :: a[Tensor Type::pri(Primitive::B1) n] => a),
        SUM => I!(a,e n :: a[Tensor e n], e[pri PRI_NUM] => e),
        // TODO (?): generalize WHICH to return tuples.
        WHICH => I!(a :: a[Tensor Type::pri(Primitive::B1) Type::V1D]
            => Tensor Type::pri(PRI_IDX) Type::V1D),
        ANY | ALL => I!(a,n :: a[Tensor Type::pri(Primitive::B1) n] => pri Primitive::B1),
        CONV => I!(a,b e n :: a[Tensor e n] => Tensor b n),
        REP => I!(a,e n m :: a[Tensor e n] => Tensor e m),
    };
    tcx.tmp.truncate(base);
    ty
}

fn visitexpr(tcx: &mut Tcx, idx: ObjRef<EXPR>) -> TypeVar {
    let objs = Access::borrow(&tcx.objs);
    let tv: TypeVar = zerocopy::transmute!(objs[idx].ann);
    if idx.is_builtin() {
        // skip for KINT logic for TRUE and FALSE
        return tv;
    }
    let ty = match objs.get(idx.erase()) {
        ObjectRef::SPEC(_) => Some(Type::UNIT),
        ObjectRef::SPLAT(&SPLAT { value, .. }) => Some(Type::var(visitexpr(tcx, value))),
        ObjectRef::FLAT(FLAT { idx, .. }) => {
            for &i in idx {
                if objs[i].op != Obj::SPEC {
                    let ety = visitexpr(tcx, i);
                    let (e, _) = unpacktensor(&mut tcx.data.sub, Type::var(ety));
                    unifyvar(&mut tcx.data.sub, e, Type::pri(PRI_IDX));
                }
            }
            Some(Type::UNIT)
        },
        ObjectRef::KINT(&KINT { k, .. }) => Some(Type::pri(kintpri(k as _))),
        ObjectRef::KINT64(&KINT64 { k, .. }) => Some(Type::pri(kintpri(tcx.intern.bump()[k].get()))),
        ObjectRef::KFP64(&KFP64 { k, .. }) => Some(Type::pri(kfpri(tcx.intern.bump()[k].get()))),
        ObjectRef::KSTR(_) => Some(Type::pri(Primitive::STR)),
        ObjectRef::DIM(_) => Some(Type::pri(PRI_IDX)),
        ObjectRef::LEN(&LEN { value, .. }) => {
            // TODO: make sure here that it has at least as many dimensions as our axis.
            let _ety = visitexpr(tcx, value);
            Some(Type::pri(PRI_IDX))
        },
        ObjectRef::TUPLE(TUPLE { fields, .. }) => {
            let mut ty = Type::UNIT;
            for &e in fields.iter().rev() {
                let ety = visitexpr(tcx, e);
                ty = newpairtype(&mut tcx.data.sub, Type::var(ety), ty);
            }
            Some(ty)
        },
        ObjectRef::LET(&LET { value, expr, .. }) => {
            let vty = visitexpr(tcx, value);
            tcx.data.locals.push(vty);
            let ety = visitexpr(tcx, expr);
            tcx.data.locals.raw.pop();
            Some(Type::var(ety))
        },
        ObjectRef::LGET(&LGET { slot, .. }) => Some(Type::var(tcx.data.locals[slot])),
        ObjectRef::VGET(&VGET { dim, var, ref idx, .. }) => Some(visitvref(tcx, var, idx, dim as _)),
        ObjectRef::CAT(CAT { elems, .. } ) => {
            let e = newtypevar(&mut tcx.data.sub);
            let d = newtypevar(&mut tcx.data.sub);
            let ty = Type::con(Constructor::TENSOR, e);
            for &v in elems {
                let ety = visitexpr(tcx, v);
                if objs[v].op == Obj::SPLAT {
                    unifyvar(&mut tcx.data.sub, ety, ty);
                } else {
                    let (ee, ed) = unpacktensor(&mut tcx.data.sub, Type::var(ety));
                    unifyvar(&mut tcx.data.sub, e, Type::var(ee));
                    unifyvar(&mut tcx.data.sub, d, Type::con(Constructor::NEXT, ed));
                }
            }
            Some(ty)
        },
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(&LOAD { addr, ref shape, .. }) => {
            let aty = visitexpr(tcx, addr);
            unify(&mut tcx.data.sub, Type::var(aty), Type::pri(Primitive::PTR));
            for &d in shape {
                // TODO: this should support all types of integers, but currently lower
                // assumes all lengths are IRT_IDX (this is hardcoded in return slots).
                // this should probably convert to IRT_IDX because there's not much benefit
                // in supporting other length sizes.
                let dty = visitexpr(tcx, d);
                unify(&mut tcx.data.sub, Type::var(dty), Type::pri(PRI_IDX));
            }
            // result type annotation is generated by parser
            None
        },
        ObjectRef::NEW(NEW { shape, .. }) => {
            for &s in shape {
                // nb. see TODO comment in LOAD
                let sty = visitexpr(tcx, s);
                unify(&mut tcx.data.sub, Type::var(sty), Type::pri(PRI_IDX));
            }
            let elem = newtypevar(&mut tcx.data.sub);
            let dim = createdimtype(&mut tcx.data, shape.len() as _);
            Some(newcontype(&mut tcx.data.sub, Constructor::Tensor, &[Type::var(elem), dim]))
        },
        ObjectRef::GET(&GET { value, mut idx, .. }) => {
            let mut vty = visitexpr(tcx, value);
            loop {
                let e = newtypevar(&mut tcx.data.sub);
                let next = newtypevar(&mut tcx.data.sub);
                let repr = newpairtype(&mut tcx.data.sub, Type::var(e), Type::var(next));
                unifyvar(&mut tcx.data.sub, vty, repr);
                match idx {
                    0 => break Some(Type::var(e)),
                    _ => {
                        idx -= 1;
                        vty = next;
                    }
                }
            }
        },
        ObjectRef::BINOP(&BINOP { binop, left, right, .. }) => {
            use BinOp::*;
            let td = newtypevar(&mut tcx.data.sub);
            let lty = visitexpr(tcx, left);
            let rty = visitexpr(tcx, right);
            let (le, ld) = unpacktensor(&mut tcx.data.sub, Type::var(lty));
            let (re, rd) = unpacktensor(&mut tcx.data.sub, Type::var(rty));
            unifyvar(&mut tcx.data.sub, le, Type::var(re));
            constraint(&mut tcx.data, Constraint::BinOp(td, ld, rd));
            let res = match BinOp::from_u8(binop) {
                OR | AND => {
                    unifyvar(&mut tcx.data.sub, le, Type::pri(Primitive::B1));
                    Type::pri(Primitive::B1)
                },
                EQ | NE => {
                    Type::pri(Primitive::B1)
                },
                LT | LE => {
                    unifyvar(&mut tcx.data.sub, le, Type::pri(PRI_NUM));
                    Type::pri(Primitive::B1)
                },
                ADD | SUB | MUL | DIV => {
                    Type::var(le)
                },
                POW => {
                    unifyvar(&mut tcx.data.sub, le, Type::pri(Primitive::F64));
                    Type::pri(Primitive::F64)
                }
            };
            Some(newcontype(&mut tcx.data.sub, Constructor::Tensor, &[res, Type::var(td)]))
        },
        ObjectRef::INTR(&INTR { func, ref args, .. })
            => Some(visitintrinsic(tcx, Intrinsic::from_u8(func), args)),
        ObjectRef::FREF(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLX(CALLX { inputs, .. }) => {
            for &input in inputs {
                visitexpr(tcx, input);
            }
            None
        },
        _ => unreachable!()
    };
    if let Some(ty) = ty {
        unifyvar(&mut tcx.data.sub, tv, ty);
    }
    tv
}

fn canondim(sub: &mut IndexSlice<TypeVar, Type>, tv: TypeVar) -> Type {
    use TypeRepr::*;
    let mut ty = sub[tv];
    ty = match ty.unpack() {
        Var(i) if i == tv => Type::UNIT,
        Var(i) => canondim(sub, i),
        Con(Constructor::NEXT, prev) => {
            canondim(sub, prev);
            return ty;
        },
        Con(Constructor::UNIT, _) => return ty,
        _ => unreachable!()
    };
    trace!(TYPE "canon dim {:?} = {:?}", tv, ty.unpack());
    sub[tv] = ty;
    ty
}

fn canonpair(sub: &mut IndexSlice<TypeVar, Type>, tv: TypeVar) -> Type {
    use TypeRepr::*;
    let mut ty = sub[tv];
    ty = match ty.unpack() {
        Var(i) if i == tv => Type::UNIT,
        Var(i) => canonpair(sub, i),
        Con(Constructor::PAIR, base) => {
            canonpair(sub, base+1);
            return ty;
        },
        Con(Constructor::UNIT, _) => ty,
        _ => unreachable!()
    };
    sub[tv] = ty;
    ty
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
            if canondim(sub, base+1) == Type::UNIT {
                sub[base]
            } else {
                return ty;
            }
        },
        Con(Constructor::PAIR, base) => {
            canonpair(sub, base+1);
            return ty;
        },
        _ => return ty
    };
    trace!(TYPE "canon {:?} = {:?}", tv, ty.unpack());
    sub[tv] = ty;
    ty
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
            let dim = dimension(&ccx.data.sub, Type::var(base+1)).unwrap();
            debug_assert!(dim > 0);
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

fn isconcretetype(tvar: &IndexSlice<TypeVar, Type>, ty: Type) -> bool {
    use TypeRepr::*;
    match ty.unpack() {
        Var(j) if ty == Type::var(j) => false,
        Var(j) => isconcretetype(tvar, tvar[j]),
        Con(c, base) => (0..Constructor::from_u8(c).arity() as isize)
            .all(|i| isconcretetype(tvar, tvar[base+i])),
        Pri(p) => p.len() <= 1,
    }
}

fn createtype(tcx: &mut Tcx, ann: &mut HashMap<ObjRef, TypeVar>, idx: ObjRef) -> Type {
    let objs = Access::borrow(&tcx.objs);
    let o = objs.get(idx);
    let ty = match o {
        ObjectRef::SPEC(&SPEC { what: SPEC::NIL, .. }) => Type::var(newtypevar(&mut tcx.data.sub)),
        ObjectRef::TVAR(_) => return Type::var(match ann.entry(idx) {
            hash_map::Entry::Vacant(e) => *e.insert(newtypevar(&mut tcx.data.sub)),
            hash_map::Entry::Occupied(e) => *e.get()
        }),
        ObjectRef::TPRI(&TPRI { ty, .. }) => Type::pri(EnumSet::from_u16_truncated(1 << ty)),
        ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
            let e = match elem.is_nil() {
                true  => Type::var(newtypevar(&mut tcx.data.sub)),
                false => createtype(tcx, ann, elem)
            };
            let d = createdimtype(&mut tcx.data, dim);
            newcontype(&mut tcx.data.sub, Constructor::Tensor, &[e, d])
        },
        ObjectRef::TTUP(&TTUP { ref elems, .. }) => {
            let mut ty = Type::UNIT;
            for &e in elems.iter().rev() {
                let ety = createtype(tcx, ann, e);
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
    ty
}

fn deannotate(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    let mut anntv: HashMap<ObjRef, TypeVar> = Default::default();
    loop {
        'body: {
            let op = ccx.objs[idx].op;
            let ofs = match op {
                Obj::VAR => obj_index_of!(VAR, ann),
                _ if Operator::is_expr_raw(op) => obj_index_of!(EXPR, ann),
                _ => break 'body
            };
            let tv = newtypevar(&mut ccx.data.sub);
            let ann: ObjRef = zerocopy::transmute!(
                replace(&mut ccx.objs.get_raw_mut(idx)[ofs], zerocopy::transmute!(tv)));
            if !ann.is_nil() {
                let ty = ccx.freeze_graph(|ccx| createtype(ccx, &mut anntv, ann));
                ccx.data.sub[tv] = ty;
            }
            trace!(TYPE "{:?} -> {:?} ({:?})", idx, tv, ccx.data.sub[tv].unpack());
        }
        let Some(i) = ccx.objs.next(idx) else { return };
        idx = i;
    }
}

fn shapetype(tcx: &mut Tcx, idx: &[ObjRef<EXPR>]) -> Type {
    let base = tcx.tmp.end();
    let fields = tcx.tmp.align_for::<Type>();
    let mut nils = 0;
    for &i in idx {
        let ety = if i.is_nil() {
            nils += 1;
            Type::UNIT
        } else if nils > 0 {
            // TODO: more generally, this should allow the dimension to have any nesting
            // and only constrain the sum of dimensions.
            // eg. consider
            //   table A[global.N]
            //   table B[:,A.N]
            //   table C[:,:,B.N]
            // here
            //   A has 1 scalar axis
            //   B has 1 scalar axis and 1 vector axis
            //   C has 1 scalar axis (of size global.N) and 2 vector axes (of sizes A.N and B.N)
            // ie. nested vector axes "spill" into the preceding `:`s
            let dim = createdimtype(&mut tcx.data, nils);
            nils = 0;
            newcontype(&mut tcx.data.sub, Constructor::Tensor, &[Type::pri(PRI_IDX), dim])
        } else {
            Type::pri(PRI_IDX)
        };
        fields.push(ety);
    }
    debug_assert!(nils == 0);
    let ty = newpairlist(&mut tcx.data.sub, &fields[base.cast_up()..]);
    tcx.tmp.truncate(base);
    ty
}

fn modeltype(tcx: &mut Tcx, vsets: &[ObjRef<VSET>]) -> Type {
    let objs = Access::borrow(&tcx.objs);
    let base = tcx.tmp.end();
    for &vset in vsets {
        let &VSET { dim, var, ref idx, .. } = &objs[vset];
        let vty = visitvref(tcx, var, idx, dim as _);
        tcx.tmp.push(vty);
    }
    let ty = match &tcx.tmp[base.cast_up()..] {
        &[ty] => ty,
        fields => newpairlist(&mut tcx.data.sub, fields)
    };
    tcx.tmp.truncate(base);
    ty
}

fn visitglobals(tcx: &mut Tcx) {
    let objs = Access::borrow(&tcx.objs);
    for (idx, o) in objs.pairs() {
        match o {
            ObjectRef::TAB(&TAB { shape, .. }) => {
                trace!(TYPE "tab {:?}", idx);
                tcx.data.tab = ObjRef::GLOBAL;
                let ty = shapetype(tcx, &objs[shape].fields);
                let ety = visitexpr(tcx, shape.cast());
                unifyvar(&mut tcx.data.sub, ety, ty);
            },
            ObjectRef::MOD(&MOD { tab, guard, value, ref outputs, .. }) => {
                trace!(TYPE "mod {:?}", idx);
                tcx.data.tab = tab;
                if !guard.is_nil() {
                    let ety = visitexpr(tcx, guard);
                    unifyvar(&mut tcx.data.sub, ety, Type::pri(Primitive::B1));
                }
                let ty = modeltype(tcx, outputs);
                let ety = visitexpr(tcx, value);
                unifyvar(&mut tcx.data.sub, ety, ty);
            },
            ObjectRef::QUERY(&QUERY { tab, ref value, .. }) => {
                trace!(TYPE "query {:?}", idx);
                tcx.data.tab = tab;
                for &v in value {
                    visitexpr(tcx, v);
                }
            },
            _ => {}
        }
    }
}

fn fixvars(tcx: &mut Tcx) {
    for (_,o) in tcx.objs.pairs() {
        if let ObjectRef::VAR(&VAR { ann, .. }) = o {
            canonty(&mut tcx.data.sub, zerocopy::transmute!(ann));
        }
    }
}

fn reannotate(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    loop {
        'body: {
            let op = ccx.objs[idx].op;
            let ofs = match op {
                Obj::VAR => obj_index_of!(VAR, ann),
                _ if Operator::is_expr_raw(op) => {
                    canonty(&mut ccx.data.sub, zerocopy::transmute!(ccx.objs[idx.cast::<EXPR>()].ann));
                    obj_index_of!(EXPR, ann)
                },
                _ => break 'body
            };
            let tobj = typeobj(ccx, Type::var(zerocopy::transmute!(ccx.objs.get_raw(idx)[ofs])));
            ccx.objs.get_raw_mut(idx)[ofs] = zerocopy::transmute!(tobj);
        }
        let Some(i) = ccx.objs.next(idx) else { return };
        idx = i;
    }
}

impl Stage for TypeInfer {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        let mut sub: IndexVec<TypeVar, Type> = Default::default();
        // ORDER BUILTINTYPE
        sub.push(Type::UNIT);
        sub.push(Type::V1D);
        Ok(TypeInfer {
            sub,
            locals: Default::default(),
            con: Default::default(),
            tobj: Default::default(),
            tab: ObjRef::NIL.cast(),
            dim: (TypeVar::V1D, 1)
        })
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        deannotate(ccx);
        ccx.freeze_graph(|ccx| {
            visitglobals(ccx);
            simplify(&mut ccx.data);
            fixvars(ccx);
            simplify(&mut ccx.data);
        });
        debug_assert!(ccx.data.con.is_empty());
        reannotate(ccx);
        // TODO: check for errors
        if trace!(TYPE) {
            trace_objs(&ccx.intern, &ccx.objs, ObjRef::NIL);
        }
        Ok(())
    }

}
