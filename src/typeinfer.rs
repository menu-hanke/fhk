//! Type inference.

use core::cmp::min;
use core::fmt::Debug;
use core::hash::Hasher;
use core::iter::{repeat_n, zip};
use core::mem::replace;

use alloc::vec::Vec;
use enumset::{enum_set, EnumSet};
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use rustc_hash::FxHasher;

use crate::compile::{self, Ccx, Stage};
use crate::dump::trace_objs;
use crate::index::{self, index, IndexSlice, IndexVec};
use crate::intern::Interned;
use crate::obj::{obj_index_of, BinOp, Intrinsic, LocalId, Obj, ObjRef, ObjectRef, Objects, Operator, APPLY, BINOP, CALL, CAT, EXPR, FLAT, FUNC, INTR, KFP64, KINT, KINT64, LET, LGET, MOD, NEW, PGET, QUERY, SPEC, SPLAT, TAB, TGET, TPRI, TTEN, TTUP, TUPLE, VAR, VGET, VSET};
use crate::relation::Relation;
use crate::trace::trace;
use crate::typestate::{Absent, Access, R};
use crate::typing::{Constructor, Primitive, PRI_IDX};

index!(struct TypeVar(u32) debug("t{}"));
index!(struct FuncId(u32) invalid(!0));
index!(struct MonoId(u32) invalid(!0));

/*
 *         +--------+-------+
 *         | 31..28 | 27..0 |
 *         +========+=======+
 * link    |   0    |  tvar |
 *         +--------+-------+
 * pri     |   1    |  pri  |
 *         +--------+-------+
 * generic |   2    |  idx  |
 *         +--------+-------+
 * con     | 3+con  |  base |
 *         +--------+-------+
 */
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct Ty(u32);

/*
 *          +--------+-------+-------+
 *          | 31..28 |   27  | 26..0 |
 *          +========+=======+=======+
 * bound    |            Ty          |
 *          +--------+-------+-------+
 * unbound  |   15   | scope |  set  |
 *          +--------+-------+-------+
 */
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct Tv(u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Scope {
    Global,
    Local
}

#[derive(Clone, Copy)]
enum Type {
    Link(TypeVar),
    Primitive(Primitive),
    Generic(usize),
    Constructor(Constructor, TypeVar),
}

#[derive(Clone, Copy, Debug)]
enum TVar {
    Bound(Ty),
    Unbound(Scope, Option<EnumSet<Primitive>>),
}

#[derive(Clone)]
enum Constraint {
    BinOp(Ty, Ty, Ty), // a:dim, b:dim, c:dim :: a = b ∘ c
    Index(Ty, Ty, Ty), // b:tensor, c:dim :: a = b[c]
}

struct Func {
    name: Interned<[u8]>, // original objs[func].name; objs name is FuncId during inference
    obj: ObjRef<FUNC>,
    type_: Ty
}

struct Monomorphization {
    func: FuncId,
    obj: ObjRef<FUNC>,
    generics: TypeVar
}

pub struct TypeInfer {
    sub: IndexVec<TypeVar, Tv>,
    con: Vec<Constraint>,
    locals: IndexVec<LocalId, TypeVar>,
    func: IndexVec<FuncId, Func>,
    func_generic: Relation<FuncId, /* packed Option<EnumSet<Primitive>>: */u16>,
    func_con: Relation<FuncId, Constraint>,
    tobj: HashTable<ObjRef>,
    monotab: HashTable<MonoId>,
    mono: IndexVec<MonoId, Monomorphization>,
    tab: ObjRef<TAB>,
    func_args: Option<Ty>, // during inference
    func_generics: TypeVar, // during monomorphization
    dim: (TypeVar, u8),
}

type Tcx<'a> = Ccx<TypeInfer, R<'a>>;

// ORDER BUILTINTYPE
impl TypeVar {
    const UNIT: Self = zerocopy::transmute!(0);
    const V1D: Self = zerocopy::transmute!(1);
}

impl Ty {

    const UNIT: Ty = Ty::constructor(Constructor::Unit, TypeVar::UNIT);
    const V1D: Ty = Ty::constructor(Constructor::Next, TypeVar::UNIT);
    const NEVER: Ty = Ty::constructor(Constructor::Never, TypeVar::UNIT);

    fn link(tv: TypeVar) -> Self {
        Self(tv.0)
    }

    fn primitive(pri: Primitive) -> Self {
        Self((1 << 28) | (pri as u32))
    }

    fn generic(idx: usize) -> Self {
        Self((2 << 28) | (idx as u32))
    }

    const fn constructor(con: Constructor, mut base: TypeVar) -> Self {
        // canonicalize UNIT and NEVER
        if (con as u8) >= (Constructor::Unit as u8) {
            base = zerocopy::transmute!(0);
        }
        Self(((3+(con as u32)) << 28) | base.0)
    }

    fn unpack(self) -> Type {
        // unit/never must always be canonicalized
        debug_assert!(((self.0>>28) != Constructor::Unit as u32 + 3) || self == Ty::UNIT);
        debug_assert!(((self.0>>28) != Constructor::Never as u32 + 3) || self == Ty::NEVER);
        match self.0 >> 28 {
            0 => Type::Link(TypeVar(self.0)),
            1 => Type::Primitive(Primitive::from_u8(self.0 as _)),
            2 => Type::Generic(self.0 as u8 as usize),
            n => Type::Constructor(Constructor::from_u8(n as u8 - 3), TypeVar(self.0 & 0xfffffff))
        }
    }

    fn unwrap_link(self) -> TypeVar {
        let Type::Link(tv) = self.unpack() else { unreachable!() };
        tv
    }

    fn unwrap_constructor(self) -> (Constructor, TypeVar) {
        let Type::Constructor(con, base) = self.unpack() else { unreachable!() };
        (con, base)
    }

}

impl Debug for Type {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Type::Link(i) => i.fmt(f),
            Type::Primitive(p) => p.fmt(f),
            Type::Generic(i) => write!(f,"<{}>", i),
            Type::Constructor(Constructor::Tensor, base) => write!(f, "{:?}[{:?}]", base, base+1),
            Type::Constructor(Constructor::Pair, base) => write!(f, "({:?}, {:?})", base, base+1),
            Type::Constructor(Constructor::Func, base) => write!(f, "{:?} -> {:?}", base, base+1),
            Type::Constructor(Constructor::Next, prev) => write!(f, "{:?}+1", prev),
            Type::Constructor(Constructor::Unit, _) => f.write_str("()"),
            Type::Constructor(Constructor::Never, _) => f.write_str("!")
        }
    }
}

impl Debug for Ty {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.unpack().fmt(f)
    }
}

fn pri2raw(pri: Option<EnumSet<Primitive>>) -> u16 {
    match pri {
        Some(pri) => pri.as_u16_truncated(),
        None => !0
    }
}

impl Tv {

    fn bound(ty: Ty) -> Self {
        Self(ty.0)
    }

    fn unbound(scope: Scope, pri: Option<EnumSet<Primitive>>) -> Self {
        Self((0xf << 28) | ((scope as u32) << 27) | pri2raw(pri) as u32)
    }

    fn unpack(self) -> TVar {
        match self.0 >> 28 {
            15 => TVar::Unbound(
                match self.0 & (1 << 27) {
                    0 => Scope::Global,
                    _ => Scope::Local
                },
                EnumSet::try_from_u16(self.0 as _)
            ),
            _ => TVar::Bound(Ty(self.0))
        }
    }

    fn unwrap_bound(self) -> Ty {
        assert!((self.0 >> 28) != 15);
        Ty(self.0)
    }

}

impl Debug for Tv {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.unpack().fmt(f)
    }
}

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

fn newtypevar(sub: &mut IndexVec<TypeVar, Tv>, scope: Scope) -> TypeVar {
    let new = Tv::unbound(scope, None);
    // trace!(TYPE "new {:?} = {:?}", sub.end(), new);
    sub.push(new)
}

fn newcontype(sub: &mut IndexVec<TypeVar, Tv>, con: Constructor, par: &[Ty]) -> Ty {
    let base = sub.end();
    sub.raw.extend(par.iter().cloned().map(Tv::bound));
    Ty::constructor(con, base)
}

fn newpairtype(sub: &mut IndexVec<TypeVar, Tv>, left: Ty, right: Ty) -> Ty {
    newcontype(sub, Constructor::Pair, &[left, right])
}

fn newpairlist(sub: &mut IndexVec<TypeVar, Tv>, fields: &[Ty]) -> Ty {
    let mut ty = Ty::UNIT;
    for &f in fields.iter().rev() {
        ty = newpairtype(sub, f, ty);
    }
    ty
}

fn emptypairlist(sub: &mut IndexVec<TypeVar, Tv>, len: usize, scope: Scope) -> Ty {
    let mut ty = Ty::UNIT;
    for _ in 0..len {
        let base = sub.end();
        newtypevar(sub, scope);
        sub.push(Tv::bound(ty));
        ty = Ty::constructor(Constructor::Pair, base);
    }
    ty
}

fn isconcretetypev(sub: &IndexSlice<TypeVar, Tv>, tv: TypeVar, scope: Scope) -> bool {
    use TVar::*;
    match sub[tv].unpack() {
        Bound(t) => isconcretetype(sub, t, scope),
        Unbound(s, _) => s < scope
    }
}

fn isconcretetype(sub: &IndexSlice<TypeVar, Tv>, ty: Ty, scope: Scope) -> bool {
    use Type::*;
    match ty.unpack() {
        Link(i) => isconcretetypev(sub, i, scope),
        Constructor(c, b) => {
            for i in 0..c.arity() as isize {
                if !isconcretetypev(sub, b+i, scope) {
                    return false
                }
            }
            true
        },
        Generic(_) => false,
        Primitive(_) => true
    }
}

fn occursv(sub: &mut IndexSlice<TypeVar, Tv>, a: TypeVar, b: TypeVar, scope: Scope) {
    use TVar::*;
    if a == b {
        // TODO: type error recursive type
        todo!()
    }
    match sub[b].unpack() {
        Bound(t) => occurs(sub, a, t, scope),
        Unbound(Scope::Global, _) => { /* ok */ },
        Unbound(Scope::Local, _) if scope == Scope::Local => { /* ok */ },
        Unbound(Scope::Local, pri) => sub[b] = Tv::unbound(Scope::Global, pri)
    }
}

fn occurs(sub: &mut IndexSlice<TypeVar, Tv>, a: TypeVar, b: Ty, scope: Scope) {
    use Type::*;
    match b.unpack() {
        Link(i) => occursv(sub, a, i, scope),
        Constructor(c, d) => {
            for i in 0..c.arity() as isize {
                occursv(sub, a, d+i, scope);
            }
        },
        _ => { /* ok */ }
    }
}

fn unifyss(a: Scope, b: Scope) -> Scope {
    use Scope::*;
    match (a, b) {
        (Global, _) | (_, Global) => Global,
        (Local, Local) => Local
    }
}

fn unifyvv(sub: &mut IndexSlice<TypeVar, Tv>, a: TypeVar, b: TypeVar) {
    use TVar::*;
    trace!(TYPE "unify {a:?} = {b:?}");
    if a == b { return }
    match (sub[a].unpack(), sub[b].unpack()) {
        (Bound(ta), Bound(tb)) => unifytt(sub, ta, tb),
        (Bound(t), Unbound(_, _)) => unifyvt(sub, b, t),
        (Unbound(_, _), Bound(t)) => unifyvt(sub, a, t),
        (Unbound(sa, pa), Unbound(sb, pb)) => {
            let pri = match (pa, pb) {
                (Some(pa), Some(pb)) => Some(pa&pb),
                (Some(p), None) | (None, Some(p)) => Some(p),
                (None, None) => None
            };
            sub[a] = match pri {
                Some(pri) if pri.is_empty() => { todo!() /* type error */ },
                Some(pri) if pri.len() == 1 => Tv::bound(Ty::primitive(pri.iter().next().unwrap())),
                _ => Tv::unbound(unifyss(sa, sb), pri)
            };
            sub[b] = Tv::bound(Ty::link(a));
        }
    }
}

fn unifyvpri(sub: &mut IndexSlice<TypeVar, Tv>, a: TypeVar, b: EnumSet<Primitive>) {
    use TVar::*;
    trace!(TYPE "unify {a:?} in {b:?}");
    match sub[a].unpack() {
        Bound(t) => unifytpri(sub, t, b),
        Unbound(scope, p) => {
            let pri = b & p.unwrap_or(EnumSet::all());
            sub[a] = match pri.len() {
                0 => { todo!() /* type error */ },
                1 => Tv::bound(Ty::primitive(pri.iter().next().unwrap())),
                _ => Tv::unbound(scope, Some(pri))
            };
        }
    }
}

fn unifyvt(sub: &mut IndexSlice<TypeVar, Tv>, a: TypeVar, mut b: Ty) {
    use {Type::*,TVar::*};
    trace!(TYPE "unify {a:?} = {b:?}");
    match (sub[a].unpack(), b.unpack()) {
        (_, Link(i)) => unifyvv(sub, a, i),
        (Bound(t), _) => unifytt(sub, t, b),
        (Unbound(scope, pri), t) => {
            match (pri, t) {
                (Some(pri), Primitive(p)) if pri.contains(p) => { /* ok */ },
                (Some(pri), Constructor(self::Constructor::Tensor, base)) => {
                    unifyvpri(sub, base, pri);
                    unifyvt(sub, base+1, Ty::UNIT);
                    b = Ty::link(base);
                },
                (None, _) => { /* ok */ },
                _ => { todo!() /* type error */ }
            }
            occurs(sub, a, b, scope);
            sub[a] = Tv::bound(b);
        }
    }
}

fn unifytt(sub: &mut IndexSlice<TypeVar, Tv>, a: Ty, b: Ty) {
    use Type::*;
    trace!(TYPE "unify {a:?} = {b:?}");
    match (a.unpack(), b.unpack()) {
        (Link(i), Link(j)) => unifyvv(sub, i, j),
        (Link(i), _) => unifyvt(sub, i, b),
        (_, Link(j)) => unifyvt(sub, j, a),
        (Primitive(p), Primitive(q)) if p==q => { /* ok */ },
        (Generic(i), Generic(j)) if i==j => { /* ok */ },
        (Constructor(c, c0), Constructor(d, d0)) if c==d => {
            for i in 0..c.arity() as isize {
                unifyvv(sub, c0 + i, d0 + i)
            }
        },
        (Constructor(self::Constructor::Tensor, base), _) => {
            unifyvt(sub, base, b);
            unifyvt(sub, base+1, Ty::UNIT);
        },
        (_, Constructor(self::Constructor::Tensor, base)) => {
            unifyvt(sub, base, a);
            unifyvt(sub, base+1, Ty::UNIT);
        },
        (Constructor(self::Constructor::Never, _), _)
            | (_, Constructor(self::Constructor::Never, _)) => { /* ok */ },
        _ => {
            // TODO: type error
            todo!()
        }
    }
}

fn unifytpri(sub: &mut IndexSlice<TypeVar, Tv>, a: Ty, b: EnumSet<Primitive>) {
    use Type::*;
    match a.unpack() {
        Link(i) => unifyvpri(sub, i, b),
        Primitive(p) if b.contains(p) => { /* ok */ },
        Constructor(self::Constructor::Tensor, base) => {
            unifyvpri(sub, base, b);
            unifyvt(sub, base+1, Ty::UNIT);
        },
        _ => { todo!() /* type error */ }
    }
}

fn generalizev(ctx: &mut TypeInfer, func: FuncId, a: TypeVar) {
    use TVar::*;
    // trace!(TYPE "generalize {:?} = {:?}", a, ctx.sub[a]);
    match ctx.sub[a].unpack() {
        Bound(t) => generalizet(ctx, func, t),
        Unbound(Scope::Local, pri) => {
            ctx.sub[a] = Tv::bound(Ty::generic(ctx.func_generic[func].len()));
            ctx.func_generic.add(func, pri2raw(pri));
            trace!(TYPE "generalize {:?}: {:?} ({:?})", a, ctx.sub[a], pri);
        },
        Unbound(Scope::Global, _) => {}
    }
}

fn generalizet(ctx: &mut TypeInfer, func: FuncId, a: Ty) {
    use Type::*;
    // trace!(TYPE "generalize {:?}", a);
    match a.unpack() {
        Link(i) => generalizev(ctx, func, i),
        Constructor(c, b) => {
            for i in 0..c.arity() as isize {
                generalizev(ctx, func, b + i)
            }
        },
        _ => {}
    }
}

fn isconcretec(sub: &IndexSlice<TypeVar, Tv>, con: &Constraint) -> bool {
    match con {
        &Constraint::BinOp(a, b, c) | &Constraint::Index(a, b, c) =>
            isconcretetype(sub, a, Scope::Local)
            && isconcretetype(sub, b, Scope::Local)
            && isconcretetype(sub, c, Scope::Local)
    }
}

fn generalizec(ctx: &mut TypeInfer, func: FuncId) {
    let mut idx = 0;
    while idx < ctx.con.len() {
        if isconcretec(&ctx.sub, &ctx.con[idx]) {
            idx += 1;
        } else {
            ctx.func_con.add(func, ctx.con.swap_remove(idx));
        }
    }
}

fn generalizef(ctx: &mut TypeInfer, func: FuncId) {
    generalizec(ctx, func);
    generalizet(ctx, func, ctx.func[func].type_);
}

fn func2scope(args: Option<Ty>) -> Scope {
    match args {
        Some(_) => Scope::Local,
        None => Scope::Global
    }
}

fn instantiatev(sub: &mut IndexVec<TypeVar, Tv>, generics: TypeVar, a: TypeVar) -> Ty {
    use TVar::*;
    match sub[a].unpack() {
        Bound(t) => instantiatet(sub, generics, t),
        Unbound(_, _) => Ty::link(a)
    }
}

fn instantiatet(sub: &mut IndexVec<TypeVar, Tv>, generics: TypeVar, a: Ty) -> Ty {
    use Type::*;
    match a.unpack() {
        Link(i) => instantiatev(sub, generics, i),
        Primitive(_) => a,
        Generic(i) => Ty::link(generics + i as isize),
        Constructor(c,b) => {
            let bb = sub.end();
            sub.raw.extend(repeat_n(Tv::unbound(Scope::Global, None), c.arity() as _));
            for i in 0..c.arity() as isize {
                sub[bb+i] = Tv::bound(instantiatev(sub, generics, b+i));
            }
            Ty::constructor(c, bb)
        }
    }
}

fn instantiatec(sub: &mut IndexVec<TypeVar, Tv>, generics: TypeVar, con: &Constraint) -> Constraint {
    use Constraint::*;
    match con {
        &BinOp(a, b, c) => {
            let a = instantiatet(sub, generics, a);
            let b = instantiatet(sub, generics, b);
            let c = instantiatet(sub, generics, c);
            BinOp(a, b, c)
        },
        &Index(a, b, c) => {
            let a = instantiatet(sub, generics, a);
            let b = instantiatet(sub, generics, b);
            let c = instantiatet(sub, generics, c);
            Index(a, b, c)
        }
    }
}

fn instantiatef(ctx: &mut TypeInfer, fid: FuncId) -> (TypeVar, Ty) {
    let &Func { type_, .. } = &ctx.func[fid];
    let generics = &ctx.func_generic[fid];
    if generics.is_empty() {
        debug_assert!(ctx.func_con[fid].is_empty());
        return (TypeVar(0), type_);
    }
    let generics_base = ctx.sub.end();
    let scope = func2scope(ctx.func_args);
    ctx.sub.raw.extend(generics.iter().map(|&c| Tv::unbound(scope, EnumSet::try_from_u16(c))));
    let ncon = ctx.func_con[fid].len();
    for i in 0..ncon {
        let con = instantiatec(&mut ctx.sub, generics_base, &ctx.func_con[fid][i]);
        constraint(ctx, con);
    }
    (generics_base, instantiatet(&mut ctx.sub, generics_base, type_))
}

fn unpacktensor(sub: &mut IndexVec<TypeVar, Tv>, ten: Ty, scope: Scope) -> (TypeVar, TypeVar) {
    match ten.unpack() {
        Type::Constructor(Constructor::Tensor, base) => return (base, base+1),
        Type::Link(i) => {
            if let TVar::Bound(t) = sub[i].unpack() {
                return unpacktensor(sub, t, scope);
            }
        },
        _ => {}
    }
    let e = newtypevar(sub, scope);
    let d = newtypevar(sub, scope);
    unifytt(sub, ten, Ty::constructor(Constructor::Tensor, e));
    (e, d)
}

fn equalvv(
    sub: &IndexSlice<TypeVar, Tv>,
    generics: Option<TypeVar>,
    a: TypeVar,
    b: TypeVar
) -> Option<bool> {
    use TVar::*;
    if a == b { return Some(true) }
    match (sub[a].unpack(), sub[b].unpack()) {
        (Bound(t), Bound(u)) => equaltt(sub, generics, t, u),
        _ => None // TODO: check primitives
    }
}

fn equalvt(
    sub: &IndexSlice<TypeVar, Tv>,
    generics: Option<TypeVar>,
    a: TypeVar,
    b: Ty
) -> Option<bool> {
    use TVar::*;
    match sub[a].unpack() {
        Bound(t) => equaltt(sub, generics, t, b),
        Unbound(_, _) => None // TODO: check primitives
    }
}

fn equaltensor(
    sub: &IndexSlice<TypeVar, Tv>,
    generics: Option<TypeVar>,
    elem: TypeVar,
    dim: TypeVar,
    b: Ty
) -> Option<bool> {
    match (equalvt(sub, generics, elem, b), equalvt(sub, generics, dim, Ty::UNIT)) {
        (Some(true), Some(true)) => Some(true),
        (Some(false), _) | (_, Some(false)) => Some(false),
        _ => None
    }
}

fn equaltt(sub: &IndexSlice<TypeVar, Tv>, generics: Option<TypeVar>, a: Ty, b: Ty) -> Option<bool> {
    use Type::*;
    if a == b { return Some(true) }
    match (a.unpack(), b.unpack()) {
        (Link(i), Link(j)) => equalvv(sub, generics, i, j),
        (Link(i), _) => equalvt(sub, generics, i, b),
        (_, Link(j)) => equalvt(sub, generics, j, a),
        (Primitive(p), Primitive(q)) => Some(p==q),
        (Generic(i), Generic(j)) if i==j => Some(true),
        (Generic(i), Generic(j)) => match generics {
            Some(base) => equalvv(sub, generics, base + i as isize, base + j as isize),
            None => None
        },
        (Constructor(c, c0), Constructor(d, d0)) if c==d => {
            for i in 0..c.arity() as isize {
                match equalvv(sub, generics, c0+i, d0+i) {
                    Some(true) => {},
                    r => return r
                }
            }
            Some(true)
        },
        (Constructor(self::Constructor::Tensor, base), _) => equaltensor(sub, generics, base, base+1, b),
        (_, Constructor(self::Constructor::Tensor, base)) => equaltensor(sub, generics, base, base+1, a),
        _ => Some(false)
    }
}

fn shallowdimension(sub: &IndexSlice<TypeVar, Tv>, ty: Ty) -> Option<Ty> {
    use {Type::*,TVar::*};
    match ty.unpack() {
        Link(i) => match sub[i].unpack() {
            Bound(t) => shallowdimension(sub, t),
            Unbound(_, _) => None
        },
        Constructor(self::Constructor::Tensor, base) => shallowdimension(sub, Ty::link(base+1)),
        Constructor(self::Constructor::Next, _) => Some(ty),
        _ => Some(Ty::UNIT)
    }
}

fn simplify_binop(sub: &mut IndexSlice<TypeVar, Tv>, a: Ty, b: Ty, c: Ty) -> bool {
    match (
        shallowdimension(sub, a),
        shallowdimension(sub, b),
        shallowdimension(sub, c),
    ) {
        (_, Some(Ty::UNIT), _) => {
            // scalar lhs -> output is rhs
            unifytt(sub, a, c);
            true
        },
        (_, _, Some(Ty::UNIT)) => {
            // scalar rhs -> output is lhs
            unifytt(sub, a, b);
            true
        },
        (Some(Ty::UNIT), _, _) | (_, Some(_), Some(_)) => {
            // scalar output -> scalar inputs
            // two tensor inputs -> tensor output
            unifytt(sub, a, b);
            unifytt(sub, a, c);
            true
        }
        _ => false
    }
}

fn simplify_index(sub: &mut IndexVec<TypeVar, Tv>, a: Ty, b: Ty, c: Ty, scope: Scope) -> bool {
    match (
        shallowdimension(sub, a),
        shallowdimension(sub, b),
        shallowdimension(sub, c)
    ) {
        (Some(Ty::UNIT), _, _) => {
            // output is scalar -> we are indexing a 1-d tensor with a scalar
            let (e, d) = unpacktensor(sub, b, scope);
            unifyvt(sub, e, a);
            unifyvt(sub, d, Ty::V1D);
            unifytt(sub, c, Ty::UNIT);
            true
        },
        (Some(_), _, Some(Ty::UNIT)) => {
            // output is n-d tensor and index is scalar -> we are indexing an (n+1)-d tensor
            let (eb, db) = unpacktensor(sub, b, scope);
            let (ea, da) = unpacktensor(sub, a, scope);
            unifyvv(sub, eb, ea);
            unifyvt(sub, db, Ty::constructor(Constructor::Next, da));
            true
        },
        (_, _, Some(d)) if d != Ty::UNIT => {
            // index is tensor -> we are indexing an n-d tensor with a 1-d tensor
            unifytt(sub, a, b);
            unifytt(sub, c, Ty::V1D);
            true
        },
        (Some(da), Some(db), _) if match equaltt(sub, None, da, db) {
            Some(true) => {
                // input and output have same dimension -> indexing with a 1-d tensor
                unifytt(sub, a, b);
                unifytt(sub, c, Ty::V1D);
                true
            },
            Some(false) => {
                // input and output have different dimensions, and output is known to be a tensor
                // -> scalar index of n-d tensor (n>1) -> tensor result
                let (ea, da) = unpacktensor(sub, a, scope);
                let (eb, db) = unpacktensor(sub, b, scope);
                unifyvv(sub, eb, ea);
                unifyvt(sub, db, Ty::constructor(Constructor::Next, da));
                unifytt(sub, c, Ty::UNIT);
                true
            },
            None => false
        } => true,
        (_, Some(db), Some(Ty::UNIT)) if match shallowdimension(sub, db) {
            Some(ddb) => match shallowdimension(sub, ddb) {
                Some(Ty::UNIT) => {
                    // scalar index of 1-d tensor -> scalar result.
                    let (eb, _) = unpacktensor(sub, b, scope);
                    unifyvt(sub, eb, a);
                    true
                },
                Some(_) => {
                    // scalar index of n-d tensor (n>1) -> tensor result.
                    let (ea, da) = unpacktensor(sub, a, scope);
                    let (eb, db) = unpacktensor(sub, b, scope);
                    unifyvv(sub, eb, ea);
                    unifyvt(sub, db, Ty::constructor(Constructor::Next, da));
                    true
                },
                None => false
            },
            None => false
        } => true,
        _ => false
    }
}

fn simplifyconstraint(ctx: &mut TypeInfer, con: Constraint) -> bool {
    match con {
        Constraint::BinOp(a, b, c) => simplify_binop(&mut ctx.sub, a, b, c),
        Constraint::Index(a, b, c) => simplify_index(&mut ctx.sub, a, b, c, func2scope(ctx.func_args))
    }
}

fn constraint(ctx: &mut TypeInfer, con: Constraint) {
    if !simplifyconstraint(ctx, con.clone()) {
        ctx.con.push(con);
    }
}

fn simplify(ctx: &mut TypeInfer) {
    loop {
        let mut fixpoint = true;
        let mut idx = 0;
        while idx < ctx.con.len() {
            if simplifyconstraint(ctx, ctx.con[idx].clone()) {
                ctx.con.swap_remove(idx);
                fixpoint = false;
            } else {
                idx += 1;
            }
        }
        if fixpoint { break }
    }
}

fn createdimtype(ts: &mut TypeInfer, dim: u8) -> TypeVar {
    let (mut tv, mut d) = ts.dim;
    while dim < d {
        let (_, prev) = ts.sub[tv].unwrap_bound().unwrap_constructor();
        tv = prev;
        d -= 1;
    }
    while dim > d {
        tv = ts.sub.push(Tv::bound(Ty::constructor(Constructor::Next, tv)));
        d += 1;
    }
    ts.dim = (tv, d);
    tv
}

fn dimension(sub: &IndexSlice<TypeVar, Tv>, ty: Ty) -> Option<u8> {
    match shallowdimension(sub, ty) {
        Some(Ty::UNIT) => Some(0),
        Some(next) => {
            let (_, prev) = next.unwrap_constructor();
            match dimension(sub, sub[prev].unwrap_bound()) {
                Some(d) => Some(d+1),
                None => None
            }
        },
        None => None
    }
}

fn sametype(a: ObjectRef, b: Type, work: &[u32]) -> bool {
    match (a, b) {
        (ObjectRef::TPRI(&TPRI { ty, .. }), Type::Primitive(p)) => ty == p as _,
        (ObjectRef::TTEN(&TTEN { elem, dim, .. }), Type::Constructor(Constructor::Tensor, _))
            => work == &[zerocopy::transmute!(elem), dim as _],
        (ObjectRef::TTUP(TTUP { elems, .. }), Type::Constructor(Constructor::Pair|Constructor::Unit, _))
            => work.len() == elems.len()
            && zip(work.iter(), elems.iter()).all(|(&ea,&eb)| ea == zerocopy::transmute!(eb)),
        _ => false
    }
}

fn createtypeobj(objs: &mut Objects, type_: Type, work: &[u32]) -> ObjRef {
    match type_ {
        Type::Primitive(p) => objs.push(TPRI::new(p as _)).erase(),
        Type::Constructor(Constructor::Tensor, _) => {
            debug_assert!(work[1] > 0); // dim 0 tensor should be canonicalized to scalar
            objs.push(TTEN::new(work[1] as _, zerocopy::transmute!(work[0]))).erase()
        },
        Type::Constructor(Constructor::Pair|Constructor::Unit, _) => {
            // XXX replace with zerocopy::transmute when it can do that
            let work: &[ObjRef] = unsafe {
                core::slice::from_raw_parts(work.as_ptr().cast(), work.len())
            };
            objs.push_args::<TTUP>(TTUP::new(), work).erase()
        }
        _ => unreachable!()
    }
}

fn createtype(tcx: &mut Tcx, idx: ObjRef, scope: Scope) -> Ty {
    let objs = Access::borrow(&tcx.objs);
    let o = objs.get(idx);
    let ty = match o {
        ObjectRef::SPEC(&SPEC { what: SPEC::NIL, .. }) => Ty::link(newtypevar(&mut tcx.data.sub, scope)),
        ObjectRef::TPRI(&TPRI { ty, .. }) => Ty::primitive(Primitive::from_u8(ty)),
        ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
            let e = match elem.is_nil() {
                true  => Ty::link(newtypevar(&mut tcx.data.sub, scope)),
                false => createtype(tcx, elem, scope)
            };
            let d = createdimtype(&mut tcx.data, dim);
            newcontype(&mut tcx.data.sub, Constructor::Tensor, &[e, Ty::link(d)])
        },
        ObjectRef::TTUP(&TTUP { ref elems, .. }) => {
            let mut ty = Ty::UNIT;
            for &e in elems.iter().rev() {
                let ety = createtype(tcx, e, scope);
                ty = newpairtype(&mut tcx.data.sub, ety, ty);
            }
            ty
        },
        _ => unreachable!()
    };
    if isconcretetype(&tcx.data.sub, ty, scope) {
        let hash = hashtypeobj(o);
        if let Entry::Vacant(e) = tcx.data.tobj.entry(
            hash,
            |&t| objs.equal(t, idx),
            |&t| hashtypeobj(objs.get(t))
        ) {
            e.insert(idx);
        }
    }
    ty
}

fn visitvref(tcx: &mut Tcx, var: ObjRef<VAR>, idx: &[ObjRef<EXPR>], mut have: usize) -> Ty {
    let objs = Access::borrow(&tcx.objs);
    let axes = &objs[objs[objs[var].tab].shape].fields;
    let need = axes.len();
    if have > need {
        // too many indices mentioned.
        return Ty::NEVER;
    }
    let prefix = min(objs.dim(tcx.data.tab), need-have);
    have += prefix;
    let mut ty = Ty::link(zerocopy::transmute!(objs[var].ann));
    let mut dim = 0;
    if have < need {
        for i in (have..need).rev() {
            dim += 1;
            if i > 0 && axes[i-1].is_nil() {
                // vector axis or end of tail
                let d = createdimtype(&mut tcx.data, dim as _);
                ty = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, Ty::link(d)]);
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
            ty = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, Ty::link(d)]);
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
        let mut v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, Ty::link(d)]);
        let scope = func2scope(tcx.data.func_args);
        for &e in idx {
            match objs[e].op {
                Obj::SPEC if objs[e].data == SPEC::NIL => continue,
                Obj::SPEC if objs[e].data == SPEC::SLURP => {
                    // dimension can't go to zero here because this is always followed by an
                    // explicit index, so we don't need a constraint.
                    let (_, dim) = unpacktensor(&mut tcx.data.sub, v, scope);
                    let dim = newcontype(&mut tcx.data.sub, Constructor::Next, &[Ty::link(dim)]);
                    v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, dim]);
                },
                Obj::FLAT => {
                    // dimension can't go to zero here because this behaves like a 1D tensor index,
                    // so we don't need a constraint.
                    visitexpr(tcx, e);
                    let m = objs[e.cast::<FLAT>()].idx.len();
                    if m > 1 {
                        let (_, dim) = unpacktensor(&mut tcx.data.sub, v, scope);
                        let mut dim = Ty::link(dim);
                        for _ in 1..m {
                            dim = newcontype(&mut tcx.data.sub, Constructor::Next, &[dim]);
                        }
                        v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, dim]);
                    }
                },
                _ => {
                    let ety = visitexpr(tcx, e);
                    let (elem, edim) = unpacktensor(&mut tcx.data.sub, Ty::link(ety), scope);
                    unifyvt(&mut tcx.data.sub, elem, Ty::primitive(PRI_IDX));
                    let vnext = newtypevar(&mut tcx.data.sub, scope);
                    constraint(&mut tcx.data, Constraint::Index(Ty::link(vnext), v, Ty::link(edim)));
                    v = Ty::link(vnext);
                }
            }
        }
        // increment dimension if we have implicit dimensions
        if dim > 0 {
            let vdim = newtypevar(&mut tcx.data.sub, scope);
            let vten = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, Ty::link(vdim)]);
            unifytt(&mut tcx.data.sub, vten, v);
            let mut rdim = Ty::constructor(Constructor::Next, vdim);
            for _ in 0..dim {
                rdim = newcontype(&mut tcx.data.sub, Constructor::Next, &[rdim]);
            }
            let rdim = tcx.data.sub.push(Tv::bound(rdim));
            v = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[ty, Ty::link(rdim)]);
        }
        v
    }
}

fn visittuple(tcx: &mut Tcx, elements: &[ObjRef<EXPR>]) -> Ty {
    let mut ty = Ty::UNIT;
    for &e in elements.iter().rev() {
        let ety = visitexpr(tcx, e);
        ty = newpairtype(&mut tcx.data.sub, Ty::link(ety), ty);
    }
    ty
}

fn indextuple(sub: &mut IndexVec<TypeVar, Tv>, mut ty: Ty, mut field: usize) -> TypeVar {
    use {Type::*, TVar::*, self::Constructor::*};
    let (scope, mut tvar) = loop {
        match ty.unpack() {
            Link(i) => match sub[i].unpack() {
                Bound(t) => ty = t,
                Unbound(scope, _) => break (scope, i)
            },
            Constructor(Pair, base) => match field {
                0 => return base,
                _ => {
                    ty = Ty::link(base+1);
                    field -= 1;
                }
            },
            _ => {
                // TODO: anything else is a type error
                todo!()
            }
        }
    };
    loop {
        let element = newtypevar(sub, scope);
        let next = newtypevar(sub, scope);
        let repr = newpairtype(sub, Ty::link(element), Ty::link(next));
        unifyvt(sub, tvar, repr);
        match field {
            0 => return element,
            _ => {
                tvar = next;
                field -= 1;
            }
        }
    }
}

fn unpackvarg(sub: &mut IndexVec<TypeVar, Tv>, args: &[Ty]) -> Ty {
    match args {
        [] => Ty::NEVER,
        &[first, ref rest@..] => {
            for &r in rest {
                unifytt(sub, first, r);
            }
            first
        }
    }
}

// TODO: replace this with generic functions
macro_rules! instantiate {
    (@type pri $v:expr ; $($_:tt)*) => {
        Ty::primitive($v)
    };
    (@type $con:ident $($t:expr)+ ; $tcx:expr) => {
        newcontype(&mut $tcx.data.sub, Constructor::$con, &[$($t),+])
    };
    (@type $v:tt ; $($_:tt)*) => {
        $v
    };
    (
        $tcx:expr,
        $scope:expr,
        $args:expr;
        $($unpack:ident)*
        $(...$varg:ident)?
        $(, $($new:ident $([$bound:expr])? )*)?
        $(
            ::
            $( $lhs:ident [$($rhs:tt)*] ),*
        )?
        =>
        $($ret:tt)*
    ) => {{
        let &[ $($unpack,)* $(ref $varg@..)? ] = $args
            else { unreachable!() /* TODO: should be type error */ };
        $(let $varg = unpackvarg(&mut $tcx.data.sub, $varg);)?
        $(
            $(
                let $new = Ty::link(
                    $tcx.data.sub.push(
                        Tv::unbound(
                            $scope,
                            None $( .or(Some($bound)) )?
                        )
                    )
                );
            )*
        )?
        $(
            $(
                {
                    let rhs = instantiate!(@type $($rhs)* ; $tcx);
                    unifytt(&mut $tcx.data.sub, $lhs, rhs);
                }
            )*
        )?
        instantiate!(@type $($ret)* ; $tcx)
    }};
}

fn visitselect(tcx: &mut Tcx, cond: Ty, tru: Ty, fal: Ty, scope: Scope) -> Ty {
    let (ce,cd) = unpacktensor(&mut tcx.data.sub, cond, scope);
    let (te,td) = unpacktensor(&mut tcx.data.sub, tru, scope);
    let (fe,fd) = unpacktensor(&mut tcx.data.sub, fal, scope);
    // must require e to be primitive here to prevent the potential creation of a
    // zero-dimension non-primitive tensor (which makes the typing unsound).
    // this restriction isn't actually always needed: if cond is scalar, we could just require
    // tru=fal and return that. for now, this is not implemented because it requires creating
    // a new constraint type.
    let e = tcx.data.sub.push(Tv::unbound(scope, Some(EnumSet::all())));
    let d = newtypevar(&mut tcx.data.sub, scope); // must be e+1
    let d1 = newtypevar(&mut tcx.data.sub, scope);
    unifyvt(&mut tcx.data.sub, ce, Ty::primitive(Primitive::B1));
    unifyvv(&mut tcx.data.sub, e, te);
    unifyvv(&mut tcx.data.sub, e, fe);
    constraint(&mut tcx.data, Constraint::BinOp(Ty::link(d1), Ty::link(td), Ty::link(fd)));
    constraint(&mut tcx.data, Constraint::BinOp(Ty::link(d), Ty::link(d1), Ty::link(cd)));
    Ty::constructor(Constructor::Tensor, e)
}

fn visitintrinsic(tcx: &mut Tcx, func: Intrinsic, args: &[ObjRef<EXPR>]) -> Ty {
    use Intrinsic::*;
    let base = tcx.tmp.end();
    for &a in args {
        let ety = visitexpr(tcx, a);
        tcx.tmp.push(Ty::link(ety));
    }
    let aty: &[Ty] = &tcx.tmp[base.cast_up()..];
    let scope = func2scope(tcx.data.func_args);
    macro_rules! I { ($($t:tt)*) => { instantiate!(tcx, scope, aty; $($t)*) }; }
    let ty = match func {
        UNM | EXP | LOG => I!(a,e[PRI_NUM] n :: a[Tensor e n] => a),
        ALL | ANY => I!(a,n :: a[Tensor Ty::primitive(Primitive::B1) n] => pri Primitive::B1),
        CONV => I!(a,b e n :: a[Tensor e n] => Tensor b n),
        EFFECT => I!(a ...b :: b[pri Primitive::FX] => a),
        LEN => I!(_a ...b :: b[pri PRI_IDX] => pri PRI_IDX),
        LOAD => I!(p ...s,r :: p[pri Primitive::PTR], s[pri PRI_IDX] => r),
        NOT => I!(a,n :: a[Tensor Ty::primitive(Primitive::B1) n] => a),
        REP => I!(a,e n m :: a[Tensor e n] => Tensor e m),
        SELECT => {
            let &[c,t,f] = aty else { unreachable!() };
            visitselect(tcx, c, t, f, scope)
        },
        SUM => I!(a,e[PRI_NUM] n :: a[Tensor e n] => e),
        // TODO (?): generalize WHICH to return tuples.
        WHICH => I!(a :: a[Tensor Ty::primitive(Primitive::B1) Ty::V1D]
            => Tensor Ty::primitive(PRI_IDX) Ty::V1D),
    };
    tcx.tmp.truncate(base);
    ty
}

fn visitexpr(tcx: &mut Tcx, idx: ObjRef<EXPR>) -> TypeVar {
    let objs = Access::borrow(&tcx.objs);
    let tv: TypeVar = zerocopy::transmute!(objs[idx].ann);
    if idx.is_builtin() {
        // skip KINT logic for TRUE and FALSE
        return tv;
    }
    let scope = func2scope(tcx.data.func_args);
    match objs.get(idx.erase()) {
        ObjectRef::SPEC(_) => {
            unifyvt(&mut tcx.data.sub, tv, Ty::UNIT);
        },
        ObjectRef::SPLAT(&SPLAT { value, .. }) => {
            let vty = visitexpr(tcx, value);
            unifyvv(&mut tcx.data.sub, tv, vty);
        },
        ObjectRef::FLAT(FLAT { idx, .. }) => {
            unifyvt(&mut tcx.data.sub, tv, Ty::UNIT);
            for &i in idx {
                if objs[i].op != Obj::SPEC {
                    let ety = visitexpr(tcx, i);
                    let (e, _) = unpacktensor(&mut tcx.data.sub, Ty::link(ety), scope);
                    unifyvt(&mut tcx.data.sub, e, Ty::primitive(PRI_IDX));
                }
            }
        },
        ObjectRef::KINT(&KINT { k, .. }) => unifyvpri(&mut tcx.data.sub, tv, kintpri(k as _)),
        ObjectRef::KINT64(&KINT64 { k, .. }) => unifyvpri(&mut tcx.data.sub, tv, kintpri(tcx.intern[k])),
        ObjectRef::KFP64(&KFP64 { k, .. }) => unifyvpri(&mut tcx.data.sub, tv, kfpri(tcx.intern[k])),
        ObjectRef::KSTR(_) => unifyvt(&mut tcx.data.sub, tv, Ty::primitive(Primitive::STR)),
        ObjectRef::TUPLE(TUPLE { fields, .. }) => {
            let ty = visittuple(tcx, fields);
            unifyvt(&mut tcx.data.sub, tv, ty);
        },
        ObjectRef::LET(&LET { value, expr, .. }) => {
            let vty = visitexpr(tcx, value);
            tcx.data.locals.push(vty);
            let ety = visitexpr(tcx, expr);
            tcx.data.locals.raw.pop();
            unifyvv(&mut tcx.data.sub, tv, ety);
        },
        ObjectRef::LGET(&LGET { slot, .. }) => {
            let lv = tcx.data.locals[slot];
            unifyvv(&mut tcx.data.sub, lv, tv)
        },
        ObjectRef::APPLY(&APPLY { func, ref args, .. }) => {
            let func: FuncId = zerocopy::transmute!(objs[func].name);
            let aty = visittuple(tcx, args);
            let ty = newcontype(&mut tcx.data.sub, Constructor::Func, &[aty, Ty::link(tv)]);
            let (generics, fty) = instantiatef(&mut tcx.data, func);
            tcx.data.sub[tv+1] = Tv::bound(Ty::link(generics));
            unifytt(&mut tcx.data.sub, fty, ty);
        },
        ObjectRef::PGET(&PGET { idx, .. }) => {
            match tcx.data.func_args {
                Some(args) => {
                    let t = indextuple(&mut tcx.data.sub, args, idx as _);
                    unifyvv(&mut tcx.data.sub, tv, t);
                },
                None => {
                    // dimension
                    unifyvt(&mut tcx.data.sub, tv, Ty::primitive(PRI_IDX));
                }
            }
        },
        ObjectRef::VGET(&VGET { dim, var, ref idx, .. }) => {
            let t = visitvref(tcx, var, idx, dim as _);
            unifyvt(&mut tcx.data.sub, tv, t);
        },
        ObjectRef::CAT(CAT { elems, .. } ) => {
            let e = newtypevar(&mut tcx.data.sub, scope);
            let d = newtypevar(&mut tcx.data.sub, scope);
            let ty = Ty::constructor(Constructor::Tensor, e);
            unifyvt(&mut tcx.data.sub, tv, ty);
            for &v in elems {
                let ety = visitexpr(tcx, v);
                if objs[v].op == Obj::SPLAT {
                    unifyvt(&mut tcx.data.sub, ety, ty);
                } else {
                    let ety = visitexpr(tcx, v);
                    let (ee, ed) = unpacktensor(&mut tcx.data.sub, Ty::link(ety), scope);
                    unifyvv(&mut tcx.data.sub, e, ee);
                    unifyvt(&mut tcx.data.sub, d, Ty::constructor(Constructor::Next, ed));
                }
            }
        },
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::NEW(NEW { shape, .. }) => {
            for &s in shape {
                // TODO: this (and LOAD) should support all types of integers, but currently lower
                // assumes all lengths are IRT_IDX (this is hardcoded in return slots).
                // this should probably convert to IRT_IDX because there's not much benefit
                // in supporting other length sizes.
                let sty = visitexpr(tcx, s);
                unifyvt(&mut tcx.data.sub, sty, Ty::primitive(PRI_IDX));
            }
            let elem = newtypevar(&mut tcx.data.sub, scope);
            let dim = createdimtype(&mut tcx.data, shape.len() as _);
            let ty = newcontype(&mut tcx.data.sub, Constructor::Tensor,
                &[Ty::link(elem), Ty::link(dim)]);
            unifyvt(&mut tcx.data.sub, tv, ty);
        },
        ObjectRef::TGET(&TGET { value, idx, .. }) => {
            let vty = visitexpr(tcx, value);
            let ety = indextuple(&mut tcx.data.sub, Ty::link(vty), idx as _);
            unifyvv(&mut tcx.data.sub, tv, ety);
        },
        ObjectRef::BINOP(&BINOP { binop, left, right, .. }) => {
            use BinOp::*;
            let td = newtypevar(&mut tcx.data.sub, scope);
            let lty = visitexpr(tcx, left);
            let rty = visitexpr(tcx, right);
            let (le, ld) = unpacktensor(&mut tcx.data.sub, Ty::link(lty), scope);
            let (re, rd) = unpacktensor(&mut tcx.data.sub, Ty::link(rty), scope);
            unifyvv(&mut tcx.data.sub, le, re);
            constraint(&mut tcx.data, Constraint::BinOp(Ty::link(td), Ty::link(ld), Ty::link(rd)));
            let res = match BinOp::from_u8(binop) {
                OR | AND => {
                    unifyvt(&mut tcx.data.sub, le, Ty::primitive(Primitive::B1));
                    Ty::primitive(Primitive::B1)
                },
                EQ | NE => {
                    Ty::primitive(Primitive::B1)
                },
                LT | LE => {
                    unifyvpri(&mut tcx.data.sub, le, PRI_NUM);
                    Ty::primitive(Primitive::B1)
                },
                ADD | SUB | MUL | DIV => {
                    Ty::link(le)
                },
                POW => {
                    unifyvt(&mut tcx.data.sub, le, Ty::primitive(Primitive::F64));
                    Ty::primitive(Primitive::F64)
                }
            };
            let t = newcontype(&mut tcx.data.sub, Constructor::Tensor, &[res, Ty::link(td)]);
            unifyvt(&mut tcx.data.sub, tv, t);
        },
        ObjectRef::INTR(&INTR { func, ref args, .. }) => {
            let t = visitintrinsic(tcx, Intrinsic::from_u8(func), args);
            unifyvt(&mut tcx.data.sub, tv, t);
        }
        ObjectRef::CALL(CALL { inputs, .. }) => {
            for &input in inputs {
                visitexpr(tcx, input);
            }
        },
        _ => unreachable!()
    }
    tv
}

// TODO: need to compute strongly connected components here to implement recursion
fn ftoposort(ccx: &mut Ccx<TypeInfer>, o: ObjRef) {
    let obj = ccx.objs[o];
    if obj.mark != 0 { return }
    ccx.objs[o].mark = 1;
    let mut p = obj.ref_params();
    if Operator::is_expr_raw(ccx.objs[o].op) {
        // skip `ann`, which currently holds the type var
        p.next();
    }
    for i in p {
        let r: ObjRef = zerocopy::transmute!(ccx.objs.get_raw(o)[1+i]);
        if Operator::is_expr_raw(ccx.objs[r].op) || ccx.objs[r].op == Obj::FUNC {
            ftoposort(ccx, r);
        }
    }
    if ccx.objs[o].op == Obj::FUNC {
        let fid = ccx.data.func.end();
        let name = replace(&mut ccx.objs[o.cast::<FUNC>()].name, zerocopy::transmute!(fid));
        ccx.data.func.push(Func { name, obj: o.cast(), type_: Ty::NEVER });
    }
}

fn collectfuncs(ccx: &mut Ccx<TypeInfer>) {
    ccx.objs.clear_marks();
    let mut idx = ObjRef::NIL;
    while let Some(i) = ccx.objs.next(idx) {
        idx = i;
        if ccx.objs[idx].op == Obj::FUNC {
            ftoposort(ccx, idx);
        }
    }
}

fn visitfuncs(ccx: &mut Ccx<TypeInfer>) {
    ccx.data.tab = ObjRef::GLOBAL;
    for fid in index::iter_span(ccx.data.func.end()) {
        let obj = ccx.data.func[fid].obj;
        trace!(TYPE "func {:?}", obj);
        let &FUNC { arity, expr, .. } = &ccx.objs[obj];
        let args = emptypairlist(&mut ccx.data.sub, arity as _, Scope::Local);
        ccx.data.func_args = Some(args);
        let ety = ccx.freeze_graph(|tcx| visitexpr(tcx, expr));
        let ty = newcontype(&mut ccx.data.sub, Constructor::Func, &[args, Ty::link(ety)]);
        ccx.data.func[fid].type_ = ty;
        simplify(&mut ccx.data);
        generalizef(&mut ccx.data, fid);
    }
    ccx.data.func_args = None;
}

fn shapetype(tcx: &mut Tcx, idx: &[ObjRef<EXPR>]) -> Ty {
    let base = tcx.tmp.end();
    let fields = tcx.tmp.align_for::<Ty>();
    let mut nils = 0;
    for &i in idx {
        let ety = if i.is_nil() {
            nils += 1;
            Ty::UNIT
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
            newcontype(&mut tcx.data.sub, Constructor::Tensor, &[Ty::primitive(PRI_IDX), Ty::link(dim)])
        } else {
            Ty::primitive(PRI_IDX)
        };
        fields.push(ety);
    }
    debug_assert!(nils == 0);
    let ty = newpairlist(&mut tcx.data.sub, &fields[base.cast_up()..]);
    tcx.tmp.truncate(base);
    ty
}

fn modeltype(tcx: &mut Tcx, vsets: &[ObjRef<VSET>]) -> Ty {
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
                unifyvt(&mut tcx.data.sub, ety, ty);
            },
            ObjectRef::MOD(&MOD { tab, guard, value, ref outputs, .. }) => {
                trace!(TYPE "mod {:?}", idx);
                tcx.data.tab = tab;
                if !guard.is_nil() {
                    let ety = visitexpr(tcx, guard);
                    unifyvt(&mut tcx.data.sub, ety, Ty::primitive(Primitive::B1));
                }
                let ty = modeltype(tcx, outputs);
                let ety = visitexpr(tcx, value);
                unifyvt(&mut tcx.data.sub, ety, ty);
            },
            ObjectRef::QUERY(&QUERY { value, .. }) => {
                trace!(TYPE "query {:?}", idx);
                tcx.data.tab = ObjRef::GLOBAL;
                visitexpr(tcx, value.cast());
            },
            _ => {}
        }
    }
}

fn deannotate(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    loop {
        'body: {
            let op = ccx.objs[idx].op;
            let (ofs, scope) = match op {
                Obj::VAR => (obj_index_of!(VAR, ann), Scope::Global),
                _ if Operator::is_expr_raw(op) => (
                    obj_index_of!(EXPR, ann),
                    if ccx.objs[idx].mark == 0 { Scope::Global } else { Scope::Local }
                ),
                _ => break 'body
            };
            let tv = newtypevar(&mut ccx.data.sub, scope);
            if op == Obj::APPLY {
                // hack: reserve two slots, second slot is pointer to generics
                ccx.data.sub.push(Tv::bound(Ty::NEVER));
            }
            let ann: ObjRef = zerocopy::transmute!(
                replace(&mut ccx.objs.get_raw_mut(idx)[ofs], zerocopy::transmute!(tv)));
            if !ann.is_nil() {
                let ty = ccx.freeze_graph(|ccx| createtype(ccx, ann, scope));
                ccx.data.sub[tv] = Tv::bound(ty);
            } else if op == Obj::VAR && ccx.objs[idx.cast::<VAR>()].tab == ObjRef::STATE {
                // hack: force state vars to FX (TODO: allow non-unit state vars, too)
                ccx.data.sub[tv] = Tv::unbound(Scope::Global, Some(Primitive::FX.into()));
            }
            trace!(TYPE "{:?} -> {:?} ({:?})", idx, tv, ccx.data.sub[tv].unpack());
        }
        let Some(i) = ccx.objs.next(idx) else { return };
        idx = i;
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    Value,
    Dimension
}

// * eliminate type variables
// * multi pri => widest type
// * tensor<t, 0> => t
fn canonicalizet(sub: &mut IndexSlice<TypeVar, Tv>, a: Ty, role: Role) -> Ty {
    use {Constructor::*,Role::*};
    match a.unpack() {
        Type::Link(i) => canonicalizev(sub, i, role),
        Type::Constructor(Tensor, b) => {
            let elem = canonicalizev(sub, b, role);
            let dim = canonicalizev(sub, b+1, Dimension);
            if dim == Ty::UNIT {
                elem
            } else {
                a
            }
        },
        Type::Constructor(Unit, _) => a,
        Type::Constructor(c, b) => {
            debug_assert!(role == match c { Next=>Dimension, _=>Value });
            for i in 0..c.arity() as isize {
                canonicalizev(sub, b+i, role);
            }
            a
        },
        _ => a
    }
}

fn canonicalizev(sub: &mut IndexSlice<TypeVar, Tv>, a: TypeVar, role: Role) -> Ty {
    use {TVar::*,Role::*};
    let ty = match sub[a].unpack() {
        Bound(t) => {
            let u = canonicalizet(sub, t, role);
            if t == u {
                // skip trace message
                return t
            }
            u
        },
        Unbound(_, None) => match role {
            Value => Ty::primitive(self::Primitive::F64),
            Dimension => Ty::UNIT
        },
        Unbound(_, Some(pri)) => {
            debug_assert!(role == Value);
            match pri.iter().next() {
                Some(pri) => Ty::primitive(pri),
                None => Ty::NEVER
            }
        }
    };
    trace!(TYPE "canon {:?} = {:?} -> {:?}", a, sub[a], ty);
    sub[a] = Tv::bound(ty);
    ty
}

// must match hashtypeobj
// stores type params in ccx.tmp
fn hashtype(ccx: &mut Ccx<TypeInfer>, type_: Type) -> u64 {
    let mut hash = FxHasher::default();
    match type_ {
        Type::Primitive(p) => hash.write_u8(p as _),
        Type::Constructor(Constructor::Tensor, base) => {
            let elem = typeobj(ccx, Ty::link(base));
            let dim = dimension(&ccx.data.sub, Ty::link(base+1)).unwrap();
            debug_assert!(dim > 0);
            hash.write_u32(zerocopy::transmute!(elem));
            hash.write_u8(dim);
            ccx.tmp.push(elem);
            ccx.tmp.push(dim as u32);
        },
        Type::Constructor(Constructor::Pair, mut t) => {
            loop {
                let e = typeobj(ccx, Ty::link(t));
                hash.write_u32(zerocopy::transmute!(e));
                ccx.tmp.push(e);
                let (c, tt) = ccx.data.sub[t+1].unwrap_bound().unwrap_constructor();
                if c == Constructor::Unit { break }
                t = tt;
            }
        },
        Type::Constructor(Constructor::Unit, _) => { /* NOP */ },
        _ => unreachable!()
    }
    hash.finish()
}

// must match hashtype
fn hashtypeobj(o: ObjectRef) -> u64 {
    let mut hash = FxHasher::default();
    match o {
        ObjectRef::TPRI(&TPRI { ty, .. }) => hash.write_u8(ty),
        ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
            hash.write_u32(zerocopy::transmute!(elem));
            hash.write_u8(dim);
        },
        ObjectRef::TTUP(TTUP { elems, .. }) => {
            for &e in elems {
                hash.write_u32(zerocopy::transmute!(e));
            }
        },
        _ => unreachable!()
    }
    hash.finish()
}

fn typeobj(ccx: &mut Ccx<TypeInfer>, ty: Ty) -> ObjRef {
    let type_ = canonicalizet(&mut ccx.data.sub, ty, Role::Value).unpack();
    let base = ccx.tmp.end();
    let hash = hashtype(ccx, type_);
    let work: &[u32] = &ccx.tmp[base.cast_up()..];
    let o = match ccx.data.tobj.entry(
        hash,
        |&t| sametype(ccx.objs.get(t), type_, work),
        |&t| hashtypeobj(ccx.objs.get(t))
    ) {
        Entry::Vacant(e) => *e.insert(createtypeobj(&mut ccx.objs, type_, work)).get(),
        Entry::Occupied(e) => *e.get()
    };
    ccx.tmp.truncate(base);
    o
}

fn fixvars(tcx: &mut Tcx) {
    for (idx,o) in tcx.objs.pairs() {
        if let ObjectRef::VAR(&VAR { ann, .. }) = o {
            trace!(TYPE "fix {:?}", idx);
            canonicalizev(&mut tcx.data.sub, zerocopy::transmute!(ann), Role::Value);
        }
    }
}

const MARK_UNVISITED: u8 = 0;
const MARK_MONO: u8 = 1;
const MARK_POLY: u8 = 2;

fn deephashtype(sub: &IndexSlice<TypeVar, Tv>, generics: TypeVar, hash: &mut FxHasher, ty: Ty) {
    use Type::*;
    match ty.unpack() {
        Link(i) => deephashtype(sub, generics, hash, sub[i].unwrap_bound()),
        Primitive(p) => hash.write_u8(p as _),
        Generic(i) => deephashtype(sub, generics, hash, Ty::link(generics + i as isize)),
        Constructor(c, b) => {
            hash.write_u8(c as _);
            for i in 0..c.arity() as isize {
                deephashtype(sub, generics, hash, Ty::link(b+i));
            }
        }
    }
}

fn hashmonofunc(
    sub: &IndexSlice<TypeVar, Tv>,
    generics: TypeVar,
    mut inst_start: TypeVar,
    inst_end: TypeVar,
    func: FuncId
) -> u64 {
    let mut hash = FxHasher::default();
    hash.write_u32(zerocopy::transmute!(func));
    while inst_start < inst_end {
        deephashtype(sub, generics, &mut hash, Ty::link(inst_start));
        inst_start += 1;
    }
    hash.finish()
}

fn monomorphizetype(sub: &mut IndexVec<TypeVar, Tv>, generics: TypeVar, a: Ty) -> Ty {
    use Type::*;
    match a.unpack() {
        Link(i) => monomorphizetype(sub, generics, sub[i].unwrap_bound()),
        Constructor(_, _) if isconcretetype(sub, a, Scope::Global) => a,
        Constructor(c, b) => {
            let base = sub.end();
            sub.raw.extend(repeat_n(Tv::bound(Ty::NEVER), c.arity() as _));
            for i in 0..c.arity() as isize {
                let t = monomorphizetype(sub, generics, Ty::link(b+i));
                sub[base+i] = Tv::bound(t);
            }
            Ty::constructor(c, base)
        },
        Generic(i) => Ty::link(generics + i as isize),
        Primitive(_) => a
    }
}

fn visitmonoapply(ccx: &mut Ccx<TypeInfer>, apply: ObjRef<APPLY>, callee_generics: TypeVar) {
    let ctx = &mut *ccx.data;
    let APPLY { mark, func, .. } = ccx.objs[apply];
    debug_assert!(mark == MARK_MONO);
    let fid: FuncId = zerocopy::transmute!(ccx.objs[func].name);
    let ngenerics = ctx.func_generic[fid].len();
    let newcallee = match ctx.monotab.entry(
        hashmonofunc(&ctx.sub, ctx.func_generics, callee_generics,
            callee_generics + ngenerics as isize, fid),
        |&id| ctx.mono[id].func == fid && (0..ngenerics).all(|i| equalvv(&ctx.sub,
                Some(ctx.func_generics), callee_generics + i as isize,
                ctx.mono[id].generics + i as isize) == Some(true)),
        |&id| {
            let mono = &ctx.mono[id];
            let n = ctx.func_generic[mono.func].len();
            hashmonofunc(&ctx.sub, zerocopy::transmute!(!0), mono.generics,
                mono.generics + n  as isize, mono.func)
        }
    ) {
        Entry::Vacant(e) => {
            let generics = ctx.sub.end();
            ctx.sub.raw.extend(repeat_n(Tv::bound(Ty::NEVER), ngenerics as _));
            for i in 0..ngenerics as isize {
                let t = monomorphizetype(&mut ctx.sub, ctx.func_generics, Ty::link(callee_generics + i));
                ctx.sub[generics+i] = Tv::bound(t);
            }
            let arity = ccx.objs[func].arity;
            let name = ctx.func[fid].name;
            let obj = match ngenerics {
                0 => func,
                _ => ccx.objs.push(FUNC::new(arity, name, ObjRef::NIL.cast(), ObjRef::NIL))
            };
            let mono = ctx.mono.push(Monomorphization { func: fid, obj, generics });
            e.insert(mono);
            obj
        },
        Entry::Occupied(e) => ctx.mono[*e.get()].obj
    };
    ccx.objs[apply].func = newcallee;
}

fn monomorphizeexpr(ccx: &mut Ccx<TypeInfer>, expr: ObjRef<EXPR>) -> ObjRef<EXPR> {
    debug_assert!(ccx.objs[expr].mark == MARK_POLY);
    let caller_generics = ccx.data.func_generics;
    let tv = zerocopy::transmute!(ccx.objs[expr].ann);
    let tvm = monomorphizetype(&mut ccx.data.sub, caller_generics, Ty::link(tv));
    let tobj = typeobj(ccx, tvm);
    let base = ccx.tmp.end();
    ccx.tmp.write(ccx.objs.get_raw(expr.erase()));
    ccx.tmp[base.cast_up().add(1)] = tobj; // tmp.ann = tobj
    for i in ccx.objs[expr.erase()].ref_params().skip(1) {
        let r: ObjRef = ccx.tmp[base.cast_up().add(1+i)];
        if Operator::is_expr_raw(ccx.objs[r].op) && ccx.objs[r].mark == MARK_POLY {
            let m = monomorphizeexpr(ccx, r.cast());
            ccx.tmp[base.cast_up().add(1+i)] = m;
        }
    }
    let new = ccx.objs.push_raw(&ccx.tmp[base.cast_up()..]);
    ccx.objs[new].mark = MARK_MONO;
    ccx.tmp.truncate(base);
    if ccx.objs[new].op == Obj::APPLY {
        let generics = ccx.data.sub[tv+1].unwrap_bound().unwrap_link();
        visitmonoapply(ccx, new.cast(), generics);
    }
    new.cast()
}

fn visitexprtype(ccx: &mut Ccx<TypeInfer>, expr: ObjRef<EXPR>) {
    if expr.is_builtin() && ccx.objs[expr].mark != MARK_UNVISITED {
        return
    }
    debug_assert!(ccx.objs[expr].mark == MARK_UNVISITED);
    let tv = zerocopy::transmute!(ccx.objs[expr].ann);
    // must canonicalize here because `tv` may have unbound variables
    let ty = canonicalizev(&mut ccx.data.sub, tv, Role::Value);
    let mut ismono = isconcretetype(&ccx.data.sub, ty, Scope::Global);
    for i in ccx.objs[expr.erase()].ref_params().skip(1) {
        let r: ObjRef = zerocopy::transmute!(ccx.objs.get_raw(expr.erase())[1+i]);
        if Operator::is_expr_raw(ccx.objs[r].op) {
            visitexprtype(ccx, r.cast());
            ismono &= ccx.objs[r].mark == MARK_MONO;
        }
    }
    if ismono {
        let tobj = typeobj(ccx, ty);
        ccx.objs[expr].ann = zerocopy::transmute!(tobj);
        ccx.objs[expr].mark = MARK_MONO;
        if ccx.objs[expr].op == Obj::APPLY {
            let generics = ccx.data.sub[tv+1].unwrap_bound().unwrap_link();
            visitmonoapply(ccx, expr.cast(), generics);
        }
    } else {
        ccx.objs[expr].mark = MARK_POLY;
    }
}

fn monoexpr(ccx: &mut Ccx<TypeInfer>, expr: ObjRef<EXPR>) -> ObjRef<EXPR> {
    if ccx.objs[expr].mark == MARK_UNVISITED {
        visitexprtype(ccx, expr);
    }
    if ccx.objs[expr].mark == MARK_MONO {
        expr
    } else {
        monomorphizeexpr(ccx, expr)
    }
}

fn reannotateglobals(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    while let Some(i) = ccx.objs.next(idx) {
        idx = i;
        if (Operator::TAB|Operator::MOD|Operator::VSET|Operator::QUERY).as_u64_truncated()
                & (1 << ccx.objs[idx].op) != 0
        {
            for j in ccx.objs[idx].ref_params() {
                let r: ObjRef = zerocopy::transmute!(ccx.objs.get_raw(idx)[1+j]);
                if Operator::is_expr_raw(ccx.objs[r].op) {
                    visitexprtype(ccx, r.cast());
                }
            }
        } else if ccx.objs[idx].op == Obj::VAR {
            let tv: TypeVar = zerocopy::transmute!(ccx.objs[idx.cast::<VAR>()].ann);
            let tobj = typeobj(ccx, Ty::link(tv));
            ccx.objs[idx.cast::<VAR>()].ann = tobj;
        }
    }
}

fn monomorphizefuncs(ccx: &mut Ccx<TypeInfer>) {
    let mut cursor: MonoId = zerocopy::transmute!(0);
    while cursor < ccx.data.mono.end() {
        let Monomorphization { func, obj, generics } = ccx.data.mono[cursor];
        let Func { obj: prototype_obj, type_, .. } = ccx.data.func[func];
        let expr = ccx.objs[prototype_obj].expr;
        ccx.data.func_generics = generics;
        if trace!(TYPE) {
            let ngenerics = ccx.data.func_generic[func].len();
            trace!(TYPE "monomorphize {:?}", obj);
            for i in 0..ngenerics as isize {
                trace!(TYPE "<{}>: {:?}", i, ccx.data.sub[generics+i].unwrap_bound());
            }
        }
        let exprm = monoexpr(ccx, expr);
        ccx.objs[obj].expr = exprm;
        let (_, args) = type_.unwrap_constructor();
        let args = monomorphizetype(&mut ccx.data.sub, generics, Ty::link(args));
        let args = typeobj(ccx, args);
        ccx.objs[obj].args = args;
        cursor += 1;
    }
}

fn restorefuncs(ccx: &mut Ccx<TypeInfer>) {
    for fid in index::iter_span(ccx.data.func.end()) {
        let Func { obj, name, .. } = ccx.data.func[fid];
        ccx.objs[obj].name = name;
        if !ccx.data.func_generic[fid].is_empty() {
            ccx.objs[obj].op = Obj::FPROT;
        }
    }
}

fn monomorphize(ccx: &mut Ccx<TypeInfer>) {
    ccx.objs.clear_marks();
    reannotateglobals(ccx);
    monomorphizefuncs(ccx);
    restorefuncs(ccx);
}

impl Stage for TypeInfer {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        let mut sub: IndexVec<TypeVar, Tv> = Default::default();
        // ORDER BUILTINTYPE
        sub.push(Tv::bound(Ty::UNIT));
        sub.push(Tv::bound(Ty::V1D));
        Ok(TypeInfer {
            sub,
            con: Default::default(),
            locals: Default::default(),
            func_generic: Default::default(),
            func_con: Default::default(),
            func: Default::default(),
            tobj: Default::default(),
            monotab: Default::default(),
            mono: Default::default(),
            tab: ObjRef::GLOBAL,
            func_args: None,
            func_generics: zerocopy::transmute!(!0),
            dim: (TypeVar::V1D, 1)
        })
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        collectfuncs(ccx);
        deannotate(ccx);
        visitfuncs(ccx);
        ccx.freeze_graph(visitglobals);
        simplify(&mut ccx.data);
        ccx.freeze_graph(fixvars);
        simplify(&mut ccx.data);
        debug_assert!(ccx.data.con.is_empty());
        monomorphize(ccx);
        // TODO: check for errors
        if trace!(TYPE) {
            trace_objs(&ccx.intern, &ccx.objs, ObjRef::NIL);
        }
        Ok(())
    }

}
