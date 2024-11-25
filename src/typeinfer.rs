//! Type inference.

use core::hash::Hasher;

use alloc::vec::Vec;
use enumset::{enum_set, EnumSet};
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use rustc_hash::FxHasher;

use crate::compile::{self, Ccx, Phase};
use crate::dump::trace_objs;
use crate::index::{self, index, IndexVec};
use crate::intrinsics::Intrinsic;
use crate::obj::{obj_index_of, Obj, ObjRef, ObjectRef, Objects, Operator, CALLN, EXPR, KINT, MOD, QUERY, TAB, TCON, TDIM, TPRI, TUPLE, VAR, VGET, VSET};
use crate::trace::trace;
use crate::typestate::{Absent, Access, R};
use crate::typing::{Constructor, Primitive, Scheme};

index!(struct TypeVar(u32) debug("t{}"));

/*
 *       +--------+--------+-------+------+
 *       | 31..29 | 28..16 | 15..8 | 7..0 |
 *       +========+========+=======+======+
 * VAR   |   0    |        typevar        |
 *       +--------+--------+-------+------+
 * DIM   |   1    |                |  dim |
 *       +--------+--------+-------+------+
 * PRI   |   2    |        |  pri enumset |
 *       +--------+--------+-------+------+
 * CON   |   3    |        |   n   |  con |
 *       +--------+--------+-------+------+
 * NEVER |               -2               |
 *       +--------+--------+-------+------+
 * UNSET |               -1               |
 *       +--------------------------------+
 *
 */
#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct Type(u32);

impl Type {

    const UNSET: Self = Self(!0);
    const NEVER: Self = Self(!1);

    fn var(var: TypeVar) -> Self {
        zerocopy::transmute!(var)
    }

    fn dim(dim: u8) -> Self {
        Self((1 << 29) | (dim as u32))
    }

    fn pri<P: Into<EnumSet<Primitive>>>(pri: P) -> Self {
        Self((2 << 29) | pri.into().as_u32_truncated())
    }

    fn con(con: u8, n: u8) -> Self {
        Self((3 << 29) | ((n as u32) << 8) | (con as u32))
    }

    fn unpack(self) -> TypeRepr {
        match self.0 >> 29 {
            0 => TypeRepr::Var(zerocopy::transmute!(self.0)),
            1 => TypeRepr::Dim(self.0 as _),
            2 => TypeRepr::Pri(EnumSet::from_u16_truncated(self.0 as _)),
            3 => TypeRepr::Con(self.0 as _, ((self.0 as u16) >> 8) as _),
            _ if self == Self::NEVER => TypeRepr::Never,
            _ => TypeRepr::Unset
        }
    }

}

#[derive(Clone, Copy, Debug)]
enum TypeRepr {
    Var(TypeVar),
    // TODO: need Par(i) for generic type params
    Dim(u8),
    Pri(EnumSet<Primitive>),
    Con(u8, u8),
    Never,
    Unset
}

// use signed int here so that -1 can be used as a dummy (and checked via "<0")
const PRI_IDX: Primitive = Primitive::I32;

// const PRI_INT: EnumSet<Primitive> = {
//     use Primitive::*;
//     enum_set!(I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64)
// };

const PRI_NUM: EnumSet<Primitive> = {
    use Primitive::*;
    enum_set!(I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64 | F32 | F64)
};


pub struct TypeInfer {
    types: IndexVec<TypeVar, Type>,
    work: Vec<u32>, /* TypeVar, ObjRef */
    typeobj: HashTable<ObjRef>,
    tab: ObjRef<TAB> // table of current expression
}

type Ctx<'a> = Ccx<TypeInfer, R<'a>>;

fn kintpri(v: i64) -> EnumSet<Primitive> {
    use Primitive::*;
    let mut pri = U64 | I64;
    if v == v as i8  as i64 { pri |= U8 | I8 };
    if v == v as i16 as i64 { pri |= U16 | I16 };
    if v == v as i32 as i64 { pri |= U32 | I32 };
    if v == v as f32 as i64 { pri |= F32 };
    if v == v as f64 as i64 { pri |= F64 };
    pri
}

fn newtypevar(types: &mut IndexVec<TypeVar, Type>) -> TypeVar {
    types.push(Type::var(types.end()))
}

fn newtypecon(types: &mut IndexVec<TypeVar, Type>, con: Constructor, par: &[Type]) -> TypeVar {
    debug_assert!(par.iter().all(|p| !matches!(p.unpack(), TypeRepr::Con(..))));
    let tv = types.push(Type::con(con as _, par.len() as _));
    types.raw.extend_from_slice(par);
    tv
}

fn copyobjtype(ccx: &mut Ccx<TypeInfer>, ty: TypeVar, idx: ObjRef) -> TypeVar {
    todo!()
}

fn hashtype(ty: TypeRepr, args: &[u32]) -> u64 {
    let mut hash = FxHasher::default();
    match ty {
        TypeRepr::Pri(p) => hash.write_u16(p.as_u16_truncated()),
        TypeRepr::Dim(d) => hash.write_u8(d),
        TypeRepr::Con(c, _) => {
            hash.write_u8(c);
            for a in args.iter().cloned() { hash.write_u32(a) }
        },
        TypeRepr::Var(_) | TypeRepr::Unset | TypeRepr::Never => unreachable!()
    }
    hash.finish()
}

fn hashtypeobj(o: ObjectRef) -> u64 {
    let mut hash = FxHasher::default();
    match o {
        ObjectRef::TPRI(&TPRI { ty, .. }) => hash.write_u16(1 << ty),
        ObjectRef::TDIM(&TDIM { dim, .. }) => hash.write_u8(dim),
        ObjectRef::TCON(&TCON { con, ref args, .. }) => {
            hash.write_u8(con);
            for a in args.iter().cloned() { hash.write_u32(zerocopy::transmute!(a)) }
        },
        _ => unreachable!()
    }
    hash.finish()
}

fn sametype(a: ObjectRef, b: TypeRepr, par: &[u32]) -> bool {
    match (a, b) {
        (ObjectRef::TPRI(&TPRI { ty, .. }), TypeRepr::Pri(p)) => p.as_u16_truncated() == 1 << ty,
        (ObjectRef::TDIM(&TDIM { dim, .. }), TypeRepr::Dim(d)) => dim == d,
        (ObjectRef::TCON(&TCON { con, ref args, .. }), TypeRepr::Con(c, _))
            => con == c
            && args.len() == par.len()
            && args.iter().cloned().zip(par.iter().cloned()).all(|(a,p)| p == zerocopy::transmute!(a)),
        _ => false
    }
}

fn createtypeobj(objs: &mut Objects, ty: TypeRepr, args: &[u32]) -> ObjRef {
    match ty {
        TypeRepr::Pri(p) => objs.push(&TPRI::new(p.into_iter().next().unwrap() as _)).erase(),
        TypeRepr::Dim(d) => objs.push(&TDIM::new(d)).erase(),
        TypeRepr::Con(con, _) => {
            // XXX replace with zerocopy::transmute when it can do that
            let args: &[ObjRef] = unsafe {
                core::slice::from_raw_parts(args.as_ptr().cast(), args.len())
            };
            objs.push(&TCON::new(con, args)).erase()
        },
        TypeRepr::Var(_) | TypeRepr::Unset | TypeRepr::Never => unreachable!()
    }
}

fn createtype(objs: &Objects, types: &mut IndexVec<TypeVar, Type>, idx: ObjRef) -> Type {
    match objs.get(idx) {
        ObjectRef::NIL(_) => Type::UNSET,
        ObjectRef::TPRI(&TPRI { ty, .. }) => Type::pri(EnumSet::from_u16_truncated(1 << ty)),
        ObjectRef::TDIM(&TDIM { dim, .. }) => Type::dim(dim),
        ObjectRef::TCON(&TCON { con, ref args, .. }) => {
            let ty = types.push(Type::con(con, args.len() as _));
            for _ in args { types.push(Type::UNSET); }
            for (i, &arg) in args.iter().enumerate() {
                types[ty+i as isize] = createtype(objs, types, arg);
            }
            Type::var(ty)
        },
        _ => unreachable!()
    }
}

fn totypevar(types: &mut IndexVec<TypeVar, Type>, ty: Type) -> TypeVar {
    match ty.unpack() {
        TypeRepr::Var(tv) => tv,
        _ => types.push(ty)
    }
}

fn typeobj(ccx: &mut Ccx<TypeInfer>, ty: TypeVar) -> ObjRef {
    match ccx.data.types[ty].unpack() {
        TypeRepr::Var(tv) => typeobj(ccx, tv),
        type_ => {
            let base = ccx.data.work.len();
            if let TypeRepr::Con(_, n) = type_ {
                for i in 0..n as isize {
                    let o = typeobj(ccx, ty+1+i);
                    ccx.data.work.push(zerocopy::transmute!(o));
                }
            }
            let tx = &mut *ccx.data;
            let args = &tx.work[base..];
            let idx = match tx.typeobj.entry(
                hashtype(type_, args),
                |t| sametype(ccx.objs.get(*t), type_, args),
                |t| hashtypeobj(ccx.objs.get(*t))
            ) {
                Entry::Vacant(e) => *e.insert(createtypeobj(&mut ccx.objs, type_, args)).get(),
                Entry::Occupied(e) => *e.get()
            };
            tx.work.truncate(base);
            idx
        }
    }
}

fn puttypeobj(ccx: &mut Ccx<TypeInfer>, idx: ObjRef) {
    if let Entry::Vacant(e) = ccx.data.typeobj.entry(
        hashtypeobj(ccx.objs.get(idx)),
        |&i| ccx.objs.equal(i, idx),
        |&i| hashtypeobj(ccx.objs.get(i))
    ) {
        e.insert(idx);
    }
}

fn init(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    while let Some(i) = ccx.objs.next(idx) {
        idx = i;
        match ccx.objs[idx].op {
            op if Operator::is_expr_raw(op) => {
                let ann = ccx.objs[idx.cast::<EXPR>()].ann;
                let ty = createtype(&ccx.objs, &mut ccx.data.types, ann);
                let ann = zerocopy::transmute!(totypevar(&mut ccx.data.types, ty));
                ccx.objs[idx.cast::<EXPR>()].ann = ann;
            },
            op if op == Operator::VAR as _ => {
                let ann = ccx.objs[idx.cast::<VAR>()].ann;
                let ty = createtype(&ccx.objs, &mut ccx.data.types, ann);
                let tv = totypevar(&mut ccx.data.types, ty);
                if ty == Type::UNSET { ccx.data.types[tv] = Type::var(tv); }
                let ann = zerocopy::transmute!(tv);
                ccx.objs[idx.cast::<VAR>()].ann = ann;
            },
            op if Operator::is_type_raw(op) => puttypeobj(ccx, idx),
            _ => {}
        }
    }
}

// set a = b
fn unify(types: &mut IndexVec<TypeVar, Type>, a: TypeVar, b: Type) {
    use TypeRepr::*;
    let ta = types[a];
    trace!(TYPE "unify {:?} {:?} = {:?}", a, ta.unpack(), b.unpack());
    match (ta.unpack(), b.unpack()) {
        (_, Var(j)) if j == a => { /* ok */ },
        (Var(i), _) if a == i => types[a] = b,
        (Var(mut i), _) => {
            // shorten the var chain while we are here.
            // this is not required for correctness, but makes it do less work.
            while let Var(j) = types[i].unpack() {
                if i == j { break }
                i = j;
                trace!(TYPE "      (={:?})", i);
            }
            types[a] = Type::var(i);
            unify(types, i, b);
        },
        (Pri(_), Pri(_)) => types[a].0 &= b.0,
        (Pri(_), Var(j)) if matches!(types[j].unpack(), Pri(_)) => {
            types[a] = b;
            types[j].0 &= ta.0;
        },
        (Pri(_), Var(j)) => unify(types, j, Type::var(a)),
        (Con(Constructor::TENSOR, _), tb) if matches!(tb, Pri(_))
            || matches!(tb, Var(j) if matches!(types[j].unpack(), Pri(_))) =>
        {
            unify(types, a+1, b);
            unify(types, a+2, Type::dim(0));
        },
        (Con(ca, na), Var(j)) => match types[j].unpack() {
            Con(cb, nb) if (ca, na) == (cb, nb) => {
                for i in 1..=na as isize {
                    unify(types, a+i, Type::var(j+i));
                }
            },
            Con(..) => unify(types, a, Type::NEVER),
            _ => unify(types, j, Type::var(a)),
        },
        (_, Var(j)) => unify(types, j, ta),
        (Dim(i), Dim(j)) if i == j => { /* ok */ },
        _ => {
            types[a] = Type::NEVER;
            trace!(TYPE "***** {:?} = NEVER", a);
        }
    }
}

// set type(idx) = int|splat
// return type(var[idx])
fn vidxtype(ctx: &mut Ctx, var: ObjRef<VAR>, idx: &[ObjRef<EXPR>]) -> TypeVar {
    let need = ctx.objs.dim(ctx.objs[var].tab);
    let mut have = idx.len();
    if have < need {
        // not enough indices mentioned, insert current expression's index.
        // these are scalar indices, so they don't increase the dimension.
        // if this results in too many indices being mentioned, it's a type error.
        have += ctx.objs.dim(ctx.data.tab);
    }
    if have > need {
        // too many indices mentioned.
        return ctx.data.types.push(Type::NEVER);
    }
    // any missing dimension is an implicit splat
    let mut dims = need - have;
    for &i in idx.iter() {
        let EXPR { op, data, .. } = ctx.objs[i];
        let ity = if (op, data) == (Operator::CALLN as _, Intrinsic::SPLAT as _) {
            dims += 1;
            Type::var(newtypecon(&mut ctx.data.types, Constructor::Splat, &[Type::pri(PRI_IDX)]))
        } else {
            Type::pri(PRI_IDX)
        };
        unifyexpr(ctx, i, ity);
    }
    let mut vty = zerocopy::transmute!(ctx.objs[var].ann);
    if dims > 0 {
        vty = newtypecon(&mut ctx.data.types, Constructor::Tensor,
            &[Type::var(vty), Type::dim(dims as _)]);
    }
    vty
}

// set (ty, type(args)) = (ret(signature), args(signature))
fn unifycall(ctx: &mut Ctx, args: &[ObjRef<EXPR>], mut signature: TypeVar, ty: Type) {
    unify(&mut ctx.data.types, signature, ty);
    for a in args.iter().cloned() {
        signature += 1;
        unifyexpr(ctx, a, Type::var(signature));
    }
}

fn instantiate(
    scheme: &Scheme,
    types: &mut IndexVec<TypeVar, Type>,
    work: &mut Vec<u32>
) -> TypeVar {
    let base = types.end();
    for _ in 0..scheme.num_generics() {
        newtypevar(types);
    }
    let bytecode = scheme.bytecode();
    let mut ip = 0;
    while let Some(&bc) = bytecode.get(ip) {
        let data = bc & ((1 << Scheme::DATA_BITS)-1);
        match bc>>Scheme::DATA_BITS {
            Scheme::BC_PRI => {
                ip += 1;
                let mask = ((data as u16) << 8) | (bytecode[ip] as u16);
                let tv = zerocopy::transmute!(work.pop().unwrap());
                unify(types, tv, Type::pri(EnumSet::from_u16_truncated(mask)));
            },
            Scheme::BC_CON => {
                ip += 1;
                let n = bytecode[ip];
                let ty = types.push(Type::con(data, n));
                // NOTE: assumes Type::var and TypeVar can transmute
                types.raw.extend(work[work.len()-n as usize..].iter().cloned().map(Type));
                work.truncate(work.len()-n as usize);
                work.push(zerocopy::transmute!(ty));
            },
            _ /* BC_GEN */ => {
                work.push(zerocopy::transmute!(base + data as isize));
            }
        }
        ip += 1;
    }
    debug_assert!(work.len() == 1);
    zerocopy::transmute!(work.pop().unwrap())
}

// set type(expr) = ty, where ty :: var|pri
fn unifyexpr(ctx: &mut Ctx, idx: ObjRef<EXPR>, ty: Type) {
    let objs = Access::borrow(&ctx.objs);
    let tv: TypeVar = zerocopy::transmute!(objs[idx].ann);
    if ctx.data.types[tv] != Type::UNSET {
        unify(&mut ctx.data.types, tv, ty);
        return;
    }
    trace!(TYPE "expr  {:?} = {:?}", tv, ty.unpack());
    ctx.data.types[tv] = ty;
    let ty = Type::var(tv);
    match objs.get(idx.erase()) {
        ObjectRef::KINT(&KINT { k, .. }) => unify(&mut ctx.data.types, tv,
            Type::pri(kintpri(k as _))),
        ObjectRef::KREF(_) => todo!(),
        ObjectRef::DIM(_) => unify(&mut ctx.data.types, tv, Type::pri(PRI_IDX)),
        ObjectRef::TUPLE(&TUPLE { ref fields, .. }) => {
            let tup = ctx.data.types.push(Type::con(Constructor::Tuple as _, fields.len() as _));
            for _ in fields { newtypevar(&mut ctx.data.types); }
            unifycall(ctx, fields, tup, ty);
        },
        ObjectRef::VGET(&VGET { var, ref idx, .. }) => {
            let vty = vidxtype(ctx, var, idx);
            unify(&mut ctx.data.types, vty, ty);
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(_) => todo!(),
        ObjectRef::GET(_) => todo!(),
        ObjectRef::FREF(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { func, ref args, .. }) => {
            let tx = &mut *ctx.data;
            let sig = instantiate(Intrinsic::from_u8(func).scheme(), &mut tx.types, &mut tx.work);
            unifycall(ctx, args, sig+1, ty);
        },
        ObjectRef::CALLX(_) => todo!(),
        _ => unreachable!()
    }
}

fn maketabtype(ctx: &mut Ctx, dims: u8) -> TypeVar {
    let TypeInfer { types, work, .. } = &mut *ctx.data;
    for _ in 0..dims {
        let dim = types.push(Type::con(Constructor::Tensor as _, 2));
        work.push(zerocopy::transmute!(dim));
        types.push(Type::pri(PRI_IDX));
        newtypevar(types);
    }
    let tv = types.push(Type::con(Constructor::Tuple as _, dims));
    types.raw.extend(work.iter().map(|&t| Type::var(zerocopy::transmute!(t))));
    work.clear();
    tv
}

fn infertoplevel(ctx: &mut Ctx) {
    let objs = Access::borrow(&ctx.objs);
    for (_, o) in objs.pairs() {
        match o {
            ObjectRef::TAB(&TAB { shape, .. }) => {
                ctx.data.tab = ObjRef::GLOBAL;
                let dims = ctx.objs[shape].fields.len();
                let ty = maketabtype(ctx, dims as _);
                unifyexpr(ctx, shape.cast(), Type::var(ty));
            },
            ObjectRef::MOD(&MOD { tab, guard, ref value, .. }) => {
                ctx.data.tab = tab;
                if !guard.is_nil() {
                    unifyexpr(ctx, guard, Type::pri(Primitive::B1));
                }
                for &vset in value.iter() {
                    let &VSET { var, value, ref idx, .. } = &objs[vset];
                    let vty = vidxtype(ctx, var, idx);
                    unifyexpr(ctx, value, Type::var(vty));
                }
            },
            ObjectRef::FUNC(_) => todo!(),
            ObjectRef::QUERY(&QUERY { tab, ref value, .. }) => for &v in value {
                ctx.data.tab = tab;
                let ann: TypeVar = zerocopy::transmute!(objs[v].ann);
                debug_assert!(ctx.data.types[ann] == Type::UNSET);
                unifyexpr(ctx, v, Type::var(ann));
            },
            _ => {}
        }
    }
}

// * eliminate unnecessary type variables
// * empty pri => never
// * multi pri => widest type
// * unset => never
// * tensor<t, 0> => t
fn canonty(types: &mut IndexVec<TypeVar, Type>, tv: TypeVar) -> Type {
    use TypeRepr::*;
    let mut ty = types[tv];
    ty = match ty.unpack() {
        // fresh type variable, ie. the type is completely unbounded.
        // treat this as equivalent to pri(all), which evaluates to f64.
        // (in other words, if there's nothing bounding a type, we choose it to be scalar f64).
        Var(i) if i == tv => Type::pri(Primitive::F64),
        Var(i) => canonty(types, i),
        Pri(p) if p.len() != 1 => match (p & PRI_NUM).as_u16_truncated() as i16 {
            0   => Type::NEVER,
            pri => Type::pri(EnumSet::from_u16_truncated((pri & -pri) as _))
        },
        Unset => Type::NEVER,
        // args are already canonicalized because we go backwards
        Con(Constructor::TENSOR, _) if types[tv+2] == Type::dim(0) => types[tv+1],
        Con(_, _) => return Type::var(tv),
        _ => return ty
    };
    types[tv] = ty;
    ty
}

fn canonicalize(types: &mut IndexVec<TypeVar, Type>) {
    for tv in index::iter_span(types.end()).rev() {
        canonty(types, tv);
    }
}

fn setannotations(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    while let Some(i) = ccx.objs.next(idx) {
        idx = i;
        let ofs = match ccx.objs[idx].op {
            Obj::VAR => obj_index_of!(VAR, ann),
            op if Operator::is_expr_raw(op) => obj_index_of!(EXPR, ann),
            _ => continue
        };
        let ann: TypeVar = zerocopy::transmute!(ccx.objs.get_raw(idx)[ofs]);
        let ann = typeobj(ccx, ann);
        ccx.objs.get_raw_mut(idx)[ofs] = zerocopy::transmute!(ann);
    }
}

impl Phase for TypeInfer {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(TypeInfer {
            types: Default::default(),
            work: Default::default(),
            typeobj: Default::default(),
            tab: ObjRef::NIL.cast()
        })
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        init(ccx);
        ccx.freeze_graph(infertoplevel);
        canonicalize(&mut ccx.data.types);
        setannotations(ccx);
        if trace!(TYPE) {
            trace_objs(&ccx.constants, &ccx.sequences, &ccx.objs, ObjRef::NIL);
        }
        Ok(())
    }

}
