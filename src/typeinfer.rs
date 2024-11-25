//! Type inference.

use core::hash::Hasher;
use core::iter::zip;

use alloc::vec::Vec;
use enumset::{enum_set, EnumSet};
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use rustc_hash::FxHasher;

use crate::compile::{self, Ccx, Phase};
use crate::dump::trace_objs;
use crate::index::{self, index, IndexSlice, IndexVec};
use crate::intrinsics::Intrinsic;
use crate::obj::{obj_index_of, Obj, ObjRef, ObjectRef, Objects, Operator, CALLN, CALLX, EXPR, GET, KFP64, KINT, KINT64, MOD, QUERY, TAB, TPRI, TTEN, TTUP, TUPLE, VAR, VGET, VSET};
use crate::trace::trace;
use crate::typestate::{Absent, Access, R};
use crate::typing::{Constructor, Primitive, Scheme, SchemeBytecode};

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

    const UNVISITED: Self = Self(!0);
    const NEVER: Self = Self(2 << 29);
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
        debug_assert!(self != Self::UNVISITED);
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

// use signed int here so that -1 can be used as a dummy (and checked via "<0")
const PRI_IDX: Primitive = Primitive::I32;

const PRI_NUM: EnumSet<Primitive> = {
    use Primitive::*;
    enum_set!(I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64 | F32 | F64)
};

pub struct TypeInfer {
    tvar: IndexVec<TypeVar, Type>,
    work: Vec<u32>, /* TypeVar, ObjRef */
    typeobj: HashTable<ObjRef>,
    tab: ObjRef<TAB> // table of current expression
}

type Ctx<'a> = Ccx<TypeInfer, R<'a>>;

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

fn newtypevar(tvar: &mut IndexVec<TypeVar, Type>) -> TypeVar {
    tvar.push(Type::var(tvar.end()))
}

fn newcontype(tvar: &mut IndexVec<TypeVar, Type>, con: Constructor, par: &[Type]) -> Type {
    let base = tvar.end();
    tvar.raw.extend_from_slice(par);
    Type::con(con as _, base)
}

fn newpairtype(tvar: &mut IndexVec<TypeVar, Type>, left: Type, right: Type) -> Type {
    newcontype(tvar, Constructor::Pair, &[left, right])
}

// must match hashtypeobj
// stores type params in typeinfer.work
fn hashtype(ccx: &mut Ccx<TypeInfer>, ty: TypeRepr) -> u64 {
    use TypeRepr::*;
    let mut hash = FxHasher::default();
    match ty {
        Pri(p) => hash.write_u16(p.as_u16_truncated()),
        Con(Constructor::TENSOR, base) => {
            let elem = typeobj(ccx, Type::var(base));
            let TypeRepr::Dim(dim) = ccx.data.tvar[base+1].unpack() else { unreachable!() };
            hash.write_u32(zerocopy::transmute!(elem));
            hash.write_u8(dim);
            ccx.data.work.push(zerocopy::transmute!(elem));
            ccx.data.work.push(dim as _);
        },
        Con(Constructor::PAIR, mut t) => {
            loop {
                let e = typeobj(ccx, Type::var(t));
                hash.write_u32(zerocopy::transmute!(e));
                ccx.data.work.push(zerocopy::transmute!(e));
                let TypeRepr::Con(c, tt) = ccx.data.tvar[t+1].unpack() else { unreachable!() };
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

fn createtypeobj(objs: &mut Objects, ty: TypeRepr, work: &[u32]) -> ObjRef {
    use TypeRepr::*;
    match ty {
        // TODO: this (or before calling this) should check that the pri is not NEVER
        //       (this unwrap can fail)
        Pri(p) => objs.push(TPRI::new(p.into_iter().next().unwrap() as _)).erase(),
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

fn createtype(objs: &Objects, tvar: &mut IndexVec<TypeVar, Type>, idx: ObjRef) -> Type {
    match objs.get(idx) {
        ObjectRef::TPRI(&TPRI { ty, .. }) => Type::pri(EnumSet::from_u16_truncated(1 << ty)),
        ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
            let e = createtype(objs, tvar, elem);
            newcontype(tvar, Constructor::Tensor, &[e, Type::dim(dim)])
        },
        ObjectRef::TTUP(&TTUP { ref elems, .. }) => {
            let mut ty = Type::UNIT;
            for &e in elems.iter().rev() {
                let ety = createtype(objs, tvar, e);
                ty = newpairtype(tvar, ety, ty);
            }
            ty
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

fn typeobj(ccx: &mut Ccx<TypeInfer>, ty: Type) -> ObjRef {
    match ty.unpack() {
        TypeRepr::Var(tv) => return typeobj(ccx, ccx.data.tvar[tv]),
        type_ => {
            let base = ccx.data.work.len();
            let hash = hashtype(ccx, type_);
            let tx = &mut *ccx.data;
            let work = &tx.work[base..];
            let o = match tx.typeobj.entry(
                hash,
                |&t| sametype(ccx.objs.get(t), type_, work),
                |&t| hashtypeobj(ccx.objs.get(t))
            ) {
                Entry::Vacant(e) => *e.insert(createtypeobj(&mut ccx.objs, type_, work)).get(),
                Entry::Occupied(e) => *e.get()
            };
            tx.work.truncate(base);
            o
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

// set a=b
fn unify(tvar: &mut IndexSlice<TypeVar, Type>, a: TypeVar, b: Type) {
    use TypeRepr::*;
    trace!(TYPE "unify {:?}:{:?} = {:?}", a, tvar[a].unpack(), b.unpack());
    match (tvar[a].unpack(), b.unpack()) {
        (Var(i), _) if i == a => tvar[a] = b,
        (Var(i), _) => unify(tvar, i, b),
        (Pri(_), Pri(_)) => tvar[a].0 &= b.0,
        (Pri(_), Var(k)) if matches!(tvar[k].unpack(), Pri(_)) => {
            tvar[k].0 &= tvar[a].0;
            tvar[a] = b;
        },
        (Pri(_), Con(Constructor::TENSOR, b0)) => {
            unify(tvar, b0, Type::var(a));
            unify(tvar, b0+1, Type::dim(0));
        },
        (Con(Constructor::TENSOR, a0), Pri(_)) => {
            unify(tvar, a0, b);
            unify(tvar, a0+1, Type::dim(0));
        },
        (Con(ca, ba), Con(cb, bb)) if ca == cb => {
            for i in 0..Constructor::from_u8(ca).arity() as isize {
                unify(tvar, ba+i, Type::var(bb+i));
            }
        },
        (Dim(i), Dim(j)) if i == j => { /* ok */ },
        (_, Var(j)) => unify(tvar, j, tvar[a]),
        _ => {
            tvar[a] = Type::NEVER;
            trace!(TYPE "***** {:?} = NEVER", a);
        }
    }
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct ExprAnn {
    expr: ObjRef<EXPR>,
    ann: Type
}

fn init(ccx: &mut Ccx<TypeInfer>) {
    let mut idx = ObjRef::NIL;
    let base = ccx.tmp.end();
    while let Some(i) = ccx.objs.next(idx) {
        idx = i;
        match ccx.objs[idx].op {
            op if Operator::is_expr_raw(op) => {
                let ann = ccx.objs[idx.cast::<EXPR>()].ann;
                let tv = ccx.data.tvar.push(Type::UNVISITED);
                ccx.objs[idx.cast::<EXPR>()].ann = zerocopy::transmute!(tv);
                if !ann.is_nil() {
                    // special case: TRUE and FALSE are KINT, but should get a boolean type
                    // instead of a numeric type.
                    if idx == ObjRef::TRUE.cast() || idx == ObjRef::FALSE.cast() {
                        ccx.data.tvar[tv] = Type::pri(Primitive::B1);
                    } else {
                        ccx.tmp.push(ExprAnn {
                            expr: idx.cast(),
                            ann: createtype(&ccx.objs, &mut ccx.data.tvar, ann)
                        });
                    }
                }
            },
            op if op == Operator::VAR as _ => {
                let ann = match ccx.objs[idx.cast::<VAR>()].ann {
                    a if a == ObjRef::NIL => newtypevar(&mut ccx.data.tvar),
                    a => {
                        let ty = createtype(&ccx.objs, &mut ccx.data.tvar, a);
                        totypevar(&mut ccx.data.tvar, ty)
                    }
                };
                ccx.objs[idx.cast::<VAR>()].ann = zerocopy::transmute!(ann);
            },
            op if Operator::is_type_raw(op) => puttypeobj(ccx, idx),
            _ => {}
        }
    }
    ccx.freeze_graph(|ctx| {
        let mut ptr = base.cast_up();
        let end = ctx.tmp.end().cast::<ExprAnn>();
        while ptr < end {
            let &ExprAnn { expr, ann } = &ctx.tmp[ptr];
            unifyexpr(ctx, expr, ann);
            ptr = ptr.add_size(1);
        }
    });
    ccx.tmp.truncate(base);
}

// set type(idx) = int|splat
// return type(var[idx])
fn vidxtype(ctx: &mut Ctx, var: ObjRef<VAR>, idx: &[ObjRef<EXPR>]) -> Type {
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
        return Type::NEVER;
    }
    // any missing dimension is an implicit splat
    let dims = need - have;
    for &i in idx.iter() {
        // let EXPR { op, data, .. } = ctx.objs[i];
        // let ity = if (op, data) == (Operator::CALLN as _, Intrinsic::SPLAT as _) {
        //     dims += 1;
        //     Type::var(newtypecon(&mut ctx.data.types, Constructor::Splat, &[Type::pri(PRI_IDX)]))
        // } else {
        //     Type::pri(PRI_IDX)
        // };
        // TODO: explicit splats
        let ity = Type::pri(PRI_IDX);
        unifyexpr(ctx, i, ity);
    }
    let mut vty: Type = zerocopy::transmute!(ctx.objs[var].ann);
    if dims > 0 {
        vty = newcontype(&mut ctx.data.tvar, Constructor::Tensor, &[vty, Type::dim(dims as _)]);
    }
    vty
}

// note: this assumes Type::var and TypeVar have the same representation
fn instantiate(scheme: &Scheme, tvar: &mut IndexVec<TypeVar, Type>, work: &mut Vec<u32>) -> Type {
    let base = tvar.end();
    for _ in 0..scheme.num_generics() {
        newtypevar(tvar);
    }
    for &ins in scheme.bytecode() {
        match SchemeBytecode::decode(ins) {
            SchemeBytecode::PriNum | SchemeBytecode::PriBool => {
                let tv: TypeVar = zerocopy::transmute!(work.pop().unwrap());
                let cst = match ins == SchemeBytecode::PriNum.encode() {
                    true  => Type::pri(PRI_NUM),
                    false => Type::pri(Primitive::B1)
                };
                unify(tvar, tv, cst);
            },
            SchemeBytecode::Con(con) => {
                let base = tvar.end();
                let n = con.arity() as usize;
                tvar.raw.extend(work[work.len()-n..].iter().cloned().map(Type));
                work.truncate(work.len()-n);
                work.push(zerocopy::transmute!(Type::con(con as _, base)));
            },
            SchemeBytecode::Gen(idx) => {
                work.push(zerocopy::transmute!(base + idx as isize));
            }
        }
    }
    debug_assert!(work.len() == 1);
    zerocopy::transmute!(work.pop().unwrap())
}

fn unifytuple(ctx: &mut Ctx, elems: &[ObjRef<EXPR>]) -> Type {
    let mut ty = Type::UNIT;
    for &e in elems.iter().rev() {
        let t = Type::var(newtypevar(&mut ctx.data.tvar));
        unifyexpr(ctx, e, t);
        ty = newpairtype(&mut ctx.data.tvar, t, ty);
    }
    ty
}

// set type(expr) = ty, where ty :: var|pri
fn unifyexpr(ctx: &mut Ctx, idx: ObjRef<EXPR>, ty: Type) {
    let objs = Access::borrow(&ctx.objs);
    let tv: TypeVar = zerocopy::transmute!(objs[idx].ann);
    if ctx.data.tvar[tv] != Type::UNVISITED {
        unify(&mut ctx.data.tvar, tv, ty);
        return;
    }
    trace!(TYPE "expr  {:?} = {:?}", tv, ty.unpack());
    ctx.data.tvar[tv] = ty;
    match objs.get(idx.erase()) {
        ObjectRef::KINT(&KINT { k, .. }) => unify(&mut ctx.data.tvar, tv,
            Type::pri(kintpri(k as _))),
        ObjectRef::KINT64(&KINT64 { k, .. }) => unify(&mut ctx.data.tvar, tv,
            Type::pri(kintpri(ctx.intern.bump()[k].get()))),
        ObjectRef::KFP64(&KFP64 { k, .. }) => unify(&mut ctx.data.tvar, tv,
            Type::pri(kfpri(ctx.intern.bump()[k].get()))),
        ObjectRef::KSTR(_) => unify(&mut ctx.data.tvar, tv, Type::pri(Primitive::STR)),
        ObjectRef::DIM(_) => unify(&mut ctx.data.tvar, tv, Type::pri(PRI_IDX)),
        ObjectRef::TUPLE(&TUPLE { ref fields, .. }) => {
            let tt = unifytuple(ctx, fields);
            unify(&mut ctx.data.tvar, tv, tt);
        },
        ObjectRef::VGET(&VGET { var, ref idx, .. }) => {
            let vty = vidxtype(ctx, var, idx);
            unify(&mut ctx.data.tvar, tv, vty);
        },
        ObjectRef::CAT(_) => todo!(),
        ObjectRef::IDX(_) => todo!(),
        ObjectRef::LOAD(_) => todo!(),
        ObjectRef::GET(&GET { value, idx, .. }) => {
            let mut tt = newpairtype(&mut ctx.data.tvar, Type::var(tv), Type::UNIT);
            for _ in 0..idx {
                let t = newtypevar(&mut ctx.data.tvar);
                tt = newpairtype(&mut ctx.data.tvar, Type::var(t), tt);
            }
            unifyexpr(ctx, value, tt);
        },
        ObjectRef::FREF(_) => todo!(),
        ObjectRef::CALL(_) => todo!(),
        ObjectRef::CALLN(&CALLN { func, ref args, .. }) => {
            let tx = &mut *ctx.data;
            let sig = instantiate(Intrinsic::from_u8(func).scheme(), &mut tx.tvar, &mut tx.work);
            let TypeRepr::Con(_, base) = sig.unpack() else { unreachable!() };
            let at = unifytuple(ctx, args);
            unify(&mut ctx.data.tvar, base, at);
            unify(&mut ctx.data.tvar, base+1, Type::var(tv));
        },
        ObjectRef::CALLX(&CALLX { ref inputs, .. }) => {
            for &input in inputs {
                let ty: TypeVar = zerocopy::transmute!(objs[input].ann);
                if ctx.data.tvar[ty] == Type::UNVISITED {
                    unifyexpr(ctx, input, Type::var(ty));
                }
            }
        },
        _ => unreachable!()
    }
}

fn maketabtype(ctx: &mut Ctx, dims: u8) -> Type {
    let tvar = &mut ctx.data.tvar;
    let mut ty = Type::UNIT;
    for _ in 0..dims {
        let base = tvar.end();
        tvar.push(Type::pri(PRI_IDX)); // elem
        newtypevar(tvar); // dim
        ty = newpairtype(tvar, Type::con(Constructor::Tensor as _, base), ty);
    }
    ty
}

fn infertoplevel(ctx: &mut Ctx) {
    let objs = Access::borrow(&ctx.objs);
    for (_, o) in objs.pairs() {
        match o {
            ObjectRef::TAB(&TAB { shape, .. }) => {
                ctx.data.tab = ObjRef::GLOBAL;
                let dims = ctx.objs[shape].fields.len();
                let ty = maketabtype(ctx, dims as _);
                unifyexpr(ctx, shape.cast(), ty);
            },
            ObjectRef::MOD(&MOD { tab, guard, ref value, .. }) => {
                ctx.data.tab = tab;
                if !guard.is_nil() {
                    unifyexpr(ctx, guard, Type::pri(Primitive::B1));
                }
                for &vset in value.iter() {
                    let &VSET { var, value, ref idx, .. } = &objs[vset];
                    let vty = vidxtype(ctx, var, idx);
                    unifyexpr(ctx, value, vty);
                }
            },
            ObjectRef::FUNC(_) => todo!(),
            ObjectRef::QUERY(&QUERY { tab, ref value, .. }) => for &v in value {
                ctx.data.tab = tab;
                let ann: TypeVar = zerocopy::transmute!(objs[v].ann);
                debug_assert!(ctx.data.tvar[ann] == Type::UNVISITED);
                unifyexpr(ctx, v, Type::var(ann));
            },
            _ => {}
        }
    }
}

// * eliminate type variables
// * multi pri => widest type
// * tensor<t, 0> => t
fn canonty(tvar: &mut IndexVec<TypeVar, Type>, tv: TypeVar) -> Type {
    use TypeRepr::*;
    let mut ty = tvar[tv];
    ty = match ty.unpack() {
        // fresh type variable, ie. the type is completely unbounded.
        // treat this as equivalent to pri(all), which evaluates to f64.
        // (in other words, if there's nothing bounding a type, we choose it to be scalar f64).
        Var(i) if i == tv => Type::pri(Primitive::F64),
        Var(i) => canonty(tvar, i),
        Pri(p) if p.len() > 1 => {
            let pri = (p & PRI_NUM).as_u16_truncated() as i16;
            Type::pri(EnumSet::from_u16_truncated((pri & -pri) as _))
        },
        Con(Constructor::TENSOR, base) if canonty(tvar, base+1) == Type::dim(0)
            => canonty(tvar, base),
        _ => return ty
    };
    tvar[tv] = ty;
    ty
}

fn canonicalize(types: &mut IndexVec<TypeVar, Type>) {
    for tv in index::iter_span(types.end()) {
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
        let ann: Type = zerocopy::transmute!(ccx.objs.get_raw(idx)[ofs]);
        let ann = typeobj(ccx, ann);
        ccx.objs.get_raw_mut(idx)[ofs] = zerocopy::transmute!(ann);
    }
}

impl Phase for TypeInfer {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(TypeInfer {
            tvar: Default::default(),
            work: Default::default(),
            typeobj: Default::default(),
            tab: ObjRef::NIL.cast()
        })
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        init(ccx);
        ccx.freeze_graph(infertoplevel);
        canonicalize(&mut ccx.data.tvar);
        setannotations(ccx);
        if trace!(TYPE) {
            trace_objs(&ccx.intern, &ccx.objs, ObjRef::NIL);
        }
        Ok(())
    }

}

// use core::hash::Hasher;
// 
// use alloc::vec::Vec;
// use enumset::{enum_set, EnumSet};
// use hashbrown::hash_table::Entry;
// use hashbrown::HashTable;
// use rustc_hash::FxHasher;
// 
// use crate::compile::{self, Ccx, Phase};
// use crate::dump::trace_objs;
// use crate::index::{self, index, IndexVec};
// use crate::intrinsics::Intrinsic;
// use crate::obj::{obj_index_of, Obj, ObjRef, ObjectRef, Objects, Operator, CALLN, EXPR, KINT, MOD, QUERY, TAB, TCON, TDIM, TPRI, TUPLE, VAR, VGET, VSET};
// use crate::trace::trace;
// use crate::typestate::{Absent, Access, R};
// use crate::typing::{Constructor, Primitive, Scheme};
// 
// index!(struct TypeVar(u32) debug("t{}"));
// 
// /*
//  *       +--------+--------+-------+------+
//  *       | 31..29 | 28..16 | 15..8 | 7..0 |
//  *       +========+========+=======+======+
//  * VAR   |   0    |        typevar        |
//  *       +--------+--------+-------+------+
//  * DIM   |   1    |                |  dim |
//  *       +--------+--------+-------+------+
//  * PRI   |   2    |        |  pri enumset |
//  *       +--------+--------+-------+------+
//  * CON   |   3    |        |   n   |  con |
//  *       +--------+--------+-------+------+
//  * NEVER |               -2               |
//  *       +--------+--------+-------+------+
//  * UNSET |               -1               |
//  *       +--------------------------------+
//  *
//  */
// #[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
// #[repr(transparent)]
// struct Type(u32);
// 
// impl Type {
// 
//     const UNSET: Self = Self(!0);
//     const NEVER: Self = Self(!1);
// 
//     fn var(var: TypeVar) -> Self {
//         zerocopy::transmute!(var)
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
//     fn con(con: u8, n: u8) -> Self {
//         Self((3 << 29) | ((n as u32) << 8) | (con as u32))
//     }
// 
//     fn unpack(self) -> TypeRepr {
//         match self.0 >> 29 {
//             0 => TypeRepr::Var(zerocopy::transmute!(self.0)),
//             1 => TypeRepr::Dim(self.0 as _),
//             2 => TypeRepr::Pri(EnumSet::from_u16_truncated(self.0 as _)),
//             3 => TypeRepr::Con(self.0 as _, ((self.0 as u16) >> 8) as _),
//             _ if self == Self::NEVER => TypeRepr::Never,
//             _ => TypeRepr::Unset
//         }
//     }
// 
// }
// 
// #[derive(Clone, Copy, Debug)]
// enum TypeRepr {
//     Var(TypeVar),
//     // TODO: need Par(i) for generic type params
//     Dim(u8),
//     Pri(EnumSet<Primitive>),
//     Con(u8, u8),
//     Never,
//     Unset
// }
// 
// // use signed int here so that -1 can be used as a dummy (and checked via "<0")
// const PRI_IDX: Primitive = Primitive::I32;
// 
// // const PRI_INT: EnumSet<Primitive> = {
// //     use Primitive::*;
// //     enum_set!(I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64)
// // };
// 
// const PRI_NUM: EnumSet<Primitive> = {
//     use Primitive::*;
//     enum_set!(I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64 | F32 | F64)
// };
// 
// pub struct TypeInfer {
//     types: IndexVec<TypeVar, Type>,
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
//     if v == v as i8  as i64 { pri |= U8 | I8 };
//     if v == v as i16 as i64 { pri |= U16 | I16 };
//     if v == v as i32 as i64 { pri |= U32 | I32 };
//     if v == v as f32 as i64 { pri |= F32 };
//     if v == v as f64 as i64 { pri |= F64 };
//     pri
// }
// 
// fn newtypevar(types: &mut IndexVec<TypeVar, Type>) -> TypeVar {
//     types.push(Type::var(types.end()))
// }
// 
// fn newtypecon(types: &mut IndexVec<TypeVar, Type>, con: Constructor, par: &[Type]) -> TypeVar {
//     debug_assert!(par.iter().all(|p| !matches!(p.unpack(), TypeRepr::Con(..))));
//     let tv = types.push(Type::con(con as _, par.len() as _));
//     types.raw.extend_from_slice(par);
//     tv
// }
// 
// fn hashtype(ty: TypeRepr, args: &[u32]) -> u64 {
//     let mut hash = FxHasher::default();
//     match ty {
//         TypeRepr::Pri(p) => hash.write_u16(p.as_u16_truncated()),
//         TypeRepr::Dim(d) => hash.write_u8(d),
//         TypeRepr::Con(c, _) => {
//             hash.write_u8(c);
//             for a in args.iter().cloned() { hash.write_u32(a) }
//         },
//         TypeRepr::Var(_) | TypeRepr::Unset | TypeRepr::Never => unreachable!()
//     }
//     hash.finish()
// }
// 
// fn hashtypeobj(o: ObjectRef) -> u64 {
//     let mut hash = FxHasher::default();
//     match o {
//         ObjectRef::TPRI(&TPRI { ty, .. }) => hash.write_u16(1 << ty),
//         ObjectRef::TDIM(&TDIM { dim, .. }) => hash.write_u8(dim),
//         ObjectRef::TCON(&TCON { con, ref args, .. }) => {
//             hash.write_u8(con);
//             for a in args.iter().cloned() { hash.write_u32(zerocopy::transmute!(a)) }
//         },
//         _ => unreachable!()
//     }
//     hash.finish()
// }
// 
// fn sametype(a: ObjectRef, b: TypeRepr, par: &[u32]) -> bool {
//     match (a, b) {
//         (ObjectRef::TPRI(&TPRI { ty, .. }), TypeRepr::Pri(p)) => p.as_u16_truncated() == 1 << ty,
//         (ObjectRef::TDIM(&TDIM { dim, .. }), TypeRepr::Dim(d)) => dim == d,
//         (ObjectRef::TCON(&TCON { con, ref args, .. }), TypeRepr::Con(c, _))
//             => con == c
//             && args.len() == par.len()
//             && args.iter().cloned().zip(par.iter().cloned()).all(|(a,p)| p == zerocopy::transmute!(a)),
//         _ => false
//     }
// }
// 
// fn createtypeobj(objs: &mut Objects, ty: TypeRepr, args: &[u32]) -> ObjRef {
//     match ty {
//         TypeRepr::Pri(p) => objs.push(&TPRI::new(p.into_iter().next().unwrap() as _)).erase(),
//         TypeRepr::Dim(d) => objs.push(&TDIM::new(d)).erase(),
//         TypeRepr::Con(con, _) => {
//             // XXX replace with zerocopy::transmute when it can do that
//             let args: &[ObjRef] = unsafe {
//                 core::slice::from_raw_parts(args.as_ptr().cast(), args.len())
//             };
//             objs.push(&TCON::new(con, args)).erase()
//         },
//         TypeRepr::Var(_) | TypeRepr::Unset | TypeRepr::Never => unreachable!()
//     }
// }
// 
// fn createtype(objs: &Objects, types: &mut IndexVec<TypeVar, Type>, idx: ObjRef) -> Type {
//     match objs.get(idx) {
//         ObjectRef::NIL(_) => Type::UNSET,
//         ObjectRef::TPRI(&TPRI { ty, .. }) => Type::pri(EnumSet::from_u16_truncated(1 << ty)),
//         ObjectRef::TDIM(&TDIM { dim, .. }) => Type::dim(dim),
//         ObjectRef::TCON(&TCON { con, ref args, .. }) => {
//             let ty = types.push(Type::con(con, args.len() as _));
//             for _ in args { types.push(Type::UNSET); }
//             for (i, &arg) in args.iter().enumerate() {
//                 types[ty+i as isize] = createtype(objs, types, arg);
//             }
//             Type::var(ty)
//         },
//         _ => unreachable!()
//     }
// }
// 
// fn totypevar(types: &mut IndexVec<TypeVar, Type>, ty: Type) -> TypeVar {
//     match ty.unpack() {
//         TypeRepr::Var(tv) => tv,
//         _ => types.push(ty)
//     }
// }
// 
// fn typeobj(ccx: &mut Ccx<TypeInfer>, ty: TypeVar) -> ObjRef {
//     match ccx.data.types[ty].unpack() {
//         TypeRepr::Var(tv) => typeobj(ccx, tv),
//         type_ => {
//             let base = ccx.data.work.len();
//             if let TypeRepr::Con(_, n) = type_ {
//                 for i in 0..n as isize {
//                     let o = typeobj(ccx, ty+1+i);
//                     ccx.data.work.push(zerocopy::transmute!(o));
//                 }
//             }
//             let tx = &mut *ccx.data;
//             let args = &tx.work[base..];
//             let idx = match tx.typeobj.entry(
//                 hashtype(type_, args),
//                 |t| sametype(ccx.objs.get(*t), type_, args),
//                 |t| hashtypeobj(ccx.objs.get(*t))
//             ) {
//                 Entry::Vacant(e) => *e.insert(createtypeobj(&mut ccx.objs, type_, args)).get(),
//                 Entry::Occupied(e) => *e.get()
//             };
//             tx.work.truncate(base);
//             idx
//         }
//     }
// }
// 
// fn puttypeobj(ccx: &mut Ccx<TypeInfer>, idx: ObjRef) {
//     if let Entry::Vacant(e) = ccx.data.typeobj.entry(
//         hashtypeobj(ccx.objs.get(idx)),
//         |&i| ccx.objs.equal(i, idx),
//         |&i| hashtypeobj(ccx.objs.get(i))
//     ) {
//         e.insert(idx);
//     }
// }
// 
// fn init(ccx: &mut Ccx<TypeInfer>) {
//     let mut idx = ObjRef::NIL;
//     while let Some(i) = ccx.objs.next(idx) {
//         idx = i;
//         match ccx.objs[idx].op {
//             op if Operator::is_expr_raw(op) => {
//                 let ann = ccx.objs[idx.cast::<EXPR>()].ann;
//                 let ty = createtype(&ccx.objs, &mut ccx.data.types, ann);
//                 let ann = zerocopy::transmute!(totypevar(&mut ccx.data.types, ty));
//                 ccx.objs[idx.cast::<EXPR>()].ann = ann;
//             },
//             op if op == Operator::VAR as _ => {
//                 let ann = ccx.objs[idx.cast::<VAR>()].ann;
//                 let ty = createtype(&ccx.objs, &mut ccx.data.types, ann);
//                 let tv = totypevar(&mut ccx.data.types, ty);
//                 if ty == Type::UNSET { ccx.data.types[tv] = Type::var(tv); }
//                 let ann = zerocopy::transmute!(tv);
//                 ccx.objs[idx.cast::<VAR>()].ann = ann;
//             },
//             op if Operator::is_type_raw(op) => puttypeobj(ccx, idx),
//             _ => {}
//         }
//     }
// }
// 
// // set a = b
// fn unify(types: &mut IndexVec<TypeVar, Type>, a: TypeVar, b: Type) {
//     use TypeRepr::*;
//     let ta = types[a];
//     trace!(TYPE "unify {:?} {:?} = {:?}", a, ta.unpack(), b.unpack());
//     match (ta.unpack(), b.unpack()) {
//         (_, Var(j)) if j == a => { /* ok */ },
//         (Var(i), _) if a == i => types[a] = b,
//         (Var(mut i), _) => {
//             // shorten the var chain while we are here.
//             // this is not required for correctness, but makes it do less work.
//             while let Var(j) = types[i].unpack() {
//                 if i == j { break }
//                 i = j;
//                 trace!(TYPE "      (={:?})", i);
//             }
//             types[a] = Type::var(i);
//             unify(types, i, b);
//         },
//         (Pri(_), Pri(_)) => types[a].0 &= b.0,
//         (Pri(_), Var(j)) if matches!(types[j].unpack(), Pri(_)) => {
//             types[a] = b;
//             types[j].0 &= ta.0;
//         },
//         (Pri(_), Var(j)) => unify(types, j, Type::var(a)),
//         (Con(Constructor::TENSOR, _), tb) if matches!(tb, Pri(_))
//             || matches!(tb, Var(j) if matches!(types[j].unpack(), Pri(_))) =>
//         {
//             unify(types, a+1, b);
//             unify(types, a+2, Type::dim(0));
//         },
//         (Con(ca, na), Var(j)) => match types[j].unpack() {
//             Con(cb, nb) if (ca, na) == (cb, nb) => {
//                 for i in 1..=na as isize {
//                     unify(types, a+i, Type::var(j+i));
//                 }
//             },
//             Con(..) => unify(types, a, Type::NEVER),
//             _ => unify(types, j, Type::var(a)),
//         },
//         (_, Var(j)) => unify(types, j, ta),
//         (Dim(i), Dim(j)) if i == j => { /* ok */ },
//         _ => {
//             types[a] = Type::NEVER;
//             trace!(TYPE "***** {:?} = NEVER", a);
//         }
//     }
// }

// // set (ty, type(args)) = (ret(signature), args(signature))
// fn unifycall(ctx: &mut Ctx, args: &[ObjRef<EXPR>], mut signature: TypeVar, ty: Type) {
//     unify(&mut ctx.data.types, signature, ty);
//     for a in args.iter().cloned() {
//         signature += 1;
//         unifyexpr(ctx, a, Type::var(signature));
//     }
// }
// 
// fn instantiate(
//     scheme: &Scheme,
//     types: &mut IndexVec<TypeVar, Type>,
//     work: &mut Vec<u32>
// ) -> TypeVar {
//     let base = types.end();
//     for _ in 0..scheme.num_generics() {
//         newtypevar(types);
//     }
//     let bytecode = scheme.bytecode();
//     let mut ip = 0;
//     while let Some(&bc) = bytecode.get(ip) {
//         let data = bc & ((1 << Scheme::DATA_BITS)-1);
//         match bc>>Scheme::DATA_BITS {
//             Scheme::BC_PRI => {
//                 ip += 1;
//                 let mask = ((data as u16) << 8) | (bytecode[ip] as u16);
//                 let tv = zerocopy::transmute!(work.pop().unwrap());
//                 unify(types, tv, Type::pri(EnumSet::from_u16_truncated(mask)));
//             },
//             Scheme::BC_CON => {
//                 ip += 1;
//                 let n = bytecode[ip];
//                 let ty = types.push(Type::con(data, n));
//                 // NOTE: assumes Type::var and TypeVar can transmute
//                 types.raw.extend(work[work.len()-n as usize..].iter().cloned().map(Type));
//                 work.truncate(work.len()-n as usize);
//                 work.push(zerocopy::transmute!(ty));
//             },
//             _ /* BC_GEN */ => {
//                 work.push(zerocopy::transmute!(base + data as isize));
//             }
//         }
//         ip += 1;
//     }
//     debug_assert!(work.len() == 1);
//     zerocopy::transmute!(work.pop().unwrap())
// }
// 
// // set type(expr) = ty, where ty :: var|pri
// fn unifyexpr(ctx: &mut Ctx, idx: ObjRef<EXPR>, ty: Type) {
//     let objs = Access::borrow(&ctx.objs);
//     let tv: TypeVar = zerocopy::transmute!(objs[idx].ann);
//     if ctx.data.types[tv] != Type::UNSET {
//         unify(&mut ctx.data.types, tv, ty);
//         return;
//     }
//     trace!(TYPE "expr  {:?} = {:?}", tv, ty.unpack());
//     ctx.data.types[tv] = ty;
//     let ty = Type::var(tv);
//     match objs.get(idx.erase()) {
//         ObjectRef::KINT(&KINT { k, .. }) => unify(&mut ctx.data.types, tv,
//             Type::pri(kintpri(k as _))),
//         ObjectRef::KREF(_) => todo!(),
//         ObjectRef::DIM(_) => unify(&mut ctx.data.types, tv, Type::pri(PRI_IDX)),
//         ObjectRef::TUPLE(&TUPLE { ref fields, .. }) => {
//             let tup = ctx.data.types.push(Type::con(Constructor::Tuple as _, fields.len() as _));
//             for _ in fields { newtypevar(&mut ctx.data.types); }
//             unifycall(ctx, fields, tup, ty);
//         },
//         ObjectRef::VGET(&VGET { var, ref idx, .. }) => {
//             let vty = vidxtype(ctx, var, idx);
//             unify(&mut ctx.data.types, vty, ty);
//         },
//         ObjectRef::CAT(_) => todo!(),
//         ObjectRef::IDX(_) => todo!(),
//         ObjectRef::LOAD(_) => todo!(),
//         ObjectRef::FREF(_) => todo!(),
//         ObjectRef::CALL(_) => todo!(),
//         ObjectRef::CALLN(&CALLN { func, ref args, .. }) => {
//             let tx = &mut *ctx.data;
//             let sig = instantiate(Intrinsic::from_u8(func).scheme(), &mut tx.types, &mut tx.work);
//             unifycall(ctx, args, sig+1, ty);
//         },
//         ObjectRef::GET(_) | ObjectRef::CALLX(_) => { /* NOP */ },
//         _ => unreachable!()
//     }
// }
// 
// fn maketabtype(ctx: &mut Ctx, dims: u8) -> TypeVar {
//     let TypeInfer { types, work, .. } = &mut *ctx.data;
//     for _ in 0..dims {
//         let dim = types.push(Type::con(Constructor::Tensor as _, 2));
//         work.push(zerocopy::transmute!(dim));
//         types.push(Type::pri(PRI_IDX));
//         newtypevar(types);
//     }
//     let tv = types.push(Type::con(Constructor::Tuple as _, dims));
//     types.raw.extend(work.iter().map(|&t| Type::var(zerocopy::transmute!(t))));
//     work.clear();
//     tv
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
//                 unifyexpr(ctx, shape.cast(), Type::var(ty));
//             },
//             ObjectRef::MOD(&MOD { tab, guard, ref value, .. }) => {
//                 ctx.data.tab = tab;
//                 if !guard.is_nil() {
//                     unifyexpr(ctx, guard, Type::pri(Primitive::B1));
//                 }
//                 for &vset in value.iter() {
//                     let &VSET { var, value, ref idx, .. } = &objs[vset];
//                     let vty = vidxtype(ctx, var, idx);
//                     unifyexpr(ctx, value, Type::var(vty));
//                 }
//             },
//             ObjectRef::FUNC(_) => todo!(),
//             ObjectRef::QUERY(&QUERY { tab, ref value, .. }) => for &v in value {
//                 ctx.data.tab = tab;
//                 let ann: TypeVar = zerocopy::transmute!(objs[v].ann);
//                 debug_assert!(ctx.data.types[ann] == Type::UNSET);
//                 unifyexpr(ctx, v, Type::var(ann));
//             },
//             _ => {}
//         }
//     }
// }
// 
// // * eliminate unnecessary type variables
// // * empty pri => never
// // * multi pri => widest type
// // * unset => never
// // * tensor<t, 0> => t
// fn canonty(types: &mut IndexVec<TypeVar, Type>, tv: TypeVar) -> Type {
//     use TypeRepr::*;
//     let mut ty = types[tv];
//     ty = match ty.unpack() {
//         // fresh type variable, ie. the type is completely unbounded.
//         // treat this as equivalent to pri(all), which evaluates to f64.
//         // (in other words, if there's nothing bounding a type, we choose it to be scalar f64).
//         Var(i) if i == tv => Type::pri(Primitive::F64),
//         Var(i) => canonty(types, i),
//         Pri(p) if p.len() != 1 => match (p & PRI_NUM).as_u16_truncated() as i16 {
//             0   => Type::NEVER,
//             pri => Type::pri(EnumSet::from_u16_truncated((pri & -pri) as _))
//         },
//         Unset => Type::NEVER,
//         // args are already canonicalized because we go backwards
//         Con(Constructor::TENSOR, _) if types[tv+2] == Type::dim(0) => types[tv+1],
//         Con(_, _) => return Type::var(tv),
//         _ => return ty
//     };
//     types[tv] = ty;
//     ty
// }
// 
// fn canonicalize(types: &mut IndexVec<TypeVar, Type>) {
//     for tv in index::iter_span(types.end()).rev() {
//         canonty(types, tv);
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
//         let ann: TypeVar = zerocopy::transmute!(ccx.objs.get_raw(idx)[ofs]);
//         let ann = typeobj(ccx, ann);
//         ccx.objs.get_raw_mut(idx)[ofs] = zerocopy::transmute!(ann);
//     }
// }
// 
// impl Phase for TypeInfer {
// 
//     fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
//         Ok(TypeInfer {
//             types: Default::default(),
//             work: Default::default(),
//             typeobj: Default::default(),
//             tab: ObjRef::NIL.cast()
//         })
//     }
// 
//     fn run(ccx: &mut Ccx<Self>) -> compile::Result {
//         init(ccx);
//         ccx.freeze_graph(infertoplevel);
//         canonicalize(&mut ccx.data.types);
//         setannotations(ccx);
//         if trace!(TYPE) {
//             trace_objs(&ccx.constants, &ccx.intern, &ccx.objs, ObjRef::NIL);
//         }
//         Ok(())
//     }
// 
// }
