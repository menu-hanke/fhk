//! C language support.

use core::cmp::{max, Ordering};
use core::iter::{repeat_n, zip};

use cranelift_codegen::ir::{AbiParam, InstBuilder, Signature};
use enumset::EnumSetType;

use crate::bitmap::BitmapWord;
use crate::bump::{BumpPtr, BumpRef, BumpVec};
use crate::compile::{self, Ccx};
use crate::emit::{cast_values, collectargs, irt2cl, Ecx, InsValue, NATIVE_CALLCONV};
use crate::index::InvalidValue;
use crate::intern::IRef;
use crate::ir::{Func, Ins, InsId, LangOp, Type};
use crate::lang::{Lang, Language};
use crate::lex::Token;
use crate::lower::CLcx;
use crate::obj::{Obj, ObjRef, CALLX, EXPR, TPRI, TTEN};
use crate::parse::parse_expr;
use crate::parser::{check, consume, next, require, Pcx};
use crate::typing::{Primitive, IRT_IDX};

const LOP_CFUNC: u8 = 0;
const LOP_CCALL: u8 = 1;
const LOP_CRES:  u8 = 2;

#[derive(Default)]
pub struct C;

macro_rules! define_primitives {
    ($($name:ident $irt:ident $($cname:literal)*;)*) => {

        #[derive(EnumSetType)]
        #[repr(u8)]
        enum CPrimitive {
            $($name,)*
        }

        impl CPrimitive {

            fn from_name(name: &[u8]) -> Option<Self> {
                match name {
                    $($($cname => Some(CPrimitive::$name),)*)*
                    _ => None
                }
            }

            fn to_ir(self) -> Type {
                match self {
                    $(CPrimitive::$name => Type::$irt),*
                }
            }

        }

    };
}

// TODO: short/int/long aliases are arch/os specific.
define_primitives! {
    bool    B1  b"bool";
    int8_t  I8  b"int8_t" b"uint8_t" b"char";
    int16_t I16 b"int16_t" b"uint16_t" b"short";
    int32_t I32 b"int32_t" b"uint32_t" b"int";
    int64_t I64 b"int64_t" b"uint64_t" b"long" b"ssize_t";
    float   F32 b"float";
    double  F64 b"double";
    void    FX  b"void";
}

impl CPrimitive {

    fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

}

#[derive(Clone, Copy, PartialEq, Eq, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct CType(u8);

impl CType {

    const VOID: Self     = Self::new(CPrimitive::void, 0);
    const VOID_PTR: Self = Self::new(CPrimitive::void, 1);

    const fn new(pri: CPrimitive, indir: u8) -> Self {
        Self((indir<<4)|(pri as u8))
    }

    fn indir(self) -> u8 {
        self.0>>4
    }

    fn primitive(self) -> CPrimitive {
        CPrimitive::from_u8(self.0 & 0xf)
    }

    fn is_ptr(self) -> bool {
        self.indir() > 0
    }

    fn to_ir(self) -> Type {
        match self.is_ptr() {
            true  => Type::PTR,
            false => self.primitive().to_ir()
        }
    }

}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct CFunc {
    what: u8,
    ret: CType,
    _pad: [u8; 2],
    args: IRef<[CType]>,
}

impl CFunc {
    // values for `what`:
    const PTR: u8 = 0;  // indirect call, first arg is function pointer
    const SYM: u8 = 1;  // call symbol (SymCall)
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct CDynFunc {
    func: CFunc,
    lib: IRef<[u8]>,
    sym: IRef<[u8]>,
}

// value = scalar(input) | struct
// struct = field*
// field = value | output

const TAG_INPUT: u16 = 0;         // inputs[idx]
const TAG_OFFSET: u16 = 1;        // alloc+offset
const TAG_OUTPUT_TENSOR: u16 = 2; // outputptr[idx]
const TAG_OUTPUT_SCALAR: u16 = 3; // (field only)

// data[14] | tag[2]
#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(transparent)]
struct Value(u16);

impl Value {

    fn from_data_tag(data: u16, tag: u16) -> Self {
        Self((data<<2) | tag)
    }

    fn unpack(self) -> (u16, u16) {
        (self.0>>2, self.0&3)
    }

}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct Store {
    ofs: u16,
    value: Value
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct ScalarOutput {
    tag: u8,
    pri: u8, // CPrimitive
    ofs: u16,
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct TensorOutput {
    tag: u8,
    dim: u8,
    input: u16,
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct ReturnOutput {
    tag: u8,
    pri: u8,
    _pad: u16
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C, align(2))]
struct Output {
    tag: u8,
    _data: [u8; 3]
}

impl Output {
    const SCALAR: u8 = 0;
    const TENSOR: u8 = 1;
    const RETURN: u8 = 2;
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct Call {
    func: IRef<CFunc>,
    args: BumpRef<Value>,
    inputs: BumpRef<CType>,
    outputs: BumpRef<Output>,
    stores: BumpRef<Store>,
    narg: u16,
    nout: u16,
    nstore: u16,
    size: u16,
    align: u16,
    _pad: u16
}

/* ---- Parsing ------------------------------------------------------------- */

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct Field {
    ofs: u16,
    data: u16, // input idx | output idx | offset
    tag: u16,  // input | output_tensor | offset | output_scalar
}

enum CExpr {
    Input(u16, CType),        // value : ctype
    ScalarOutput(u16, CType), // out : ctype
    _TensorOutput(u16),        // out[...] : ctype (TODO)
    Ptr(u16),                 // :struct { ... } *
    Struct(AllocLayout)       // :struct { ... }      (details in ps.fields)
}

#[derive(Default)]
struct AllocLayout {
    size: u16,
    align: u8
}

struct ParseState {
    need: BitmapWord,
    n: u16,
    sig: BumpVec<CType>,
    args: BumpVec<Value>,
    inputs: BumpVec<ObjRef<EXPR>>,
    inputs_ctype: BumpVec<CType>,
    outputs: BumpRef<Output>,
    alloc: AllocLayout,
    stores: BumpVec<Store>,
    fields: BumpVec<Field>,
    sym: Option<(IRef<[u8]>, IRef<[u8]>)>,
    ret: CType
}

fn putfield(outer: &mut AllocLayout, inner: AllocLayout) -> u16 {
    outer.size = (outer.size + inner.align as u16 - 1) & !(inner.align as u16 - 1);
    outer.align = max(outer.align, inner.align);
    let ofs = outer.size;
    outer.size += inner.size;
    ofs
}

fn ctypelayout(ctype: CType) -> AllocLayout {
    let size = ctype.to_ir().size();
    AllocLayout { size: size as _, align: size as _ }
}

fn dumpstruct(pcx: &mut Pcx, ps: &mut ParseState, layout: AllocLayout, base: u32) -> u16 {
    let offset = putfield(&mut ps.alloc, layout);
    for i in base..ps.fields.len() {
        let Field { ofs, data, tag } = ps.fields.as_slice(&pcx.tmp)[i as usize];
        if tag == TAG_OUTPUT_SCALAR {
            let o: &mut ScalarOutput = zerocopy::transmute_mut!(
                &mut pcx.tmp[ps.outputs.add_size(data as _)]
            );
            debug_assert!(o.ofs == 0);
            o.ofs = offset + ofs;
        } else {
            ps.stores.push(&mut pcx.perm, Store {
                ofs: offset + ofs,
                value: Value::from_data_tag(data, tag)
            })
        }
    }
    ps.fields.truncate(base);
    offset
}

fn dumpfield(pcx: &mut Pcx, ps: &mut ParseState, layout: AllocLayout, field: Field) -> u16 {
    let base = ps.fields.len();
    ps.fields.push(&mut pcx.tmp, field);
    dumpstruct(pcx, ps, layout, base)
}

fn parse_indirection(pcx: &mut Pcx) -> compile::Result<u8> {
    let mut indir = 0;
    while check(pcx, Token::Asterisk)? {
        indir += 1;
    }
    Ok(indir)
}

fn parse_ctype(pcx: &mut Pcx) -> compile::Result<CType> {
    require(pcx, Token::Ident)?;
    let Some(pri) = CPrimitive::from_name(pcx.intern.get_slice(zerocopy::transmute!(pcx.data.tdata)))
        else { todo!() /* TODO: report error (invalid ctype) */ };
    next(pcx)?;
    let indir = parse_indirection(pcx)?;
    Ok(CType::new(pri, indir))
}

fn parse_out(pcx: &mut Pcx, ps: &mut ParseState) -> compile::Result<CExpr> {
    let idx = match pcx.data.token {
        Token::LParen => {
            next(pcx)?;
            require(pcx, Token::Int)?;
            let idx = pcx.data.tdata as _;
            if !ps.need.test(idx) {
                // TODO: report error (don't want this out parameter)
                todo!();
            }
            next(pcx)?;
            consume(pcx, Token::RParen)?;
            idx
        },
        _ => match ps.need.ffs() {
            Some(idx) => idx,
            None => {
                // TODO: report error (too many out expressions)
                todo!()
            }
        }
    };
    let dim = if check(pcx, Token::LBracket)? {
        todo!()
    } else {
        0
    };
    ps.need.clear(idx);
    consume(pcx, Token::Colon)?;
    let ctype = parse_ctype(pcx)?;
    Ok(match dim {
        0 => {
            let o: &mut ScalarOutput = zerocopy::transmute_mut!(
                &mut pcx.tmp[ps.outputs.add_size(idx as _)]);
            o.tag = Output::SCALAR;
            o.pri = ctype.primitive() as _;
            let indir = ctype.indir();
            if indir > 0 {
                let mut ofs = dumpfield(
                    pcx,
                    ps,
                    ctypelayout(CType::new(ctype.primitive(), 0)),
                    Field { ofs: 0, data: idx as _, tag: TAG_OUTPUT_SCALAR}
                );
                for _ in 1..indir {
                    ofs = dumpfield(
                        pcx,
                        ps,
                        ctypelayout(CType::VOID_PTR),
                        Field { ofs: 0, data: ofs, tag: TAG_OFFSET }
                    );
                }
                CExpr::Ptr(ofs)
            } else {
                CExpr::ScalarOutput(idx as _, ctype)
            }
        },
        _ => {
            todo!()
        }
    })
}

fn parse_in(pcx: &mut Pcx, ps: &mut ParseState) -> compile::Result<CExpr> {
    let value = parse_expr(pcx)?;
    let idx = ps.inputs.len();
    ps.inputs.push(&mut pcx.tmp, value);
    consume(pcx, Token::Colon)?;
    let ann = parse_ctype(pcx)?;
    ps.inputs_ctype.push(&mut pcx.tmp, ann);
    Ok(CExpr::Input(idx as _, ann))
}

fn parse_struct(pcx: &mut Pcx, ps: &mut ParseState) -> compile::Result<CExpr> {
    consume(pcx, Token::LCurly)?;
    let mut layout = AllocLayout::default();
    let start = ps.fields.len();
    let mut fieldbase = start;
    while pcx.data.token != Token::RCurly {
        match parse_cexpr(pcx, ps)? {
            CExpr::Input(idx, ctype) => {
                let ofs = putfield(&mut layout, ctypelayout(ctype));
                ps.fields.push(&mut pcx.tmp, Field { ofs, data: idx, tag: TAG_INPUT });
            },
            CExpr::ScalarOutput(idx, ctype) => {
                let ofs = putfield(&mut layout, ctypelayout(ctype));
                ps.fields.push(&mut pcx.tmp, Field { ofs, data: idx as _, tag: TAG_OUTPUT_SCALAR });
            },
            CExpr::_TensorOutput(idx) => {
                let ofs = putfield(&mut layout, ctypelayout(CType::VOID_PTR));
                ps.fields.push(&mut pcx.tmp, Field { ofs, data: idx as _, tag: TAG_OUTPUT_TENSOR });
            },
            CExpr::Ptr(offset) => {
                let ofs = putfield(&mut layout, ctypelayout(CType::VOID_PTR));
                ps.fields.push(&mut pcx.tmp, Field { ofs, data: offset, tag: TAG_OFFSET });
            },
            CExpr::Struct(mem) => {
                let ofs = putfield(&mut layout, mem);
                for f in &mut ps.fields.as_mut_slice(&mut pcx.tmp)[fieldbase as usize..] {
                    f.ofs += ofs;
                }
                fieldbase = ps.fields.len();
            }
        }
        if !check(pcx, Token::Comma)? { break }
    }
    consume(pcx, Token::RCurly)?;
    Ok(if check(pcx, Token::Asterisk)? {
        let offset = dumpstruct(pcx, ps, layout, start);
        if check(pcx, Token::Asterisk)? {
            // TODO: auto box it as many times as needed
            todo!()
        }
        CExpr::Ptr(offset)
    } else {
        layout.size = (layout.size + layout.align as u16 - 1) & !(layout.align as u16 - 1);
        CExpr::Struct(layout)
    })
}

fn parse_cexpr(pcx: &mut Pcx, ps: &mut ParseState) -> compile::Result<CExpr> {
    match pcx.data.token {
        Token::Colon => {
            next(pcx)?;
            require(pcx, Token::Ident)?;
            if pcx.intern.get_slice::<u8>(zerocopy::transmute!(pcx.data.tdata)) != b"struct" {
                // TODO: report error (expected `struct`)
                todo!()
            }
            next(pcx)?;
            parse_struct(pcx, ps)
        },
        Token::Out => {
            next(pcx)?;
            parse_out(pcx, ps)
        },
        _ => {
            parse_in(pcx, ps)
        }
    }
}

fn parse_call(pcx: &mut Pcx, ps: &mut ParseState) -> compile::Result {
    consume(pcx, Token::LBracket)?;
    ps.sym = match pcx.data.token {
        Token::Literal => {
            let s = zerocopy::transmute!(pcx.data.tdata);
            next(pcx)?;
            match check(pcx, Token::Colon)? {
                true => {
                    let sym = zerocopy::transmute!(pcx.data.tdata);
                    next(pcx)?;
                    Some((s, sym))
                },
                false => Some((IRef::EMPTY, s))
            }
        },
        _ => {
            let ptr = parse_expr(pcx)?;
            pcx.objs.annotate(ptr, ObjRef::PTR.erase());
            ps.inputs.push(&mut pcx.tmp, ptr);
            ps.inputs_ctype.push(&mut pcx.tmp, CType::VOID_PTR);
            None
        }
    };
    consume(pcx, Token::RBracket)?;
    consume(pcx, Token::LParen)?;
    while pcx.data.token != Token::RParen {
        match parse_cexpr(pcx, ps)? {
            CExpr::Input(idx, ctype) => {
                ps.args.push(&mut pcx.tmp, Value::from_data_tag(idx, TAG_INPUT));
                ps.sig.push(&mut pcx.tmp, ctype);
            },
            CExpr::ScalarOutput(..) => {
                // TODO: report error (out parameter is not a pointer)
                todo!()
            },
            CExpr::_TensorOutput(idx) => {
                ps.args.push(&mut pcx.tmp, Value::from_data_tag(idx, TAG_OUTPUT_TENSOR));
                ps.sig.push(&mut pcx.tmp, CType::VOID_PTR);
            },
            CExpr::Ptr(offset) => {
                ps.args.push(&mut pcx.tmp, Value::from_data_tag(offset, TAG_OFFSET));
                ps.sig.push(&mut pcx.tmp, CType::VOID_PTR);
            },
            CExpr::Struct(_) => {
                // TODO: pass struct by value
                todo!()
            }
        }
        if !check(pcx, Token::Comma)? { break }
    }
    consume(pcx, Token::RParen)?;
    if let Some(idx) = ps.need.ffs() {
        consume(pcx, Token::Colon)?;
        let ret = parse_ctype(pcx)?;
        ps.ret = ret;
        if ret.is_ptr() {
            // TODO: auto deref
            todo!()
        }
        let o: &mut ReturnOutput = zerocopy::transmute_mut!(
            &mut pcx.tmp[ps.outputs.add_size(idx as _)]);
        o.tag = Output::RETURN;
        o.pri = ret.primitive() as _;
        ps.need.clear(idx);
    }
    Ok(())
}

fn collect_call(pcx: &mut Pcx, ps: &ParseState) -> ObjRef<CALLX> {
    let func = {
        let args = pcx.intern.intern(ps.sig.as_slice(&pcx.tmp));
        let func = CFunc {
            what: match ps.sym { Some(_) => CFunc::SYM, _ => CFunc::PTR },
            ret: ps.ret,
            args,
            _pad: Default::default()
        };
        match ps.sym {
            None             => pcx.intern.intern(&func),
            Some((lib, sym)) => pcx.intern.intern(&CDynFunc { func, lib, sym }).cast(),
        }
    };
    let call = {
        let args = pcx.perm.write(ps.args.as_slice(&pcx.tmp));
        let stores = pcx.perm.write(ps.stores.as_slice(&pcx.tmp));
        let inputs = pcx.perm.write(ps.inputs_ctype.as_slice(&pcx.tmp));
        let outputs = pcx.perm.write(&pcx.tmp[ps.outputs..ps.outputs.add_size(ps.n as _)]);
        pcx.perm.write(&Call {
            func,
            args: args.cast(),
            inputs: inputs.cast(),
            outputs: outputs.cast(),
            stores: stores.cast(),
            narg: ps.args.len() as _,
            nout: ps.n,
            nstore: ps.stores.len() as _,
            size: ps.alloc.size,
            align: ps.alloc.align as _,
            _pad: 0
        })
    };
    // TODO: nonscalar out parameters need annotations
    pcx.objs.push_args(
        CALLX::new(Lang::C as _, ObjRef::NIL, zerocopy::transmute!(call)),
        ps.inputs.as_slice(&pcx.tmp)
    )
}

/* ---- Lowering ------------------------------------------------------------ */

struct LowerState {
    inputs: BumpRef<InsId>,
    outputs: BumpRef<InsId>,
    alloc: InsId,
}

fn lower_value(lower: &LowerState, tmp: &BumpPtr, func: &Func, value: Value) -> InsId {
    match value.unpack() {
        (idx, TAG_INPUT) => {
            tmp[lower.inputs.add_size(idx as _)]
        },
        (ofs, TAG_OFFSET) => {
            let ofs = func.code.push(Ins::KINT(Type::I64, ofs as _));
            func.code.push(Ins::ADDP(lower.alloc, ofs))
        },
        (idx, _ /* TAG_OUTPUT_TENSOR */) => {
            tmp[lower.outputs.add_size(idx as _)]
        }
    }
}

fn lower_call(
    lcx: &mut CLcx,
    ctr: InsId,
    obj: ObjRef<CALLX>,
    func: &Func,
    inputs: &[InsId]
) -> InsId {
    let callx = &lcx.objs[obj];
    let call: BumpRef<Call> = zerocopy::transmute!(callx.func);
    let call = &lcx.perm[call];
    let alloc = match call.size {
        0 => InsId::INVALID.into(),
        size => {
            let size = func.code.push(Ins::KINT(Type::I64, size as _));
            let align = func.code.push(Ins::KINT(Type::I64, call.align as _));
            func.code.push(Ins::ALLOC(size, align, ctr))
        }
    };
    let callins = func.code.push(Ins::NOP_FX);
    // auto box and convert inputs
    let inputs_conv = {
        let (iref, iptr) = lcx.tmp.reserve_dst::<[InsId]>(inputs.len());
        for ((&iexpr, &ctype), (&input, ip)) in zip(
            zip(&callx.inputs, &lcx.perm[call.inputs..call.inputs.add_size(inputs.len() as _)]),
            zip(inputs, iptr)
        ) {
            if ctype != CType::VOID_PTR {
                let mut indir = 0;
                let mut ann = lcx.objs[iexpr].ann;
                while lcx.objs[ann].op == Obj::TTEN {
                    indir += 1;
                    ann = lcx.objs[ann.cast::<TTEN>()].elem;
                }
                debug_assert!(lcx.objs[ann].op == Obj::TPRI);
                let havepri = Primitive::from_u8(lcx.objs[ann.cast::<TPRI>()].ty);
                let needpri = ctype.primitive();
                if havepri.to_ir() != needpri.to_ir() {
                    if indir > 0 {
                        // TODO: report error (invalid parameter type)
                        todo!()
                    }
                    // TODO: perform scalar conversion
                    todo!()
                }
                match ctype.indir().cmp(&indir) {
                    Ordering::Less => {
                        // TODO: report error (invalid parameter type)
                        todo!()
                    },
                    Ordering::Equal => { /* perfect */ },
                    Ordering::Greater => {
                        // TODO: auto box input
                        todo!()
                    }
                }
            }
            *ip = input;
        }
        iref
    };
    let outbase = func.code.extend(repeat_n(Ins::NOP_FX, call.nout as _));
    let outputs = {
        let (outputs, optr) = lcx.tmp.reserve_dst::<[InsId]>(call.nout as _);
        let mut cursor = outbase;
        for (o, op) in zip(&lcx.perm[call.outputs..call.outputs.add_size(call.nout as _)], optr) {
            match o.tag {
                Output::SCALAR => {
                    let o: &ScalarOutput = zerocopy::transmute_ref!(o);
                    let alloc = func.code.push(Ins::MOVF(Type::PTR, alloc, callins));
                    let ofs = func.code.push(Ins::KINT(Type::I64, o.ofs as _));
                    let ptr = func.code.push(Ins::ADDP(alloc, ofs));
                    func.code.set(cursor, Ins::LOAD(CPrimitive::from_u8(o.pri).to_ir(), ptr));
                    cursor += 1;
                },
                Output::TENSOR => {
                    let o: &TensorOutput = zerocopy::transmute_ref!(o);
                    let mut len = inputs[o.input as usize];
                    for i in 1..o.dim {
                        len = func.code.push(
                            Ins::MUL(IRT_IDX, len, inputs[o.input as usize + i as usize]));
                    }
                    // this can overalign and that's ok
                    let align = func.code.push(Ins::KINT(Type::I64, 8));
                    let alloc = func.code.push(Ins::ALLOC(len, align, ctr));
                    *op = alloc;
                    func.code.set(cursor, Ins::MOVF(Type::PTR, alloc, callins));
                    cursor += 1;
                    for i in 0..o.dim {
                        func.code.set(cursor,
                            Ins::MOV(IRT_IDX, inputs[o.input as usize + i as usize]));
                        cursor += 1;
                    }
                },
                _ /* RETURN */ => {
                    let o: &ReturnOutput = zerocopy::transmute_ref!(o);
                    func.code.set(
                        cursor,
                        Ins::LOV(
                            CPrimitive::from_u8(o.pri).to_ir(),
                            callins,
                            LangOp::new(Lang::C, LOP_CRES)
                        )
                    );
                    cursor += 1;
                }
            }
        }
        outputs
    };
    let lower = LowerState {
        inputs: inputs_conv.cast(),
        outputs: outputs.cast(),
        alloc
    };
    let mut args = func.code.push(Ins::NOP(Type::LSV));
    for store in &lcx.perm[call.stores..call.stores.add_size(call.nstore as _)] {
        let value = lower_value(&lower, &lcx.tmp, func, store.value);
        let ofs = func.code.push(Ins::KINT(Type::I64, store.ofs as _));
        let ptr = func.code.push(Ins::ADDP(alloc, ofs));
        let fx = func.code.push(Ins::STORE(ptr, value));
        args = func.code.push(Ins::MOVF(Type::FX, args, fx));
    }
    for &arg in lcx.perm[call.args..call.args.add_size(call.narg as _)].iter().rev() {
        let value = lower_value(&lower, &lcx.tmp, func, arg);
        args = func.code.push(Ins::CARG(args, value));
    }
    if lcx.intern[call.func].what == CFunc::PTR {
        args = func.code.push(Ins::CARG(args, inputs[0]));
    }
    let funcref = func.code.push(Ins::LOXX(Type::LSV,
            LangOp::new(Lang::C, LOP_CFUNC), zerocopy::transmute!(call.func)));
    func.code.set(callins, Ins::LOVV(Type::FX, args, funcref, LangOp::new(Lang::C, LOP_CCALL)));
    outbase
}

/* ---- Emitting ------------------------------------------------------------ */

fn emit_call(ecx: &mut Ecx, id: InsId) -> InsValue {
    let emit = &mut *ecx.data;
    let (mut args, cf) = emit.code[id].decode_VV();
    let func: &CFunc = &ecx.intern[zerocopy::transmute!(emit.code[cf].bc())];
    let ptr = match func.what {
        CFunc::PTR => {
            let (ap, ptr) = emit.code[args].decode_CARG();
            args = ap;
            ptr
        },
        _ /* SYM */ => {
            // TODO: load dynamic sym
            todo!()
        }
    };
    let mut sig = Signature::new(NATIVE_CALLCONV);
    sig.params.extend(
        ecx.intern.get_slice(func.args)
        .iter()
        .map(|ct| AbiParam::new(irt2cl(ct.to_ir())))
    );
    sig.returns.push(AbiParam::new(irt2cl(func.ret.to_ir())));
    let sig = emit.fb.ctx.func.import_signature(sig);
    let argv = ecx.tmp.align_for::<InsValue>();
    let argbase = argv.end();
    collectargs(emit, argv, args);
    InsValue::from_cl_inst(
        emit.fb.ins().call_indirect(sig, emit.values[ptr].value(), cast_values(&argv[argbase..]))
    )
}

fn emit_res(ecx: &mut Ecx, id: InsId) -> InsValue {
    let emit = &mut *ecx.data;
    let call = emit.code[id].decode_V();
    let inst = emit.values[call].cl_inst();
    InsValue::from_value(emit.fb.ctx.func.dfg.inst_results(inst)[0])
}

/* -------------------------------------------------------------------------- */

impl Language for C {

    fn parse(pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALLX>> {
        let base = pcx.tmp.end();
        let (outputs, _) = pcx.tmp.reserve_dst::<[Output]>(n);
        let mut ps = ParseState {
            need: Default::default(),
            n: n as _,
            sig: Default::default(),
            args: Default::default(),
            inputs: Default::default(),
            inputs_ctype: Default::default(),
            outputs: outputs.cast(),
            alloc: Default::default(),
            stores: Default::default(),
            fields: Default::default(),
            sym: Default::default(),
            ret: CType::VOID
        };
        ps.need.set_range(0..n);
        parse_call(pcx, &mut ps)?;
        if !ps.need.is_empty() {
            // TODO: report error (not enough out parameters)
            todo!()
        }
        let obj = collect_call(pcx, &ps);
        pcx.tmp.truncate(base);
        Ok(obj)
    }

    fn lower(
        lcx: &mut CLcx,
        ctr: InsId,
        obj: ObjRef<CALLX>,
        func: &Func,
        inputs: &[InsId]
    ) -> InsId {
        let base = lcx.tmp.end();
        let res = lower_call(lcx, ctr, obj, func, inputs);
        lcx.tmp.truncate(base);
        res
    }

    fn begin_emit(_: &mut Ccx) -> compile::Result<Self> {
        Ok(Default::default())
    }

    fn emit(ecx: &mut Ecx, id: InsId, lop: u8) -> compile::Result<InsValue> {
        Ok(match lop {
            LOP_CCALL => emit_call(ecx, id),
            LOP_CRES  => emit_res(ecx, id),
            _ => unreachable!()
        })
    }

}
