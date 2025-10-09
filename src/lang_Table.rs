//! Table support.

// TODO:
// * string keys/values
// * perfect hashing
// * vectorized lookups tab[vec] -> vec
// * inlining (inliner: add exec_cost(...) to language trait)
// * bounds checking
// * csv options for files (delimiter/header/...)
// * allow parsing header and referring to columns by name

// TODO:
// trait LangOpType (from_u8/to_u8/name)

use core::cmp::Ordering;
use core::iter::zip;
use core::mem::{offset_of, MaybeUninit};
use core::u32;

use cranelift_codegen::ir::{InstBuilder, MemFlags, Value};
use enumset::EnumSetType;

use crate::bitmap::BitmapWord;
use crate::bump::{self, BumpPtr, BumpRef, BumpVec};
use crate::compile::{self, Ccx};
use crate::emit::{irt2cl, signature, Ecx, InsValue, Signature, NATIVE_CALLCONV};
use crate::intern::Interned;
use crate::ir::{Conv, Func, Ins, InsId, LangOp, Opcode, Type};
use crate::lang::{Lang, Language};
use crate::lex::Token;
use crate::lower::{decomposition, reserve, CLcx};
use crate::mcode::{MCodeOffset, Reloc};
use crate::obj::{ObjRef, CALL};
use crate::parse::parse_expr;
use crate::parser::{check, consume, next, Pcx};
use crate::runtime::IRT_IDX;

// (LOXX) lsv TREF ...
// (LOVV) idx TROW (TREF) (CARG idxlist)
// (LOVV) fx  TVAL (TREF) (ptr[query,result])
// (LOVX) lsv TCOL (TREF) (col)
// (LOVV) ty  TGET (TCOL) (row)

const LOP_TREF: u8 = 0;
const LOP_TROW: u8 = 1;
const LOP_TVAL: u8 = 2;
const LOP_TCOL: u8 = 3;
const LOP_TGET: u8 = 4;

const SPARSE_THREHOLD: f64 = 0.5;
const SPARSE_MINSIZE: usize = 32;

pub struct Table;

#[derive(EnumSetType)]
#[repr(u8)]
enum InputOperator {
    Eq,   // pick row with equal value
    Le,   // pick the largest row less than or equal to the value
    Ge,   // pick the smallest row greater than or equal to the value
    Int,  // linear interpolation between smaller and larger row
}

#[derive(EnumSetType)]
#[repr(u8)]
enum IndexType {
    Dense,
    TreeRows,
    TreeValues,
    Hash
}

#[derive(Clone, Copy, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct Column {
    op: u8, // InputOperator or output
    idx: u8
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct DenseInput {
    bias: i64,
    span: usize,
    // TODO: stride
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct DenseOutput {
    data: MCodeOffset,
    ty: u8,  // ir::Type
    sign: u8,
    _pad: [u8; 2]
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct DenseData {
    inputs: BumpRef<DenseInput>,
    outputs: BumpRef<DenseOutput>
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct TreeRowsData {
    rtq: MCodeOffset,
    outputs: BumpRef<DenseOutput>
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct TreeValuesData {
    rtq: MCodeOffset
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct TabDef {
    data: BumpRef<()>,    // DenseData|TreeRowsData|TreeValuesData|HashData
    rows: BumpRef<f64>,   // nrow * (ncol * f64)
    file: Interned<[u8]>, // empty for inline tables, non-empty for file tables
    nrow: u32,
    ncol: u8,
    index: u8,            // IndexType
    _pad: [u8; 2]
} // [Column; ncol] follows

impl TabDef {
    const INDEX_PENDING: u8 = 0x80;
    const INDEX_NONE: u8 = 0x7f;
}

impl DenseInput {
    const SKIP: i64 = i64::MIN;
}

impl InputOperator {

    fn is_input_u8(op: u8) -> bool {
        // FIXME replace with core::mem::variant_count when it stabilizes
        op < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _
    }

}

impl IndexType {

    fn from_u8(ty: u8) -> Option<Self> {
        // FIXME replace with core::mem::variant_count when it stabilizes
        if ty < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _ {
            Some(unsafe { core::mem::transmute(ty) })
        } else {
            None
        }
    }

}

/* ---- Parsing ------------------------------------------------------------- */

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct ColumnDef {
    data: u32, // input->ObjRef<EXPR>, output->index
    op: u32, // input->InputOperator, output->!0
}

// n.b. this assumes `next(pcx)` does not write anything in `pcx.perm`
fn parse_row(pcx: &mut Pcx) -> compile::Result {
    loop {
        match pcx.data.token {
            Token::Int => {
                pcx.perm.push(pcx.data.tdata as i32 as f64);
                next(pcx)?;
            },
            Token::Fp64 => {
                let data: Interned<f64> = zerocopy::transmute!(pcx.data.tdata);
                pcx.perm.push(pcx.intern[data]);
                next(pcx)?;
            },
            Token::Int64 => {
                let data: Interned<i64> = zerocopy::transmute!(pcx.data.tdata);
                let value = pcx.intern[data];
                if (value as f64 as i64) == value {
                    pcx.perm.push(value);
                } else {
                    // TODO: either error or some sensible fallback
                    todo!()
                }
                next(pcx)?;
            },
            _ => return Ok(())
        }
        if !check(pcx, Token::Comma)? {
            return Ok(())
        }
    }
}

fn parse_inlinedef(pcx: &mut Pcx) -> compile::Result<(usize, usize, BumpRef<f64>)> {
    let data = pcx.perm.align_for::<f64>().end();
    let mut ncol: Option<usize> = None;
    let mut nrow = 0;
    while (Token::Int|Token::Fp64|Token::Int64).contains(pcx.data.token) {
        let start = pcx.perm.end().cast::<f64>();
        parse_row(pcx)?;
        let nn = pcx.perm.end().cast::<f64>().index() - start.index();
        match ncol {
            Some(n) => {
                if n != nn as _ {
                    // TODO: report error
                    todo!()
                }
            },
            None => ncol = Some(nn)
        }
        nrow += 1;
    }
    let ncol = ncol.unwrap_or(0);
    Ok((nrow, ncol, data))
}

fn parse_tabdef(pcx: &mut Pcx) -> compile::Result<TabDef> {
    consume(pcx, Token::LBracket)?;
    let def = match pcx.data.token {
        Token::Literal => {
            // TODO: also support common csv options e.g. delimiter,header,...
            let file: Interned<[u8]> = zerocopy::transmute!(pcx.data.tdata);
            next(pcx)?;
            TabDef {
                data: BumpRef::zero(),
                rows: BumpRef::zero(),
                file,
                nrow: 0,
                ncol: 0,
                index: TabDef::INDEX_NONE,
                _pad: Default::default()
            }
        },
        _ => {
            let (nrow, ncol, rows) = parse_inlinedef(pcx)?;
            TabDef {
                data: BumpRef::zero(),
                rows,
                file: Interned::EMPTY,
                nrow: nrow as _,
                ncol: ncol as _,
                index: TabDef::INDEX_NONE,
                _pad: Default::default()
            }
        }
    };
    consume(pcx, Token::RBracket)?;
    Ok(def)
}

// pushes ColumnDefs on pcx.tmp
// returns index type if a tree index is required
fn parse_columns(pcx: &mut Pcx, nout: usize) -> compile::Result<Option<IndexType>> {
    let mut need = BitmapWord::default();
    need.set_range(0..nout);
    consume(pcx, Token::LParen)?;
    let mut index = None;
    while pcx.data.token != Token::RParen {
        match pcx.data.token {
            Token::Out => {
                next(pcx)?;
                let idx = if check(pcx, Token::LParen)? {
                    let idx = consume(pcx, Token::Int)? as usize;
                    if !need.test(idx) {
                        // TODO: report error (don't want this out parameter)
                        todo!()
                    }
                    consume(pcx, Token::RParen)?;
                    idx
                } else {
                    match need.ffs() {
                        Some(idx) => idx,
                        None => {
                            // TODO: report error (did not expect an out parameter)
                            todo!()
                        }
                    }
                };
                pcx.tmp.push(ColumnDef { data: idx as _, op: !0 });
                need.clear(idx);
            },
            _ => {
                let value = parse_expr(pcx)?;
                let op = if check(pcx, Token::Colon)? {
                    let ident: Interned<[u8]> = zerocopy::transmute!(consume(pcx, Token::Ident)?);
                    let op = match &pcx.intern[ident] {
                        b"atmost"      => InputOperator::Le,
                        b"atleast"     => InputOperator::Ge,
                        b"interpolate" => InputOperator::Int,
                        _ => { todo!() /* TODO: compile error: unknown operator */ }
                    };
                    index = Some(match (op, index) {
                        (InputOperator::Int, _) | (_, Some(IndexType::TreeValues))
                            => IndexType::TreeValues,
                        _ => IndexType::TreeRows
                    });
                    op
                } else {
                    InputOperator::Eq
                };
                pcx.tmp.push(ColumnDef {
                    data: zerocopy::transmute!(value),
                    op: op as _
                });
            }
        }
        if !check(pcx, Token::Comma)? { break }
    }
    if !need.is_empty() {
        // TODO: report error (not enough out parameters)
        todo!()
    }
    consume(pcx, Token::RParen)?;
    Ok(index)
}

fn collect(pcx: &mut Pcx, cols: BumpRef<[ColumnDef]>, ncol: usize, tab: TabDef) -> ObjRef<CALL> {
    let tref = pcx.perm.push(tab);
    // organize columns:
    // * inputs go in pcx.tmp[base..]
    // * column info goes in pcx.perm
    let base = pcx.tmp.end();
    let mut inputidx = 0;
    for i in 0..ncol {
        let ColumnDef { data, op } = pcx.tmp[cols.elem(i)];
        let idx = match op {
            u32::MAX => {
                // output
                data
            },
            _ => {
                // input
                pcx.tmp.push(data);
                inputidx += 1;
                inputidx-1
            }
        };
        pcx.perm.push(Column { idx: idx as _, op: op as _ });
    }
    // don't need to truncate tmp here, parse_call will truncate
    pcx.objs.push_args(CALL::new(Lang::Table as _, ObjRef::NIL, zerocopy::transmute!(tref)),
        &pcx.tmp[base.cast_up()..])
}

fn parse_call(pcx: &mut Pcx, nout: usize) -> compile::Result<ObjRef<CALL>> {
    let mut def = parse_tabdef(pcx)?;
    let base = pcx.tmp.end();
    if let Some(index) = parse_columns(pcx, nout)? {
        def.index = TabDef::INDEX_PENDING | (index as u8);
    }
    let ncol = pcx.tmp.end().cast::<ColumnDef>().index() - base.cast::<ColumnDef>().index();
    if def.file.is_empty() {
        if def.ncol != ncol as _ {
            return pcx.error(format_args!("expected {} columns, found {}", def.ncol, ncol));
        }
    } else {
        def.ncol = ncol as _;
    }
    let call = collect(pcx, base.cast_up(), ncol, def);
    pcx.tmp.truncate(base);
    Ok(call)
}

/* ---- Lowering ------------------------------------------------------------ */

fn tabcols(bump: &BumpPtr, tab: BumpRef<TabDef>) -> &[Column] {
    let ncol = bump[tab].ncol as usize;
    let base: BumpRef<Column> = tab.add(1).cast();
    &bump[base..base.add(ncol)]
}

fn lower_call(
    lcx: &mut CLcx,
    ctr: InsId,
    obj: ObjRef<CALL>,
    func: &Func,
    inputs: &[InsId]
) -> InsId {
    let base = lcx.tmp.end();
    let tab: BumpRef<TabDef> = zerocopy::transmute!(lcx.objs[obj].func);
    let tref = func.code.push(
        Ins::LOXX(Type::LSV, LangOp::Table(LOP_TREF), zerocopy::transmute!(tab)));
    let deco = decomposition(&lcx.objs, obj.erase(), &mut lcx.tmp);
    let out = reserve(func, deco.len());
    let cols = tabcols(&lcx.perm, tab);
    let index = lcx.perm[tab].index;
    let trow = if (index & TabDef::INDEX_PENDING) != 0 {
        let isvalue = index == TabDef::INDEX_PENDING | (IndexType::TreeValues as u8);
        let nbox = inputs.len() + match isvalue { true => deco.len(), false => 0 };
        let abox = func.code.push(
            Ins::ABOX(ctr, (Type::F64.size() * nbox) as _, Type::F64.size() as _));
        let ptr = func.code.push(Ins::BREF(abox));
        let mut fx = func.code.push(Ins::NOP(Type::FX));
        for (i,&input) in inputs.iter().enumerate() {
            let ofs = func.code.push(Ins::KINT(Type::I64, i as u32 * Type::F64.size() as u32));
            let ptr = func.code.push(Ins::ADDP(ptr, ofs));
            let input = func.code.push(Ins::CONV(Type::F64, input, Conv::SIGNED));
            let store = func.code.push(Ins::STORE(ptr, input));
            fx = func.code.push(Ins::MOVF(Type::FX, fx, store));
        }
        let args = func.code.push(Ins::MOVF(Type::PTR, ptr, fx));
        if isvalue {
            let tval = func.code.push(Ins::LOVV(Type::FX, tref, args, LangOp::Table(LOP_TVAL)));
            let ptr = func.code.push(Ins::MOVF(Type::PTR, ptr, tval));
            for &col in cols {
                if !InputOperator::is_input_u8(col.op) {
                    let ofs = func.code.push(Ins::KINT(Type::I64,
                            (col.idx as u32 + inputs.len() as u32) * Type::F64.size() as u32));
                    let ptr = func.code.push(Ins::ADDP(ptr, ofs));
                    let mut value = Ins::LOAD(Type::F64, ptr);
                    if deco[col.idx as usize] != Type::F64 {
                        let load = func.code.push(value);
                        value = Ins::CONV(deco[col.idx as usize], load, Conv::SIGNED);
                    }
                    func.code.set(out + col.idx as isize, value);
                }
            }
            None
        } else {
            Some(func.code.push(Ins::LOVV(IRT_IDX, tref, args, LangOp::Table(LOP_TROW))))
        }
    } else {
        let mut args = func.code.push(Ins::NOP(Type::LSV));
        for &input in inputs.iter().rev() {
            args = func.code.push(Ins::CARG(args, input));
        }
        Some(func.code.push(Ins::LOVV(IRT_IDX, tref, args, LangOp::Table(LOP_TROW))))
    };
    if let Some(trow) = trow {
        // TODO: this assumes each output is a primitive. vectorized lookups have to emit a loop.
        for &col in cols {
            if !InputOperator::is_input_u8(col.op) {
                let tcol = func.code.push(
                    Ins::LOVX(Type::LSV, tref, col.idx as _, LangOp::Table(LOP_TCOL)));
                func.code.set(out + col.idx as isize,
                    Ins::LOVV(deco[col.idx as usize], tcol, trow, LangOp::Table(LOP_TGET)));
            }
        }
    }
    lcx.tmp.truncate(base);
    out
}

/* ---- Runtime ------------------------------------------------------------- */

struct RtTreeQueryR {
    key: *const f64,
    link: *const u32,
    op: *const InputOperator,
    n_in: usize,
    leaf_bias: usize
}

struct RtTreeQueryV {
    key: *const f64,
    link: *const u32,
    op: *const InputOperator,
    data: *const f64,
    n_in: usize,
    n_out: usize,
    leaf_bias: usize
}

unsafe impl bump::IntoBytes for RtTreeQueryR {}
unsafe impl bump::Immutable for RtTreeQueryR {}
unsafe impl bump::IntoBytes for RtTreeQueryV {}
unsafe impl bump::Immutable for RtTreeQueryV {}

fn cmpfp(a: f64, b: f64) -> Ordering {
    if a < b {
        Ordering::Less
    } else if a > b {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

fn binsearchkey(keys: &[f64], query: f64) -> Result<usize, usize> {
    keys.binary_search_by(|&x| cmpfp(x, query))
}

const TREELOOKUPR_SIGNATURE: &Signature = &signature!(NATIVE_CALLCONV, PTR PTR -> I32);
unsafe extern "C" fn rt_treelookupr(rtq: &RtTreeQueryR, query: *const f64) -> u32 {
    let mut idx = 0;
    for i in 0..rtq.n_in {
        let start = (unsafe { *rtq.link.add(idx) }) as usize;
        let end = (unsafe { *rtq.link.add(idx+1) }) as usize;
        let keys = unsafe { core::slice::from_raw_parts(rtq.key.add(start), end-start) };
        let q = unsafe { *query.add(i) };
        let o = unsafe { *rtq.op.add(i) };
        idx = start + match binsearchkey(keys, q) {
            Ok(j) => j,
            Err(j) => match o {
                InputOperator::Eq | InputOperator::Le => ((j as isize)-1).max(0) as usize,
                InputOperator::Ge => j.min(keys.len() - 1),
                InputOperator::Int => unreachable!()
            }
        };
    }
    (idx - rtq.leaf_bias) as _
}

const TREELOOKUPV_MAXOUT: usize = 8;
unsafe fn rt_treelookupvx(
    rtq: &RtTreeQueryV,
    query: *const f64,
    out: *mut f64,
    input: usize,
    node: usize
) {
    if input == rtq.n_in {
        for i in 0..rtq.n_out {
            unsafe {
                *out.add(i) = *rtq.data.add((node-rtq.leaf_bias)*rtq.n_out+i);
            }
        }
    } else {
        let start = (unsafe { *rtq.link.add(node) }) as usize;
        let end = (unsafe { *rtq.link.add(node+1) }) as usize;
        let keys = unsafe { core::slice::from_raw_parts(rtq.key.add(start), end-start) };
        let q = unsafe { *query.add(input) };
        let o = unsafe { *rtq.op.add(input) };
        let next = start + match binsearchkey(keys, q) {
            Ok(j) => j,
            Err(j) => match o {
                InputOperator::Int if j > 0 && j < keys.len() => {
                    let mut t: [MaybeUninit<f64>; 2*TREELOOKUPV_MAXOUT] = [
                        const { MaybeUninit::uninit() };
                        2*TREELOOKUPV_MAXOUT
                    ];
                    let tptr = t.as_mut_ptr() as *mut f64;
                    unsafe {
                        rt_treelookupvx(rtq, query, tptr, input+1, start+j-1);
                        rt_treelookupvx(rtq, query, tptr.add(TREELOOKUPV_MAXOUT),input+1,start+j);
                    }
                    let s = (q - keys[j-1]) / (keys[j] - keys[j-1]);
                    for i in 0..rtq.n_out {
                        let a = unsafe { *tptr.add(i) };
                        let b = unsafe { *tptr.add(TREELOOKUPV_MAXOUT+i) };
                        let v = a + (b-a)*s;
                        unsafe { *out.add(i) = v };
                    }
                    return
                },
                InputOperator::Eq | InputOperator::Le => ((j as isize)-1).max(0) as usize,
                InputOperator::Ge | InputOperator::Int => j.min(keys.len() - 1),
            }
        };
        unsafe { rt_treelookupvx(rtq, query, out, input+1, next); }
    }
}

const TREELOOKUPV_SIGNATURE: &Signature = &signature!(NATIVE_CALLCONV, PTR PTR);
unsafe extern "C" fn rt_treelookupv(rtq: &RtTreeQueryV, arg: *mut f64) {
    unsafe { rt_treelookupvx(rtq, arg as _, arg.add(rtq.n_in) as _, 0, 0); }
}

/* ---- Emitting ------------------------------------------------------------ */

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct ColumnInfo {
    min: f64,
    max: f64,
    ty: u8,
    sign: u8,
    _pad: [u8; 6]
}

fn isrepresentable(x: f64, ty: Type) -> bool {
    use Type::*;
    match ty {
        I8  => x as i8 as f64 == x,
        I16 => x as i16 as f64 == x,
        I32 => x as i32 as f64 == x,
        I64 => x as i64 as f64 == x,
        F32 => x as f32 as f64 == x,
        F64 => true,
        _ => false
    }
}

fn rangedatatype(min: f64, max: f64) -> (Type, /*signed:*/bool) {
    for ty in [Type::I8, Type::I16, Type::I32] {
        if isrepresentable(min, ty) && isrepresentable(max, ty) && isrepresentable(max-min, ty) {
            return (ty, min<0.0);
        }
    }
    (Type::F64, true)
}

fn analyzecolumn(data: &[f64], ncol: usize, col: usize) -> ColumnInfo {
    let mut min = f64::INFINITY;
    let mut max = -f64::INFINITY;
    let mut integer = true;
    for &x in data.iter().skip(col).step_by(ncol) {
        min = min.min(x);
        max = max.max(x);
        integer &= x as i64 as f64 == x;
    }
    let (ty, signed) = if integer {
        rangedatatype(min, max)
    } else {
        (Type::F64, true)
    };
    ColumnInfo {
        min,
        max,
        ty: ty as _,
        sign: signed as _,
        _pad: Default::default()
    }
}

// pushes column info on ecx.tmp
fn analyzetable(ecx: &mut Ecx, tab: BumpRef<TabDef>) -> IndexType {
    let TabDef { rows, nrow, index, .. } = ecx.perm[tab];
    let nrow = nrow as usize;
    let columns = tabcols(&ecx.perm, tab);
    let tdata = &ecx.perm[rows..rows.add(nrow*columns.len())];
    let (_, colinfo_data) = ecx.tmp.reserve_dst::<[ColumnInfo]>(columns.len());
    let mut integer = true;
    let mut dense_size = 1;
    let mut ninputcol = 0;
    for (i, &col) in columns.iter().enumerate() {
        let info = analyzecolumn(tdata, columns.len(), i);
        if InputOperator::is_input_u8(col.op) {
            dense_size *= 1 + (info.max - info.min) as usize;
            integer &= Type::from_u8(info.ty).is_int();
            ninputcol += 1;
        }
        colinfo_data[i] = info;
    }
    if let Some(index) = IndexType::from_u8(index ^ TabDef::INDEX_PENDING) {
        index
    } else if !integer || (dense_size >= SPARSE_MINSIZE
            && (dense_size as f64 / (nrow*ninputcol) as f64) < SPARSE_THREHOLD)
    {
        IndexType::Hash
    } else {
        IndexType::Dense
    }
}

fn writepacked(dst: &mut [u8], info: &ColumnInfo, value: f64) {
    match (Type::from_u8(info.ty), info.sign != 0) {
        (Type::I8, true)   => dst[0] = value as i8 as u8,
        (Type::I8, false)  => dst[0] = value as u8,
        (Type::I16, true)  => dst.copy_from_slice(&(value as i16).to_ne_bytes()),
        (Type::I16, false) => dst.copy_from_slice(&(value as u16).to_ne_bytes()),
        (Type::I32, true)  => dst.copy_from_slice(&(value as i32).to_ne_bytes()),
        (Type::I32, false) => dst.copy_from_slice(&(value as u32).to_ne_bytes()),
        _ => dst.copy_from_slice(&value.to_ne_bytes()),
    }
}

fn makedensetab(ecx: &mut Ecx, tab: BumpRef<TabDef>, info: BumpRef<ColumnInfo>) -> DenseData {
    let TabDef { rows, nrow, ncol, .. } = ecx.perm[tab];
    let (nrow, ncol) = (nrow as usize, ncol as usize);
    let cols: BumpRef<Column> = tab.add(1).cast();
    let (mut nin, mut nout) = (0, 0);
    let mut dense_size = 1;
    let info = &ecx.tmp[info..info.add(ncol)];
    for (&col, info) in zip(&ecx.perm[cols..cols.add(ncol)], info) {
        if InputOperator::is_input_u8(col.op) {
            nin += 1;
            dense_size *= 1 + (info.max - info.min) as usize;
        } else {
            nout += 1;
        }
    }
    let (inputs, _) = ecx.perm.reserve_dst::<[DenseInput]>(nin);
    let (outputs, _) = ecx.perm.reserve_dst::<[DenseOutput]>(nout);
    for (i, (col, cinfo)) in
        zip(bump::iter_range(cols..cols.add(ncol)), info).enumerate()
    {
        let col = ecx.perm[col];
        if InputOperator::is_input_u8(col.op) {
            let bias = if cinfo.min == cinfo.max {
                DenseInput::SKIP
            } else {
                debug_assert!(isrepresentable(cinfo.min, Type::I64));
                cinfo.min as _
            };
            let input = &mut ecx.perm[inputs.elem(col.idx as usize)];
            input.bias = bias;
            input.span = 1 + (cinfo.max - cinfo.min) as usize;
        } else {
            let size = Type::from_u8(cinfo.ty).size();
            ecx.image.mcode.align_data(size);
            let (mcode_output, data) = ecx.image.mcode.reserve_data::<u8>(size * dense_size);
            let columns = &ecx.perm[cols..cols.add(ncol)];
            for r in 0..nrow {
                let row = &ecx.perm[rows.add(r*ncol)..rows.add((r+1)*ncol)];
                let mut pos = 0;
                let mut colsize = 0;
                for (j,(cc,cci)) in zip(columns, info).enumerate() {
                    if InputOperator::is_input_u8(cc.op) && cci.min != cci.max {
                        pos *= colsize;
                        pos += (row[j] - cci.min) as usize;
                        colsize = 1 + (cci.max - cci.min) as usize;
                    }
                }
                writepacked(&mut data[pos*size..(pos+1)*size], cinfo, row[i]);
            }
            let out = &mut ecx.perm[outputs.elem(col.idx as usize)];
            out.data = mcode_output;
            out.ty = cinfo.ty;
            out.sign = cinfo.sign;
        }
    }
    DenseData {
        inputs: inputs.base(),
        outputs: outputs.base()
    }
}

fn sortrows(ecx: &mut Ecx, tab: BumpRef<TabDef>) {
    let TabDef { rows, nrow, ncol, .. } = ecx.perm[tab];
    let (nrow, ncol) = (nrow as usize, ncol as usize);
    let columns = tabcols(&ecx.perm, tab);
    let base = ecx.tmp.end();
    let indices = ecx.tmp.extend(0..nrow);
    ecx.tmp[indices..]
        .sort_unstable_by(|&i,&j|
            columns.iter()
            .enumerate()
            .find_map(|(k,&c)| if InputOperator::is_input_u8(c.op) {
                let a = ecx.perm[rows.add(i*ncol+k)];
                let b = ecx.perm[rows.add(j*ncol+k)];
                if a != b {
                    Some(cmpfp(a, b))
                } else {
                    None
                }
            } else {
                None
            })
            .unwrap_or(Ordering::Equal)
        );
    let data = ecx.tmp.write(&ecx.perm[rows..rows.add(nrow*ncol)]);
    for (j,&i) in ecx.tmp[indices..indices.add(nrow)].iter().enumerate() {
        ecx.perm[rows.add(ncol*j)..rows.add(ncol*(j+1))]
            .copy_from_slice(&ecx.tmp[data.elem(ncol*i)..data.elem(ncol*(i+1))]);
    }
    ecx.tmp.truncate(base);
}

fn buildtree(ecx: &mut Ecx, tab: BumpRef<TabDef>, info: BumpRef<ColumnInfo>) -> BumpRef<()> {
    let TabDef { rows, nrow, ncol, index, .. } = ecx.perm[tab];
    let (nrow, ncol) = (nrow as usize, ncol as usize);
    let columns = tabcols(&ecx.perm, tab);
    let mut key: BumpVec<f64> = Default::default();       // node -> key
    let mut link: BumpVec<u32> = Default::default();      // node -> start of child nodes
    let mut work_link: BumpVec<u32> = Default::default(); // node -> end of rows
    key.push(&mut ecx.tmp, f64::NAN);
    work_link.push(&mut ecx.tmp, nrow as _);
    let mut work_start = 0;
    let mut nin = 0;
    let mut nout = 0;
    let mcode_op = ecx.image.mcode.align_data_for::<InputOperator>();
    for (i,&col) in columns.iter().enumerate() {
        if InputOperator::is_input_u8(col.op) {
            nin += 1;
            ecx.image.mcode.write_data(&col.op);
            let work_end = work_link.len();
            let mut r = 0;
            for j in work_start..work_end {
                link.push(&mut ecx.tmp, key.len());
                let e = work_link.as_slice(&ecx.tmp)[j as usize] as usize;
                while r < e {
                    let k = ecx.perm[rows.add(ncol*r+i)];
                    key.push(&mut ecx.tmp, k);
                    loop {
                        r += 1;
                        if r >= e || ecx.perm[rows.add(ncol*r+i)] != k { break }
                    }
                    work_link.push(&mut ecx.tmp, r as _);
                }
            }
            work_start = work_end;
        } else {
            nout += 1;
        }
    }
    debug_assert!(nin > 0);
    debug_assert!(nout > 0);
    let leaf_bias = link.len() as usize;
    let nleaf = key.len() as usize - leaf_bias;
    link.push(&mut ecx.tmp, key.len());
    let work_link = work_link.as_slice(&ecx.tmp);
    let mcode_key = ecx.image.mcode.write_data(key.as_slice(&ecx.tmp));
    let mcode_link = ecx.image.mcode.write_data(link.as_slice(&ecx.tmp));
    if index == IndexType::TreeValues as _ {
        let (mcode_outputs, out) = ecx.image.mcode.reserve_data::<f64>(nleaf * nout);
        for i in 0..nleaf {
            let r = work_link[leaf_bias+i] as usize - 1;
            for (j,&c) in columns.iter().enumerate() {
                if !InputOperator::is_input_u8(c.op) {
                    out[i*nout + c.idx as usize] = ecx.perm[rows.add(r*ncol + j)];
                }
            }
        }
        let rtq = ecx.image.mcode.write_data(&RtTreeQueryV {
            key: core::ptr::null(),
            link: core::ptr::null(),
            op: core::ptr::null(),
            data: core::ptr::null(),
            n_in: nin as _,
            n_out: nout as _,
            leaf_bias: leaf_bias as _
        });
        ecx.image.mcode.relocs.push(
            Reloc::data_abs8(rtq+offset_of!(RtTreeQueryV, key) as MCodeOffset, mcode_key));
        ecx.image.mcode.relocs.push(
            Reloc::data_abs8(rtq+offset_of!(RtTreeQueryV, link) as MCodeOffset, mcode_link));
        ecx.image.mcode.relocs.push(
            Reloc::data_abs8(rtq+offset_of!(RtTreeQueryV, op) as MCodeOffset, mcode_op));
        ecx.image.mcode.relocs.push(
            Reloc::data_abs8(rtq+offset_of!(RtTreeQueryV, data) as MCodeOffset, mcode_outputs));
        ecx.perm.push(TreeValuesData { rtq }).cast()
    } else /* TreeRows */ {
        let (outputs, _) = ecx.perm.reserve_dst::<[DenseOutput]>(nout);
        let cols: BumpRef<Column> = tab.add(1).cast();
        for (j,(col,cinfo)) in zip(
            bump::iter_range(cols..cols.add(ncol)),
            &ecx.tmp[info..info.add(ncol)]
        ).enumerate() {
            let col = ecx.perm[col];
            if !InputOperator::is_input_u8(col.op) {
                let size = Type::from_u8(cinfo.ty).size();
                ecx.image.mcode.align_data(size);
                let (mcode_output, out) = ecx.image.mcode.reserve_data::<u8>(nleaf * size);
                for i in 0..nleaf {
                    let r = work_link[leaf_bias+i] as usize - 1;
                    writepacked(&mut out[i*size..(i+1)*size],cinfo,ecx.perm[rows.add(r*ncol+j)]);
                }
                let out = &mut ecx.perm[outputs.elem(col.idx as usize)];
                out.data = mcode_output;
                out.ty = cinfo.ty;
                out.sign = cinfo.sign;
            }
        }
        let rtq = ecx.image.mcode.write_data(&RtTreeQueryR {
            key: core::ptr::null(),
            link: core::ptr::null(),
            op: core::ptr::null(),
            n_in: nin as _,
            leaf_bias: leaf_bias as _
        });
        ecx.image.mcode.relocs.push(
            Reloc::data_abs8(rtq+offset_of!(RtTreeQueryR, key) as MCodeOffset, mcode_key));
        ecx.image.mcode.relocs.push(
            Reloc::data_abs8(rtq+offset_of!(RtTreeQueryR, link) as MCodeOffset, mcode_link));
        ecx.image.mcode.relocs.push(
            Reloc::data_abs8(rtq+offset_of!(RtTreeQueryR, op) as MCodeOffset, mcode_op));
        ecx.perm.push(TreeRowsData { rtq, outputs: outputs.base() }).cast()
    }
}

fn maketreetab(ecx: &mut Ecx, tab: BumpRef<TabDef>, info: BumpRef<ColumnInfo>) -> BumpRef<()> {
    sortrows(ecx, tab);
    buildtree(ecx, tab, info)
}

#[cfg(feature="csv")]
fn readfile(ecx: &mut Ecx, tab: BumpRef<TabDef>) -> compile::Result {
    let TabDef { file, ncol, .. } = ecx.perm[tab];
    let ncol = ncol as usize;
    let path = match str::from_utf8(&ecx.intern[file]) {
        Ok(path) => path,
        Err(e) => return ecx.error(e)
    };
    let mut reader = match csv::Reader::from_path(path) {
        Ok(reader) => reader,
        Err(e) => return ecx.error(e)
    };
    let mut rec = csv::StringRecord::new();
    let data = ecx.perm.align_for::<f64>().end();
    ecx.perm[tab].rows = data;
    let mut nrow = 0;
    let mut header = 0;
    loop {
        match reader.read_record(&mut rec) {
            Ok(true) => {},
            Ok(false) => {
                ecx.perm[tab].nrow = nrow-header;
                return Ok(());
            },
            Err(e) => return ecx.error(e)
        }
        if rec.len() != ncol {
            ecx.host.set_error(format_args!("{}: expected {} columns, found {}", path, ncol,
                    rec.len()));
            return Err(());
        }
        let start = ecx.perm.end().cast::<f64>();
        for field in &rec {
            let value: f64 = match field.parse() {
                Ok(v) => v,
                Err(e) => {
                    if nrow == 0 {
                        // first row is not a valid number.
                        // i'll just assume it's a header.
                        ecx.perm.truncate(start);
                        header = 1;
                        break;
                    } else {
                        return ecx.error(e);
                    }
                }
            };
            ecx.perm.push(value);
        }
        nrow += 1;
    }
}

#[cfg(not(feature="csv"))]
fn readfile(ecx: &mut Ecx, _tab: BumpRef<TabDef>) -> compile::Result {
    ecx.error("csv support not enabled: recompile with feature `csv`")
}

fn makedata(ecx: &mut Ecx, tab: BumpRef<TabDef>) -> compile::Result<(IndexType, BumpRef<()>)> {
    if !ecx.perm[tab].file.is_empty() {
        readfile(ecx, tab)?;
    }
    let base = ecx.tmp.end();
    let index = analyzetable(ecx, tab);
    ecx.perm[tab].index = index as _;
    let data = match index {
        IndexType::Dense => {
            let data = makedensetab(ecx, tab, base.cast_up());
            ecx.perm.push(data).cast()
        },
        IndexType::TreeRows | IndexType::TreeValues => maketreetab(ecx, tab, base.cast_up()),
        IndexType::Hash => todo!()
    };
    ecx.tmp.truncate(base);
    ecx.perm[tab].data = data;
    Ok((index, data))
}

fn emittref(ecx: &mut Ecx, tab: BumpRef<TabDef>) -> compile::Result<(IndexType, BumpRef<()>)> {
    let TabDef { data, index, .. } = ecx.perm[tab];
    if let Some(index) = IndexType::from_u8(index) {
        Ok((index, data))
    } else {
        makedata(ecx, tab)
    }
}

fn emitdenserow(ecx: &mut Ecx, data: BumpRef<DenseData>, mut args: InsId) -> Value {
    let emit = &mut *ecx.data;
    let mut row = emit.fb.ins().iconst(irt2cl(IRT_IDX), 0);
    let mut prevspan = 0;
    let mut idx = 0;
    let inputs = ecx.perm[data].inputs;
    while emit.code[args].opcode() == Opcode::CARG {
        let (next, value) = emit.code[args].decode_CARG();
        let mut value = emit.values[value].value();
        value = emit.fb.coerce(value, IRT_IDX, Conv::Signed);
        let DenseInput { bias, span } = ecx.perm[inputs.add(idx)];
        if bias != DenseInput::SKIP {
            if bias != 0 {
                value = emit.fb.ins().iadd_imm(value, -bias);
            }
            if prevspan != 0 {
                row = emit.fb.ins().imul_imm(row, prevspan);
            }
            row = emit.fb.ins().iadd(row, value);
            prevspan = span as _;
        }
        idx += 1;
        args = next;
    }
    row
}

fn emittreerow(ecx: &mut Ecx, data: BumpRef<TreeRowsData>, arg: InsId) -> Value {
    let emit = &mut *ecx.data;
    let mut sig = cranelift_codegen::ir::Signature::new(NATIVE_CALLCONV);
    TREELOOKUPR_SIGNATURE.to_cranelift(&mut sig);
    let sig = emit.fb.ctx.func.import_signature(sig);
    let treelookupfunc = emit.fb.ins().iconst(irt2cl(Type::PTR), rt_treelookupr as i64);
    let rtq = emit.fb.usedata(ecx.perm[data].rtq);
    let arg = emit.values[arg].value();
    let call = emit.fb.ins().call_indirect(sig, treelookupfunc, &[rtq, arg]);
    emit.fb.ctx.func.dfg.inst_results(call)[0]
}

fn emit_trow(ecx: &mut Ecx, id: InsId) -> compile::Result<Value> {
    let (tref, args, _) = ecx.data.code[id].decode_LOVV();
    Ok(match emittref(ecx, zerocopy::transmute!(ecx.data.code[tref].bc()))? {
        (IndexType::Dense, data) => emitdenserow(ecx, data.cast(), args),
        (IndexType::TreeRows, data) => emittreerow(ecx, data.cast(), args),
        (IndexType::TreeValues, _) => unreachable!(), // TROW not emitted
        (IndexType::Hash, _) => todo!(),
    })
}

fn emitdensedataptr(ecx: &mut Ecx, output: BumpRef<DenseOutput>) -> (Value, Type, bool) {
    let DenseOutput { data, ty, sign, .. } = ecx.perm[output];
    let data = ecx.data.fb.usedata(data);
    (data, Type::from_u8(ty), sign != 0)
}

fn emit_tget(ecx: &mut Ecx, id: InsId) -> compile::Result<Value> {
    let (tcol, row, _) = ecx.data.code[id].decode_LOVV();
    let (tref, output, _) = ecx.data.code[tcol].decode_LOVX();
    let (dataptr, datatype, sign) = match emittref(ecx,
        zerocopy::transmute!(ecx.data.code[tref].bc()))?
    {
        (IndexType::Dense, data) => emitdensedataptr(
            ecx, ecx.perm[data.cast::<DenseData>()].outputs.add(output as usize)),
        (IndexType::TreeRows, data) => emitdensedataptr(
            ecx, ecx.perm[data.cast::<TreeRowsData>()].outputs.add(output as usize)),
        (IndexType::TreeValues, _) => unreachable!(), // TGET not emitted
        (IndexType::Hash, _) => todo!(),
    };
    let emit = &mut *ecx.data;
    let row = emit.values[row].value();
    let ofs = emit.fb.ins().imul_imm(row, datatype.size() as i64);
    // TODO: rework IRT_IDX handling so that this coercion is not needed
    let ofs = emit.fb.coerce(ofs, Type::I64, Conv::Signed);
    let dataptr = emit.fb.ins().iadd(dataptr, ofs);
    let value = emit.fb.ins().load(irt2cl(datatype), MemFlags::trusted().with_readonly(),
        dataptr, 0);
    let outtype = emit.code[id].type_();
    Ok(emit.fb.coerce(value, outtype, match sign { true=>Conv::Signed, false=>Conv::Unsigned }))
}

fn emit_tval(ecx: &mut Ecx, id: InsId) -> compile::Result<cranelift_codegen::ir::Inst> {
    let (tref, arg, _) = ecx.data.code[id].decode_LOVV();
    let (_, tab) = emittref(ecx, zerocopy::transmute!(ecx.data.code[tref].bc()))?;
    let TreeValuesData { rtq } = ecx.perm[tab.cast()];
    let mut sig = cranelift_codegen::ir::Signature::new(NATIVE_CALLCONV);
    TREELOOKUPV_SIGNATURE.to_cranelift(&mut sig);
    let sig = ecx.data.fb.ctx.func.import_signature(sig);
    let treelookupfunc = ecx.data.fb.ins().iconst(irt2cl(Type::PTR), rt_treelookupv as i64);
    let rtq = ecx.data.fb.usedata(rtq);
    let arg = ecx.data.values[arg].value();
    Ok(ecx.data.fb.ins().call_indirect(sig, treelookupfunc, &[rtq, arg]))
}

/* -------------------------------------------------------------------------- */

impl Language for Table {

    fn parse(pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALL>> {
        parse_call(pcx, n)
    }

    fn lower(
        lcx: &mut CLcx,
        ctr: InsId,
        obj: ObjRef<CALL>,
        func: &Func,
        inputs: &[InsId]
    ) -> InsId {
        lower_call(lcx, ctr, obj, func, inputs)
    }

    fn begin_emit(_: &mut Ccx) -> compile::Result<Self> {
        Ok(Table)
    }

    fn emit(ecx: &mut Ecx, id: InsId, lop: u8) -> compile::Result<InsValue> {
        Ok(match lop {
            LOP_TROW => InsValue::from_value(emit_trow(ecx, id)?),
            LOP_TGET => InsValue::from_value(emit_tget(ecx, id)?),
            LOP_TVAL => InsValue::from_cl_inst(emit_tval(ecx, id)?),
            _ => unreachable!()
        })
    }

}
