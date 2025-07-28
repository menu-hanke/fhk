//! R language support.

// useful references:
//   * https://cran.r-project.org/doc/manuals/R-exts.html
//   * https://cran.r-project.org/doc/manuals/r-devel/R-ints.html
//   * https://github.com/r-devel/r-svn/blob/main/src/include/Rinternals.h
//   * https://github.com/hadley/r-internals

use core::ffi::{c_char, c_int, c_void, CStr};
use core::iter::zip;
use core::ptr::NonNull;

use alloc::boxed::Box;
use cranelift_codegen::ir::InstBuilder;
use zerocopy::Unalign;

use crate::array::{Array, ArrayBuf, ArrayMut, ArrayType};
use crate::bump::{AlignedBytes, BumpRef};
use crate::compile::Ccx;
use crate::data::CALL_R;
use crate::dl::LibBox;
use crate::emit::{irt2cl, signature, Ecx, Emit, InsValue, Signature, NATIVE_CALLCONV};
use crate::image::{fhk_vmexit, Instance};
use crate::ir::{Func, Ins, InsId, LangOp, Opcode, Type};
use crate::lower::{areserve, decompose, decomposition, decomposition_size, reserve, CLcx};
use crate::mem::{CursorA, CursorType};
use crate::typing::{Idx, Primitive, IRT_IDX};
use crate::{compile, dl};
use crate::intern::IRef;
use crate::lang::{Lang, Language};
use crate::lex::Token;
use crate::obj::{ObjRef, ObjectRef, CALL, TTUP};
use crate::parse::parse_expr;
use crate::parser::{check, consume, Pcx};

#[cfg(unix)]
const R_LIBNAME: &'static [u8] = b"/usr/lib/R/lib/libR.so\0";

#[cfg(windows)]
const R_LIBNAME: &'static [u8] = b"R.dll\0";

// unfortunately there's no good way to tell if anyone else is using the R environment,
// nor is there even a way to tell if it's already initialized.
// the best we can really do is refcount our own uses.
//
// note that the counter is not atomic!
// our R caller is not thread-safe, so it's not worth making it thread-safe because that
// would mean locking on every single call to the R environment.
// since the R caller is not intended to be thread-safe anyway, it's not worth making the
// refcount atomic either.
static mut REFCOUNT: usize = 0;

// TODO: check during compilation that all arrays passed into rcall will fit.
// rcall then doesn't have to do any bound checking etc.
const ABUFSLOTS: usize = 32;

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
struct SEXP(NonNull<c_void>);

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
enum SEXPTYPE {
    // NILSXP     =  0,
    // SYMSXP     =  1,
    // LISTSXP    =  2,
    // CLOSXP     =  3,
    // ENVSXP     =  4,
    // PROMSXP    =  5,
    LANGSXP    =  6,
    // SPECIALSXP =  7,
    // BUILTINSXP =  8,
    // CHARSXP    =  9,
    LGLSXP     = 10,
    INTSXP     = 13,
    REALSXP    = 14,
    // CPLXSXP    = 15,
    STRSXP     = 16,
    // DOTSXP     = 17,
    // ANYSXP     = 18,
    VECSXP     = 19,
    // EXPRSXP    = 20,
    // BCODESXP   = 21,
    // EXTPTRSXP  = 22,
    // WEAKREFSXP = 23,
    // RAWSXP     = 24,
    // S4SXP      = 25,
    // NEWSXP     = 30,
    // FREESXP    = 31,
    // FUNSXP     = 99,
}

impl SEXPTYPE {

    fn size(self) -> usize {
        use SEXPTYPE::*;
        match self {
            LANGSXP => 0,
            INTSXP|LGLSXP => size_of::<c_int>(),
            REALSXP => size_of::<f64>(),
            STRSXP => 1,
            VECSXP => size_of::<SEXP>()
        }
    }

}

// R_xlen_t is ptrdiff_t on 64 bits, int on 32 bits, but fhk doesn't support 32 bits anyway.
type R_xlen_t = isize;
type R_len_t = c_int;

macro_rules! r_api {
    (
        $(rt fn $rname:ident($($rpname:ident : $rpty:ty),*) $(-> $rrty:ty)?;)*
        $(fn $name:ident($($pname:ident : $pty:ty),*) $(-> $rty:ty)?;)*
        $(rt extern $rsname:ident: $rsty:ty;)*
        $(extern $sname:ident: $sty:ty;)*
    ) => {
        dl::lib! {
            struct LibR {
                $( fn $rname($($rpname:$rpty),*) $(-> $rrty)?; )*
                $( fn $name($($pname:$pty),*) $(-> $rty)?; )*
                $( extern $rsname: $rsty; )*
                $( extern $sname: $sty; )*
            }
        }

        struct RuntimeLibR {
            $( $rname: unsafe extern "C" fn($($rpty),*) $(-> $rrty)?, )*
            $( $rsname: $rsty, )*
        }

        // zerocopy refuses to implement IntoBytes for pointers. sigh.
        unsafe impl crate::bump::IntoBytes for RuntimeLibR {}
        unsafe impl crate::bump::Immutable for RuntimeLibR {}

        impl RuntimeLibR {
            fn new(lib: &LibR) -> Self {
                Self {
                    $( $rname: lib.$rname, )*
                    $( $rsname: unsafe { *lib.$rsname }, )*
                }
            }
        }
    };
}

r_api! {
    rt fn R_tryEval(e: SEXP, env: SEXP, err: *mut c_int) -> SEXP;
    rt fn R_curErrorBuf() -> *const c_char;
    rt fn Rf_protect(s: SEXP) -> SEXP;
    rt fn Rf_unprotect(n: c_int);
    rt fn Rf_allocVector(sexp_t: SEXPTYPE, n: R_xlen_t) -> SEXP;
    rt fn Rf_allocList(n: c_int) -> SEXP;
    rt fn Rf_setAttrib(vec: SEXP, name: SEXP, val: SEXP) -> SEXP;
    rt fn Rf_getAttrib(vec: SEXP, name: SEXP) -> SEXP;
    rt fn Rf_length(x: SEXP) -> R_len_t;
    rt fn CDR(x: SEXP) -> SEXP;
    rt fn SETCAR(x: SEXP, y: SEXP) -> SEXP;
    rt fn SET_TYPEOF(x: SEXP, ty: SEXPTYPE) -> SEXP;
    rt fn TYPEOF(x: SEXP) -> SEXPTYPE;
    rt fn DATAPTR(x: SEXP) -> *mut c_void;
    rt fn SET_VECTOR_ELT(x: SEXP, i: R_xlen_t, v: SEXP) -> SEXP;
    fn R_PreserveObject(object: SEXP);
    fn R_ReleaseObject(object: SEXP);
    fn R_ParseEvalString(str: *const c_char, env: SEXP) -> SEXP;
    fn Rf_initEmbeddedR(argc: c_int, argv: *const *const c_char) -> c_int;
    fn Rf_endEmbeddedR(fatal: c_int);
    fn Rf_mkCharLen(s: *const c_char, n: c_int) -> SEXP;
    fn Rf_lang3(x1: SEXP, x2: SEXP, x3: SEXP) -> SEXP;
    fn SET_STRING_ELT(x: SEXP, i: R_xlen_t, v: SEXP);
    rt extern R_GlobalEnv: SEXP;
    rt extern R_DimSymbol: SEXP;
    extern R_NilValue: SEXP;
    extern R_SignalHandlers: c_int;
}

pub struct R {
    lib: Box<LibR>, // boxed to keep size of LangState reasonable.
    loader: SEXP,
    rt: BumpRef<RuntimeLibR>
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct RFunc {
    source: IRef<[u8]>,
    expr: IRef<[u8]>,
}

// note: if you change the layout, make sure to also update the construction in emit_call.
#[repr(C)]
struct Call {
    fun: SEXP,
    narg: u8,
    nret: u8,
    aty: [u8; 0], // packed array of (ofs: u16, aty: [u8; <variable length>])
}

// execute an R function call.
// FX LOVV (CARG LOP_VALUE*) (KREF IRef<RFunc>)
const LOP_CALL: u8 = 0;

// LSV LOVV ([A]BOX) (KREF type)
const LOP_INPUT: u8 = 1;
const LOP_OUTPUT: u8 = 2;

/* ---- Parsing ------------------------------------------------------------- */

fn parse_call(pcx: &mut Pcx) -> compile::Result<ObjRef<CALL>> {
    consume(pcx, Token::LBracket)?;
    let (source, expr) = {
        let lit: IRef<[u8]> = zerocopy::transmute!(consume(pcx, Token::Literal)?);
        if check(pcx, Token::Colon)? {
            (lit, zerocopy::transmute!(consume(pcx, Token::Literal)?))
        } else {
            (IRef::EMPTY, lit)
        }
    };
    let rf = pcx.intern.intern(&RFunc { source, expr });
    consume(pcx, Token::RBracket)?;
    consume(pcx, Token::LParen)?;
    let base = pcx.tmp.end();
    while pcx.data.token != Token::RParen {
        let v = parse_expr(pcx)?;
        pcx.tmp.push(v);
        if !check(pcx, Token::Comma)? { break }
    }
    consume(pcx, Token::RParen)?;
    let callx = pcx.objs.push_args(
        CALL::new(Lang::R as _, ObjRef::NIL, zerocopy::transmute!(rf)),
        &pcx.tmp[base.cast_up()..]
    );
    pcx.tmp.truncate(base);
    Ok(callx)
}

/* ---- Lowering ------------------------------------------------------------ */

fn lower_call(
    lcx: &mut CLcx,
    ctr: InsId,
    obj: ObjRef<CALL>,
    func: &Func,
    inputs: &[InsId]
) -> InsId {
    let mut args = func.code.push(Ins::NOP(Type::LSV));
    let [call] = areserve(func);
    let callx = &lcx.objs[obj];
    let ds = decomposition_size(&lcx.objs, callx.ann);
    let mut out = reserve(func, ds) + ds as isize;
    let outann = match lcx.objs.get(callx.ann) {
        ObjectRef::TTUP(TTUP { elems, .. }) => elems,
        _ => &[callx.ann],
    };
    let base = lcx.tmp.end();
    for &a in outann.iter().rev() {
        let [abox] = areserve(func);
        let ty = func.code.push(Ins::KREF(zerocopy::transmute!(a)));
        let output = func.code.push(Ins::LOVV(Type::LSV, abox, ty, LangOp::R(LOP_OUTPUT)));
        args = func.code.push(Ins::CARG(args, output));
        let ptr = func.code.push(Ins::BREF(abox));
        let ptr = func.code.push(Ins::MOVF(Type::PTR, ptr, call));
        let mut cursor = CursorA::default();
        let deco = decomposition(&lcx.objs, a, &mut lcx.tmp);
        out -= deco.len() as isize;
        let mut curout = out;
        for &ty in &*deco {
            let ofs = cursor.alloc_type(ty);
            let ofs = func.code.push(Ins::KINT(Type::I64, ofs as _));
            let ptr = func.code.push(Ins::ADDP(ptr, ofs));
            func.code.set(curout, Ins::LOAD(ty, ptr));
            curout += 1;
        }
        lcx.tmp.truncate(base);
        func.code.set(abox, Ins::ABOX(ctr, cursor.ptr as _, cursor.align as _));
    }
    for (&i,&o) in zip(inputs, &callx.inputs).rev() {
        let ann = lcx.objs[o].ann;
        let ty = func.code.push(Ins::KREF(zerocopy::transmute!(ann)));
        let value = decompose(func, &lcx.objs, ann, i);
        let value = func.code.push(Ins::BOX(value));
        let value = func.code.push(Ins::LOVV(Type::LSV, value, ty, LangOp::R(LOP_INPUT)));
        args = func.code.push(Ins::CARG(args, value));
    }
    let fref = func.code.push(Ins::KREF(callx.func));
    func.code.set(call, Ins::LOVV(Type::FX, args, fref, LangOp::R(LOP_CALL)));
    out
}

/* ---- Emitting ------------------------------------------------------------ */

unsafe fn rinit(lib: &LibR) -> compile::Result {
    // this check *could* be put behind a config, but R probably isn't supported on any platform
    // where you would want no_std anyway.
    extern crate std;
    if std::env::var("R_HOME").is_err() {
        // R_HOME is not set. try running `R RHOME`.
        if let Ok(mut output) = std::process::Command::new("R").arg("RHOME").output() {
            // on linux this contains a trailing newline, on windows it doesn't.
            if let Some(&b'\n') = output.stdout.last() {
                output.stdout.pop();
            }
            unsafe {
                std::env::set_var(
                    "R_HOME",
                    std::ffi::OsStr::from_encoded_bytes_unchecked(&output.stdout)
                );
            }
        } else {
            // TODO: report error
            todo!()
            // emit.error.push_str("R_HOME is not set");
            // return Err(());
        }
    }
    let argv: [*const i8; 3] = [c"R".as_ptr(), c"--quiet".as_ptr(), c"--no-save".as_ptr()];
    unsafe {
        *lib.R_SignalHandlers = 0;
        // TODO: can a failure here be caught?
        lib.Rf_initEmbeddedR(argv.len() as _, argv.as_ptr());
    }
    Ok(())
}

fn begin_emit(ccx: &mut Ccx) -> compile::Result<R> {
    // load libR
    let lib = match dl::open(R_LIBNAME) {
        Some(lib) => lib,
        None => {
            // TODO: try calling 'R RHOME' first
            // TODO: then report error
            todo!()
        }
    };
    let lib = match LibR::new(lib) {
        Some(lib) => Box::new(lib),
        None => {
            // TODO: report error
            todo!()
        }
    };
    // init R if not yet initialized
    unsafe {
        if REFCOUNT == 0 {
            rinit(&lib)?;
        }
        REFCOUNT += 1;
    }
    // load the loader. this cannot fail.
    let loader = unsafe { lib.R_ParseEvalString(CALL_R.as_ptr().cast(), *lib.R_GlobalEnv) };
    // define the runtime library.
    let rt = ccx.mcode.data.intern(&RuntimeLibR::new(&lib)).to_bump();
    Ok(R { lib, loader, rt })
}

fn optstring(lib: &LibR, s: &[u8]) -> SEXP {
    if s.is_empty() {
        unsafe { *lib.R_NilValue }
    } else {
        unsafe {
            let t = lib.Rf_protect(lib.Rf_allocVector(SEXPTYPE::STRSXP, 1));
            let v = lib.Rf_protect(lib.Rf_mkCharLen(s.as_ptr().cast(), s.len() as _));
            lib.SET_STRING_ELT(t, 0, v);
            lib.Rf_unprotect(2);
            t
        }
    }
}

fn emit_call(ecx: &mut Ecx, id: InsId) -> compile::Result<InsValue> {
    let emit = &mut *ecx.data;
    let (mut args, rf) = emit.code[id].decode_VV();
    let &mut R { ref lib, loader, rt } = emit.lang.R();
    let fun = {
        let rf: &RFunc = &ecx.intern[zerocopy::transmute!(emit.code[rf].bc())];
        let mut err = 0;
        unsafe {
            let source = lib.Rf_protect(optstring(lib, ecx.intern.get_slice(rf.source)));
            let expr = lib.Rf_protect(optstring(lib, ecx.intern.get_slice(rf.expr)));
            let call = lib.Rf_lang3(loader, source, expr);
            let fun = lib.R_tryEval(call, *lib.R_GlobalEnv, &mut err);
            lib.Rf_unprotect(2);
            if err != 0 {
                ecx.host.buf.write(CStr::from_ptr(lib.R_curErrorBuf()).to_bytes());
                return Err(());
            }
            fun
        }
    };
    let base = ecx.tmp.end();
    let mut narg = 0;
    let mut nret = 0;
    // layout `Call` by hand because zerocopy doesn't let us derive the traits. sigh.
    ecx.tmp.push(Unalign::<usize>::new(fun.0.as_ptr() as _));
    let info = ecx.tmp.push([0u8, 0u8]); // narg, nret
    while emit.code[args].opcode() != Opcode::NOP {
        let (next, value) = emit.code[args].decode_CARG();
        match emit.code[value].decode_L().op {
            LOP_INPUT => narg += 1,
            _ /* OUTPUT */ => nret += 1
        }
        debug_assert!({
            let lop = emit.code[value].decode_L();
            lop == LangOp::R(LOP_INPUT) || lop == LangOp::R(LOP_OUTPUT)
        });
        let (value, ty) = emit.code[value].decode_VV();
        ecx.tmp.push(Unalign::<u16>::new(emit.values[value].raw as _));
        let aty = ArrayType::from_obj(&ecx.objs, zerocopy::transmute!(emit.code[ty].bc()));
        aty.pack_into(&mut ecx.tmp);
        args = next;
    }
    ecx.tmp[info] = [narg, nret];
    let calldata = emit.fb.importdata(
        &mut ecx.mcode,
        AlignedBytes::<{align_of::<Call>()}>::new(&ecx.tmp[base..])
    );
    ecx.tmp.truncate(base);
    let calldata = emit.fb.dataptr(calldata);
    let rt = emit.fb.importdataref(rt.cast());
    let rt = emit.fb.dataptr(rt);
    let mut sig = cranelift_codegen::ir::Signature::new(NATIVE_CALLCONV);
    CALL_SIGNATURE.to_cranelift(&mut sig);
    let sig = emit.fb.ctx.func.import_signature(sig);
    let callfunc = emit.fb.ins().iconst(irt2cl(Type::PTR), call as i64);
    let frame = emit.fb.frame(&mut emit.frame).slot;
    let frame = emit.fb.ins().stack_addr(irt2cl(Type::PTR), frame, 0);
    let vmctx = emit.fb.vmctx();
    let call = emit.fb.ins().call_indirect(sig, callfunc, &[vmctx, rt, calldata, frame]);
    Ok(InsValue::from_cl_inst(call))
}

/* ---- Runtime ------------------------------------------------------------- */

fn pri2sexp(pri: Primitive) -> SEXPTYPE {
    use Primitive::*;
    match pri {
        F64 | F32 => SEXPTYPE::REALSXP,
        I64 | I32 | I16 | I8 | U64 | U32 | U16 | U8 => SEXPTYPE::INTSXP,
        B1 => SEXPTYPE::LGLSXP,
        STR => SEXPTYPE::STRSXP,
        PTR => todo!("pri2sexp ptr") // does this even make sense to implement?
    }
}

unsafe fn importprivalue(dst: *mut (), src: *const (), pri: Primitive) {
    use Primitive::*;
    unsafe {
        match pri {
            F64 => *dst.cast::<f64>()       = *src.cast::<f64>(),
            F32 => *dst.cast::<f64>()       = *src.cast::<f32>() as _,
            I64|U64 => *dst.cast::<c_int>() = *src.cast::<i64>() as _,
            I32|U32 => *dst.cast::<c_int>() = *src.cast::<i32>(),
            I16 => *dst.cast::<c_int>()     = *src.cast::<i16>() as _,
            I8  => *dst.cast::<c_int>()     = *src.cast::<i8>() as _,
            U16 => *dst.cast::<c_int>()     = *src.cast::<u16>() as _,
            U8|B1 => *dst.cast::<c_int>()   = *src.cast::<u8>() as _,
            STR|PTR => todo!("importprivalue ptr") // is str c_char?
        }
    }
}

unsafe fn importscalar(lib: &RuntimeLibR, src: *const (), pri: Primitive) -> SEXP {
    unsafe {
        let v = (lib.Rf_allocVector)(pri2sexp(pri), 1);
        importprivalue((lib.DATAPTR)(v) as _, src, pri);
        v
    }
}

unsafe fn importarray(lib: &RuntimeLibR, array: Array) -> SEXP {
    let type_ = array.type_();
    let ety = match type_.is_tensor() {
        true => pri2sexp(type_.primitive()),
        _ => SEXPTYPE::VECSXP
    };
    let (vec, size) = match array.shape() {
        &[size] => {
            let vec = unsafe { (lib.Rf_protect)((lib.Rf_allocVector)(ety, size as _)) };
            (vec, size)
        },
        shape => unsafe {
            let size: Idx = shape.iter().product();
            let vec = (lib.Rf_protect)((lib.Rf_allocVector)(ety, size as _));
            let dims = (lib.Rf_protect)((lib.Rf_allocVector)(SEXPTYPE::INTSXP, shape.len() as _));
            let data = (lib.DATAPTR)(dims) as *mut u32;
            for (i,&s) in shape.iter().enumerate() {
                *data.add(i) = s;
            }
            (lib.Rf_setAttrib)(vec, lib.R_DimSymbol, dims);
            (lib.Rf_unprotect)(1);
            (vec, size)
        }
    };
    let size = size as usize;
    let dsize = ety.size();
    if type_.is_tensor() {
        let pri = type_.primitive();
        let mut data = unsafe { (lib.DATAPTR)(vec) as *mut u8 };
        let mut src = array.data()[0] as *const u8;
        if (Primitive::F64|Primitive::I32|Primitive::U32).contains(pri) {
            unsafe { core::ptr::copy_nonoverlapping(src, data, dsize*size); }
        } else {
            let esize = pri.size();
            for _ in 0..size {
                unsafe {
                    importprivalue(data.cast(), src.cast(), pri);
                    data = data.add(dsize);
                    src = src.add(esize);
                }
            }
        }
    } else {
        let mut buf = ArrayBuf::<ABUFSLOTS>::default();
        for i in 0..size {
            unsafe {
                let v = importarray(lib, array.get(i, &mut buf));
                (lib.SET_VECTOR_ELT)(vec, i as _, v);
            }
        }
    }
    vec
}

unsafe fn importvalue(lib: &RuntimeLibR, ptr: *const (), aty: ArrayType) -> SEXP {
    unsafe {
        match aty.is_scalar() {
            true  => importscalar(lib, ptr, aty.primitive()),
            false => importarray(lib, Array::new_unchecked(NonNull::new_unchecked(ptr as _), aty))
        }
    }
}

unsafe fn exportprivalue(dst: *mut (), src: *const (), pri: Primitive, vty: SEXPTYPE) {
    use {Primitive::*, SEXPTYPE::*};
    unsafe {
        match vty {
            REALSXP => {
                let value = *src.cast::<f64>();
                match pri {
                    F64      => *dst.cast::<f64>() = value,
                    F32      => *dst.cast::<f32>() = value as _,
                    I64      => *dst.cast::<i64>() = value as _,
                    U64      => *dst.cast::<u64>() = value as _,
                    I32      => *dst.cast::<i32>() = value as _,
                    U32      => *dst.cast::<u32>() = value as _,
                    I16      => *dst.cast::<i16>() = value as _,
                    U16      => *dst.cast::<u16>() = value as _,
                    I8       => *dst.cast::<i8>()  = value as _,
                    U8       => *dst.cast::<u8>()  = value as _,
                    B1       => *dst.cast::<u8>()  = (value != 0.0) as _,
                    _ => unreachable!()
                }
            },
            INTSXP|LGLSXP => {
                let value = *src.cast::<c_int>();
                match pri {
                    F64      => *dst.cast::<f64>() = value as _,
                    F32      => *dst.cast::<f32>() = value as _,
                    I64      => *dst.cast::<i64>() = value as _,
                    U64      => *dst.cast::<u64>() = value as _,
                    I32|U32  => *dst.cast::<i32>() = value,
                    I16|U16  => *dst.cast::<i16>() = value as _,
                    I8|U8    => *dst.cast::<i8>()  = value as _,
                    B1       => *dst.cast::<u8>()  = (value != 0) as _,
                    _ => unreachable!()
                }
            },
            _ => {
                todo!("error reporting (bad primitive SEXPTYPE)")
            }
        }
    }
}

unsafe fn exportscalar(lib: &RuntimeLibR, dst: *mut (), src: SEXP, pri: Primitive) {
    unsafe { exportprivalue(dst, (lib.DATAPTR)(src) as _, pri, (lib.TYPEOF)(src)) }
}

unsafe fn exportarray(vmctx: &mut Instance, lib: &RuntimeLibR, value: SEXP, mut array: ArrayMut) {
    let type_ = array.borrow().type_();
    let size = unsafe { (lib.Rf_length)(value) as usize };
    match unsafe { array.borrow_mut().shape_mut() } {
        [s] => *s = size as _,
        shape => unsafe {
            let dims = (lib.Rf_getAttrib)(value, lib.R_DimSymbol);
            if (lib.Rf_length)(dims) != shape.len() as _ {
                todo!("error reporting (R returned bad array shape)")
            }
            let data = (lib.DATAPTR)(dims) as *const u32;
            for (i,s) in shape.iter_mut().enumerate() {
                *s = *data.add(i);
            }
        }
    }
    let src = unsafe { (lib.DATAPTR)(value) };
    let vty = unsafe { (lib.TYPEOF)(value) };
    if type_.is_tensor() {
        let pri = type_.primitive();
        let esize = pri.size();
        let mut data = vmctx.host.alloc(esize*size, esize);
        unsafe { array.data_mut()[0] = data.cast() };
        let mut src = src as *const u8;
        if matches!((pri, vty), (Primitive::F64, SEXPTYPE::REALSXP)
            | (Primitive::I32|Primitive::U32, SEXPTYPE::INTSXP|SEXPTYPE::LGLSXP))
        {
            unsafe { core::ptr::copy_nonoverlapping(src, data, esize*size); }
        } else {
            let vsize = vty.size();
            for _ in 0..size {
                unsafe {
                    exportprivalue(data.cast(), src.cast(), pri, vty);
                    src = src.add(vsize);
                    data = data.add(esize);
                }
            }
        }
    } else {
        if vty != SEXPTYPE::VECSXP {
            todo!("report error (expected list)")
        }
        let data = unsafe { array.borrow_mut().data_mut() };
        let mut buf = ArrayBuf::<ABUFSLOTS>::default();
        let elem = type_.element();
        let edim = elem.dimension();
        let ds = elem.decomposition_size();
        for i in 0..ds {
            data[i] = vmctx.host.alloc(Type::PTR.size()*size, Type::PTR.size()).cast();
        }
        for i in ds..ds+edim {
            data[i] = vmctx.host.alloc(IRT_IDX.size()*size, IRT_IDX.size()).cast();
        }
        for i in 0..size {
            let mut tmp = ArrayMut::new_empty(elem, &mut buf);
            unsafe {
                exportarray(vmctx, lib, *src.cast::<SEXP>().add(i), tmp.borrow_mut());
                for (j,&t) in tmp.borrow().data().iter().enumerate() {
                    *data[j].cast::<*const ()>() = t;
                }
                for (j,&s) in tmp.borrow().shape().iter().enumerate() {
                    *data[ds+j].cast::<Idx>() = s;
                }
            }
        }
    }
}

unsafe fn exportvalue(
    vmctx: &mut Instance,
    lib: &RuntimeLibR,
    value: SEXP,
    aty: ArrayType,
    ptr: *mut ()
) {
    unsafe {
        match aty.is_scalar() {
            true  => exportscalar(lib, ptr, value, aty.primitive()),
            false => exportarray(vmctx, lib, value,
                ArrayMut::new_unchecked_mut(NonNull::new_unchecked(ptr), aty))
        }
    }
}

const CALL_SIGNATURE: &Signature = &signature!(NATIVE_CALLCONV, PTR PTR PTR PTR);
unsafe extern "C" fn call(
    vmctx: &mut Instance,
    lib: &RuntimeLibR,
    call: *const Call,
    frame: *mut u8
) {
    unsafe {
        let Call { narg, nret, fun, .. } = *call;
        let c = (lib.Rf_protect)((lib.Rf_allocList)(1 + narg as c_int));
        (lib.SET_TYPEOF)(c, SEXPTYPE::LANGSXP);
        (lib.SETCAR)(c, fun);
        let mut s = c;
        let mut ptr = &raw const (*call).aty as *const u8;
        for _ in 0..narg {
            let ofs = ptr.cast::<u16>().read_unaligned();
            ptr = ptr.add(2);
            let v = importvalue(lib, frame.add(ofs as _).cast(), ArrayType::unpack_unchecked(&mut ptr));
            s = (lib.CDR)(s);
            (lib.SETCAR)(s, v);
        }
        let mut err = 0;
        let result = (lib.R_tryEval)(c, lib.R_GlobalEnv, &mut err);
        (lib.Rf_unprotect)(1);
        if err != 0 {
            vmctx.host.set_error(CStr::from_ptr((lib.R_curErrorBuf)()).to_bytes());
            fhk_vmexit(vmctx);
        }
        (lib.Rf_protect)(result);
        match nret {
            1 => {
                let ofs = ptr.cast::<u16>().read_unaligned();
                ptr = ptr.add(2);
                let aty = ArrayType::unpack_unchecked(&mut ptr);
                exportvalue(vmctx, lib, result, aty, frame.add(ofs as _).cast());
            },
            n => {
                if (lib.TYPEOF)(result) != SEXPTYPE::VECSXP {
                    todo!("error reporting (expected list)")
                }
                let data = (lib.DATAPTR)(result) as *const SEXP;
                for i in 0..n {
                    let ofs = ptr.cast::<u16>().read_unaligned();
                    ptr = ptr.add(2);
                    let aty = ArrayType::unpack_unchecked(&mut ptr);
                    exportvalue(vmctx, lib, *data.add(i as _), aty, frame.add(ofs as _).cast());
                }
            }
        }
        (lib.Rf_unprotect)(1);
    }
}

/* ---- Finalization -------------------------------------------------------- */

struct RFinalizer {
    _lib: LibBox,
    loader: SEXP,
    R_ReleaseObject: unsafe extern "C" fn(SEXP),
    Rf_endEmbeddedR: unsafe extern "C" fn(c_int)
}

impl Drop for RFinalizer {
    fn drop(&mut self) {
        unsafe {
            REFCOUNT -= 1;
            if REFCOUNT == 0 {
                (self.Rf_endEmbeddedR)(0)
            } else {
                (self.R_ReleaseObject)(self.loader);
            }
        }
    }
}

/* -------------------------------------------------------------------------- */

impl Language for R {

    fn parse(pcx: &mut Pcx, _: usize) -> compile::Result<ObjRef<CALL>> {
        parse_call(pcx)
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

    fn begin_emit(ccx: &mut Ccx) -> compile::Result<Self> {
        begin_emit(ccx)
    }

    fn emit(ecx: &mut Ecx, id: InsId, lop: u8) -> compile::Result<InsValue> {
        debug_assert!(lop == LOP_CALL);
        emit_call(ecx, id)
    }

    fn finish_emit(self, ccx: &mut Ccx<Emit>) -> compile::Result {
        ccx.fin.push(RFinalizer {
            _lib: self.lib.lib,
            loader: self.loader,
            R_ReleaseObject: self.lib.R_ReleaseObject,
            Rf_endEmbeddedR: self.lib.Rf_endEmbeddedR
        });
        Ok(())
    }

}
