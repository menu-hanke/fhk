//! Lua language support.

use core::ffi::{c_char, c_int, c_void, CStr};
use core::iter::zip;

use cfg_if::cfg_if;
use cranelift_codegen::ir::{InstBuilder, MemFlags};
use zerocopy::Unalign;

use crate::bitmap::BitmapWord;
use crate::bump::{self, BumpRef, BumpVec};
use crate::compile::{self, Ccx};
use crate::data::{CALL_LUA, TENSOR_LUA};
use crate::emit::{irt2cl, Ecx, Emit, InsValue};
use crate::image::{fhk_swap, fhk_swap_exit, fhk_swap_init, fhk_swap_instance, SwapInit};
use crate::intern::IRef;
use crate::ir::{Func, Ins, InsId, LangOp, Opcode, Type};
use crate::lang::{Lang, Language};
use crate::lex::Token;
use crate::lower::{decomposition, decomposition_size, reserve, CLcx};
use crate::mmap::{Mmap, Prot};
use crate::obj::{Obj, ObjRef, ObjectRef, Objects, CALLX, EXPR, NEW, TPRI, TTEN, TTUP, TVAR};
use crate::parse::parse_expr;
use crate::parser::{check, consume, next, require, Pcx};
use crate::support::SuppFunc;

#[cfg(all(unix, not(feature="host-Lua")))]
const LJ_LIBNAME: &'static [u8] = b"libluajit.so\0libluajit-5.1.so\0";

// TODO: make this configurable?
#[cfg(unix)]
const CORO_STACK: usize = 1024 * 16;

#[cfg(windows)]
const CORO_STACK: usize = 1024 * 128;

type lua_State = c_void;

cfg_if! {

    if #[cfg(feature="host-Lua")] {

        macro_rules! lua_api {
            ( $(fn $name:ident($($pname:ident : $pty:ty),*) $(-> $rty:ty)?;)* ) => {
                mod host_liblua {
                    use super::*;
                    // these should really be "C-unwind", but we handle Lua errors manually
                    // with pcall() so in practice these shouldn't unwind.
                    // (unfortunately it's not possible to have lua exceptions unwind rust stack
                    //  while compiling with panic="abort" due to some horrible design decisions
                    //  by the rust people, as usual.)
                    #[allow(clashing_extern_declarations)]
                    extern "C" {
                        $(
                            pub fn $name($($pname:$pty),*) $(-> $rty)?;
                        )*
                    }
                }
                struct LuaLib;
                impl LuaLib {
                    $(
                        #[inline(always)]
                        #[allow(dead_code)]
                        unsafe fn $name(&self, $($pname:$pty),*) $(-> $rty)? {
                            host_liblua::$name($($pname),*)
                        }
                    )*
                }
            }
        }

        fn open_liblua(_: &mut Ccx) -> compile::Result<LuaLib> {
            Ok(LuaLib)
        }

    } else {
        // TODO
    }

}

lua_api! {
    fn luaL_newstate() -> *mut lua_State;
    fn luaL_openlibs(L: *mut lua_State);
    fn luaL_loadbuffer(L: *mut lua_State, buff: *const u8, sz: usize, name: *const c_char) -> c_int;
    fn lua_call(L: *mut lua_State, nargs: c_int, nresults: c_int);
    fn lua_pcall(L: *mut lua_State, nargs: c_int, nresults: c_int, errfunc: c_int) -> c_int;
    fn lua_gettop(L: *mut lua_State) -> c_int;
    fn lua_settop(L: *mut lua_State, idx: c_int);
    fn lua_type(L: *mut lua_State, idx: c_int) -> c_int;
    fn lua_pushnumber(L: *mut lua_State, n: f64);
    fn lua_pushlstring(L: *mut lua_State, s: *const u8, n: isize);
    fn lua_pushnil(L: *mut lua_State);
    fn lua_pushvalue(L: *mut lua_State, idx: c_int);
    fn lua_tointeger(L: *mut lua_State, idx: c_int) -> isize;
    fn lua_tolstring(L: *mut lua_State, idx: c_int, len: *mut usize) -> *const c_char;
    fn lua_toboolean(L: *mut lua_State, idx: c_int) -> c_int;
    fn lua_createtable(L: *mut lua_State, narr: c_int, nrec: c_int);
    fn lua_getfield(L: *mut lua_State, idx: c_int, k: *const c_char);
    fn lua_rawgeti(L: *mut lua_State, idx: c_int, n: c_int);
    fn lua_setfield(L: *mut lua_State, idx: c_int, k: *const c_char);
    fn lua_rawseti(L: *mut lua_State, idx: c_int, n: c_int);
    fn lua_close(L: *mut lua_State);
}

const LUA_TNIL: c_int = 0;
const LUA_TTABLE: c_int = 5;
const LUA_GLOBALSINDEX: c_int = -10002;

pub struct Lua {
    L: *mut lua_State,
    base: usize,
    #[cfg(feature="host-Lua")]
    lib: LuaLib, // zero sized
    #[cfg(not(feature="host-Lua"))]
    lib: Box<LuaLib> // boxed to keep LangState small
}

bump::vla_struct! {
    struct LuaFunc {
        load: Unalign<IRef<[u8]>>,
        template: Unalign<IRef<[u8]>>,
        no: u8
    } out: [u8; |lf| lf.no as usize]
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
#[repr(C)]
struct LuaCall {
    load: IRef<[u8]>,
    template: IRef<[u8]>,
    ret: IRef<[ObjRef]>
}

// execute a lua function call.
// before begin_emit:
//   FX LOVV (args: CARG LOP_VALUE) (func: KREF IRef<LuaCall>)
// after begin_emit:
//   FX LOVX (args unchanged) (func: jump table index)
const LOP_CALL: u8 = 0;

// get a call result.
// VAL LOVX (call: LOP_CALL) idx
const LOP_RES: u8 = 1;

// create a lua value from ir value(s).
// scalar (TPRI) -> value is an ir value.
// tensor (TTEN) -> value is a CARG list.
// LSV LOVV value (type: KREF TPRI|TTEN)
const LOP_VALUE: u8 = 2;

/* ---- Parsing ------------------------------------------------------------- */

struct ParseState {
    need: BitmapWord,
    template: BumpVec<u8>,
    inputs: BumpVec<ObjRef<EXPR>>,
    lf: BumpRef<LuaFunc>
}

fn parse_luavalue(pcx: &mut Pcx, ps: &mut ParseState) -> compile::Result {
    match pcx.data.token {
        Token::LCurly => {
            next(pcx)?;
            ps.template.push(&mut pcx.tmp, b'{');
            while pcx.data.token != Token::RCurly {
                if check(pcx, Token::LBracket)? {
                    ps.template.push(&mut pcx.tmp, b'[');
                    parse_luavalue(pcx, ps)?;
                    ps.template.push(&mut pcx.tmp, b']');
                    ps.template.push(&mut pcx.tmp, b'=');
                    consume(pcx, Token::RBracket)?;
                    consume(pcx, Token::Eq)?;
                }
                parse_luavalue(pcx, ps)?;
                if !check(pcx, Token::Comma)? { break }
                ps.template.push(&mut pcx.tmp, b',');
            }
            consume(pcx, Token::RCurly)?;
            ps.template.push(&mut pcx.tmp, b'}');
        },
        Token::Out => {
            next(pcx)?;
            let idx = match pcx.data.token {
                Token::LParen => {
                    next(pcx)?;
                    let idx = consume(pcx, Token::Int)? as usize;
                    if !ps.need.test(idx) {
                        // TODO: report error (don't want this out parameter)
                        todo!();
                    }
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
            ps.need.clear(idx);
            // at least one dimension is required
            consume(pcx, Token::LBracket)?;
            let base = pcx.tmp.end();
            loop {
                let size = parse_expr(pcx)?;
                pcx.tmp.push(size);
                if !check(pcx, Token::Comma)? || pcx.data.token == Token::RBracket { break }
            }
            consume(pcx, Token::RBracket)?;
            let shape: &[ObjRef<EXPR>] = &pcx.tmp[base.cast_up()..];
            let tv = pcx.objs.push(TVAR::new());
            let ty = pcx.objs.push(TTEN::new(shape.len() as _, tv.erase()));
            let new = pcx.objs.push_args::<NEW>(NEW::new(ty.erase()), shape);
            pcx.tmp.truncate(base);
            let input = ps.inputs.len();
            pcx.perm[ps.lf].out[idx] = !input as _;
            ps.inputs.push(&mut pcx.tmp, new.cast());
            ps.template.push(&mut pcx.tmp, 0x80 | input as u8);
        },
        _ => {
            let input = parse_expr(pcx)?;
            let idx = ps.inputs.len();
            ps.inputs.push(&mut pcx.tmp, input);
            ps.template.push(&mut pcx.tmp, 0x80 | idx as u8);
        }
    }
    Ok(())
}

fn parse_call(pcx: &mut Pcx, ps: &mut ParseState) -> compile::Result {
    consume(pcx, Token::LBracket)?;
    require(pcx, Token::Literal)?;
    let mut load: IRef<[u8]> = zerocopy::transmute!(pcx.data.tdata);
    next(pcx)?;
    if check(pcx, Token::Colon)? {
        // TODO: this needs some escaping but that's a problem for another day.
        let name: IRef<[u8]> = zerocopy::transmute!(consume(pcx, Token::Literal)?);
        let base = pcx.tmp.end();
        pcx.tmp.write(b"return require(\"");
        pcx.tmp.write(pcx.intern.get_slice(load));
        pcx.tmp.write(b"\")[\"");
        pcx.tmp.write(pcx.intern.get_slice(name));
        pcx.tmp.write(b"\"]");
        load = pcx.intern.intern(&pcx.tmp[base..]);
        pcx.tmp.truncate(base);
    }
    pcx.perm[ps.lf].load.set(load);
    consume(pcx, Token::RBracket)?;
    consume(pcx, Token::LParen)?;
    while pcx.data.token != Token::RParen {
        if !ps.template.is_empty() {
            // we allow trailing commas but lua doesn't, so insert comma here instead.
            ps.template.push(&mut pcx.tmp, b',');
        }
        parse_luavalue(pcx, ps)?;
        if !check(pcx, Token::Comma)? { break }
    }
    consume(pcx, Token::RParen)?;
    Ok(())
}

fn collect_call(pcx: &mut Pcx, ps: &ParseState, n: usize) -> ObjRef<CALLX> {
    let lf = &mut pcx.perm[ps.lf];
    lf.template.set(pcx.intern.intern(ps.template.as_slice(&pcx.tmp)));
    // all remaining outputs are return values
    for (i,j) in ps.need.ones().enumerate() {
        lf.out[j] = i as _;
    }
    // if there were any explicit out parameters, create a type annotation
    let inputs = ps.inputs.as_slice(&pcx.tmp);
    let ann = if ps.need.is_empty() && n == 1 {
        pcx.objs[inputs[!lf.out[0] as usize]].ann
    } else if ps.need.popcount() < n as _ {
        let (ann, tup) = pcx.objs.push_reserve_dst::<TTUP>(n);
        tup.op = Obj::TTUP;
        tup.elems.fill(ObjRef::NIL);
        for (i,&o) in lf.out.iter().enumerate() {
            if (o as i8) < 0 {
                pcx.objs[ann].elems[i] = pcx.objs[inputs[!o as usize]].ann;
            }
        }
        ann.erase()
    } else {
        ObjRef::NIL
    };
    pcx.objs.push_args(CALLX::new(Lang::Lua as _, ann, zerocopy::transmute!(ps.lf)), inputs)
}

/* ---- Lowering ------------------------------------------------------------ */

fn lower_call(lcx: &mut CLcx, obj: ObjRef<CALLX>, func: &Func, inputs: &[InsId]) -> InsId {
    let callx = &lcx.objs[obj];
    let mut args = func.code.push(Ins::NOP(Type::LSV));
    for (&i,&o) in zip(inputs, &callx.inputs).rev() {
        let ann = lcx.objs[o].ann;
        let ty = func.code.push(Ins::KREF(zerocopy::transmute!(ann)));
        let value = match lcx.objs.get(ann) {
            ObjectRef::TPRI(_) => i,
            ObjectRef::TTEN(&TTEN { dim, .. }) => {
                let mut values = func.code.push(Ins::NOP(Type::LSV));
                for j in (0..dim+1).rev() {
                    values = func.code.push(Ins::CARG(values, i + j as isize));
                }
                values
            },
            _ => unreachable!()
        };
        let value = func.code.push(Ins::LOVV(Type::LSV, value, ty, LangOp::Lua(LOP_VALUE)));
        args = func.code.push(Ins::CARG(args, value));
    }
    let call = func.code.push(Ins::NOP_FX);
    let out = reserve(func, decomposition_size(&lcx.objs, callx.ann));
    let outann = match lcx.objs.get(callx.ann) {
        ObjectRef::TTUP(TTUP { elems, .. }) => elems,
        _ => &[callx.ann],
    };
    let lf: BumpRef<LuaFunc> = zerocopy::transmute!(callx.func);
    let lf: &LuaFunc = &lcx.perm[lf];
    let base = lcx.tmp.end();
    let mut curout = out;
    for (i,(&o,&a)) in zip(&lf.out, outann).enumerate() {
        let base = lcx.tmp.end();
        let deco = decomposition(&lcx.objs, a, &mut lcx.tmp);
        if (o as i8) < 0 {
            let mut input = inputs[!o as usize];
            for &ty in &*deco {
                func.code.set(curout, Ins::MOVF(ty, input, call));
                curout += 1;
                input += 1;
            }
            lcx.tmp.truncate(base);
        } else {
            for &ty in &*deco {
                func.code.set(curout, Ins::LOVX(ty, call, i as _, LangOp::Lua(LOP_RES)));
                curout += 1;
            }
            lcx.tmp.truncate(base);
            lcx.tmp.push(a);
        }
    }
    let ret = lcx.intern.intern(&lcx.tmp[base.cast_up()..]);
    let cref = lcx.intern.intern(&LuaCall { load: lf.load.get(), template: lf.template.get(), ret });
    let cref = func.code.push(Ins::KREF(zerocopy::transmute!(cref)));
    func.code.set(call, Ins::LOVV(Type::FX, args, cref, LangOp::Lua(LOP_CALL)));
    lcx.tmp.truncate(base);
    out
}

/* ---- Emitting ------------------------------------------------------------ */

// stack layout:
const STACK_TENSORLIB: c_int = 1; // require("tensor")
const STACK_FUNCS: c_int = 2;     // table containing all jump table functions

unsafe fn toabsidx(lib: &LuaLib, L: *mut lua_State, idx: c_int) -> c_int {
    if idx < 0 {
        lib.lua_gettop(L) + idx + 1
    } else {
        idx
    }
}

unsafe fn pushctype(objs: &Objects, lib: &LuaLib, L: *mut lua_State, tab: c_int, idx: ObjRef) {
    lib.lua_rawgeti(L, tab, {let idx: u32 = zerocopy::transmute!(idx); idx as _});
    if lib.lua_type(L, -1) != LUA_TNIL {
        return;
    }
    lib.lua_settop(L, -2);
    match objs.get(idx) {
        ObjectRef::TPRI(&TPRI { ty, .. }) => {
            lib.lua_getfield(L, STACK_TENSORLIB, c"scalar_ctype".as_ptr());
            lib.lua_pushnumber(L, ty as _);
            lib.lua_call(L, 1, 1);
        },
        ObjectRef::TTEN(&TTEN { elem, dim: 1, .. }) if objs[elem].op == Obj::TPRI => {
            lib.lua_getfield(L, STACK_TENSORLIB, c"vector_ctype".as_ptr());
            pushctype(objs, lib, L, tab, elem);
            lib.lua_call(L, 1, 1);
        },
        ObjectRef::TTEN(&TTEN { elem, dim, .. }) => {
            lib.lua_getfield(L, STACK_TENSORLIB, c"tensor_ctype".as_ptr());
            pushctype(objs, lib, L, tab, elem);
            lib.lua_pushnumber(L, dim as _);
            lib.lua_call(L, 2, 1);
        },
        _ => unreachable!()
    }
    lib.lua_pushvalue(L, -1);
    lib.lua_rawseti(L, tab, {let idx: u32 = zerocopy::transmute!(idx); idx as _});
}

unsafe fn makejumptab(ccx: &mut Ccx, lib: &LuaLib, L: *mut lua_State) -> compile::Result<usize> {
    let mut jump = 0;
    lib.lua_createtable(L, 0, 0);
    let ctidx = toabsidx(lib, L, -1);
    for func in &ccx.ir.funcs.raw {
        for (id, ins) in func.code.pairs() {
            if ins.opcode() == Opcode::LOVV && ins.decode_L() == LangOp::Lua(LOP_CALL) {
                let (mut args, cref, _) = ins.decode_LOVV();
                lib.lua_createtable(L, 0, 4); // {load,template,inputs,returns}
                lib.lua_createtable(L, 0, 0); // inputs
                lib.lua_createtable(L, 0, 0); // insid -> input idx
                let mut n_in = 0;
                while func.code.at(args).opcode() != Opcode::NOP {
                    let (next, value) = func.code.at(args).decode_CARG();
                    lib.lua_rawgeti(L, -1, {let idx: u16 = zerocopy::transmute!(value); idx as _});
                    if lib.lua_type(L, -1) == LUA_TNIL {
                        // TODO: handle constants (constant scalars) here specially. they don't
                        // need a memory write, just put the value in the table and hardcode
                        // it in the generated lua code.
                        lib.lua_settop(L, -2);
                        lib.lua_createtable(L, 0, 0);
                        let (_, tref, _) = func.code.at(value).decode_LOVV();
                        let tobj: ObjRef = zerocopy::transmute!(func.code.at(tref).bc());
                        pushctype(&ccx.objs, lib, L, ctidx, tobj);
                        lib.lua_setfield(L, -2, c"ctype".as_ptr());
                        n_in += 1;
                        lib.lua_rawseti(L, -3, n_in as _);
                        lib.lua_pushnumber(L, n_in as _);
                    }
                    lib.lua_rawseti(L, -3, {let idx: u16 = zerocopy::transmute!(value); idx as _ });
                    args = next;
                }
                lib.lua_settop(L, -2);
                lib.lua_setfield(L, -2, c"inputs".as_ptr());
                let cref: IRef<LuaCall> = zerocopy::transmute!(func.code.at(cref).bc());
                let call = &ccx.intern[cref];
                lib.lua_createtable(L, 0, 0); // returns
                for (i,&ret) in ccx.intern.get_slice(call.ret).iter().enumerate() {
                    lib.lua_createtable(L, 0, 0);
                    pushctype(&ccx.objs, lib, L, ctidx, ret);
                    lib.lua_setfield(L, -2, c"ctype".as_ptr());
                    lib.lua_pushnumber(L, {let ret: u32 = zerocopy::transmute!(ret); ret as _});
                    lib.lua_setfield(L, -2, c"ann".as_ptr());
                    lib.lua_rawseti(L, -2, (i+1) as _);
                }
                lib.lua_setfield(L, -2, c"returns".as_ptr());
                let load = ccx.intern.get_slice(call.load);
                lib.lua_pushlstring(L, load.as_ptr(), load.len() as _);
                lib.lua_setfield(L, -2, c"load".as_ptr());
                let template = ccx.intern.get_slice(call.template);
                lib.lua_pushlstring(L, template.as_ptr(), template.len() as _);
                lib.lua_setfield(L, -2, c"template".as_ptr());
                jump += 1;
                lib.lua_rawseti(L, STACK_FUNCS, jump as _);
                func.code.set(id, ins.set_b(jump as _).set_opcode(Opcode::LOVX));
            }
        }
    }
    lib.luaL_loadbuffer(L, CALL_LUA.as_ptr(), CALL_LUA.len(), c"fhk:call".as_ptr());
    lib.lua_pushvalue(L, STACK_FUNCS);
    lib.lua_pushnumber(L, fhk_swap as usize as _);
    lib.lua_call(L, 2, 2);
    if lib.lua_type(L, -2) == LUA_TNIL {
        // TODO: return error message
        todo!()
    }
    let mem = lib.lua_tointeger(L, -2);
    lib.lua_settop(L, -3);
    Ok(mem as _)
}

fn emitcall(ecx: &mut Ecx, id: InsId) -> InsValue {
    let emit = &mut *ecx.data;
    let (mut args, jump, _) = emit.code[id].decode_LOVX();
    let &mut Lua { L, ref lib, base } = emit.lang.Lua();
    unsafe {
        lib.lua_rawgeti(L, STACK_FUNCS, jump as _);
        lib.lua_getfield(L, -1, c"inputs".as_ptr());
    }
    let base = emit.fb.ins().iconst(irt2cl(Type::PTR), base as i64);
    let mut idx = 0;
    while emit.code[args].opcode() != Opcode::NOP {
        idx += 1;
        let (next, value) = emit.code[args].decode_CARG();
        let ofs = unsafe {
            lib.lua_rawgeti(L, -1, idx);
            if lib.lua_type(L, -1) == LUA_TTABLE {
                lib.lua_getfield(L, -1, c"offset".as_ptr());
                let ofs = lib.lua_tointeger(L, -1);
                lib.lua_settop(L, -3);
                Some(ofs as usize)
            } else {
                lib.lua_settop(L, -2);
                None
            }
        };
        if let Some(mut ofs) = ofs {
            let (value, _, _) = emit.code[value].decode_LOVV();
            if emit.code[value].opcode() == Opcode::CARG {
                let mut vlist = value;
                while emit.code[vlist].opcode() != Opcode::NOP {
                    let (next, value) = emit.code[vlist].decode_CARG();
                    emit.fb.ins().store(MemFlags::trusted(), emit.values[value].value(), base,
                        ofs as i32);
                    ofs += emit.code[value].type_().size();
                    vlist = next;
                }
            } else {
                emit.fb.ins().store(MemFlags::trusted(), emit.values[value].value(), base,
                    ofs as i32);
            }
        }
        args = next;
    }
    let swap = emit.fb.importsupp(&ecx.ir, SuppFunc::SWAP);
    let jump = emit.fb.ins().iconst(irt2cl(Type::I64), jump as i64);
    emit.fb.ins().call(swap, &[base, jump]); // base+0 = coro
    unsafe { lib.lua_getfield(L, -2, c"returns".as_ptr()); }
    let ret = emit.bump.align_for::<InsValue>();
    let retv = ret.end();
    let mut idx = 0;
    loop {
        idx += 1;
        let (mut ofs, ann) = unsafe {
            lib.lua_rawgeti(L, -1, idx as _);
            if lib.lua_type(L, -1) == LUA_TNIL { break }
            lib.lua_getfield(L, -1, c"offset".as_ptr());
            let ofs = lib.lua_tointeger(L, -1);
            lib.lua_getfield(L, -2, c"ann".as_ptr());
            let ann = lib.lua_tointeger(L, -1);
            lib.lua_settop(L, -4);
            (ofs as usize, ann as u32)
        };
        let tbase = ecx.tmp.end();
        for &ty in &*decomposition(&ecx.objs, zerocopy::transmute!(ann), &mut ecx.tmp) {
            let v = emit.fb.ins().load(irt2cl(ty), MemFlags::trusted(), base, ofs as i32);
            ret.push(InsValue::from_value(v));
            ofs += ty.size();
        }
        ecx.tmp.truncate(tbase);
    }
    unsafe {
        // pop nil, returns, inputs, func
        lib.lua_settop(L, -5);
    }
    InsValue { raw: zerocopy::transmute!(retv) }
}

fn emitres(ecx: &mut Ecx, id: InsId) -> InsValue {
    let emit = &*ecx.data;
    let (call, idx, _) = emit.code[id].decode_LOVX();
    let res: BumpRef<InsValue> = zerocopy::transmute!(emit.values[call].raw);
    emit.bump[res.add_size(idx as _)]
}

/* ---- Runtime ------------------------------------------------------------- */

struct InitCtx {
    L: *mut lua_State,
    base: usize,
    // TODO: lua_call and lua_close pointers go here when host-Lua is not enabled
}

#[cold]
unsafe extern "C" fn fhk_lua_swap_exit(coro: usize, errmsg: *const c_char) -> i64 {
    let inst = &mut *fhk_swap_instance(coro);
    inst.host.set_error(CStr::from_ptr(errmsg).to_bytes());
    fhk_swap_exit(coro)
}

unsafe extern "C" fn run(ctx: *mut ()) -> ! {
    let init = &*(ctx as *const InitCtx);
    let L = init.L;
    let mem = init.base;
    #[cfg(feature="host-Lua")]
    let lua_call = host_liblua::lua_call;
    #[cfg(not(feature="host-Lua"))]
    let lua_call = todo!();
    lua_call(L, 1, 0);
    loop { fhk_swap(mem, 0); }
}

unsafe fn init(lua: &Lua, stack: usize) {
    let &Lua { L, ref lib, base } = lua;
    lib.lua_settop(L, 0);
    lib.lua_getfield(L, LUA_GLOBALSINDEX, c"__fhk_run".as_ptr());
    lib.lua_pushnumber(L, fhk_lua_swap_exit as usize as _);
    let mut ctx = InitCtx { L, base };
    fhk_swap_init(&SwapInit {
        coro: base,
        stack,
        func: run,
        ctx: &mut ctx as *mut _ as *mut _,
        #[cfg(windows)]
        bottom: stack - CORO_STACK
    })
}

/* ---- Finalization -------------------------------------------------------- */

struct LuaFinalizer {
    L: *mut lua_State,
    base: usize,
    _stack: Mmap
    // TODO: when NOT compiling with host-Lua, this also needs the dl handle and lua_close pointer
}

impl Drop for LuaFinalizer {
    fn drop(&mut self) {
        #[cfg(feature="host-Lua")]
        let lua_close = host_liblua::lua_close;
        #[cfg(not(feature="host-Lua"))]
        let lua_close = todo!();
        unsafe {
            fhk_swap(self.base, 0);
            lua_close(self.L);
        }
        // TODO: when NOT compiling with host-Lua, also close the dlhandle
    }
}

/* -------------------------------------------------------------------------- */

impl Language for Lua {

    fn parse(pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALLX>> {
        let (lf, lfp) = pcx.perm.reserve_dst::<LuaFunc>(n);
        lfp.no = n as _;
        let mut ps = ParseState {
            need: Default::default(),
            template: Default::default(),
            inputs: Default::default(),
            lf
        };
        ps.need.set_range(0..n);
        let base = pcx.tmp.end();
        parse_call(pcx, &mut ps)?;
        let obj = collect_call(pcx, &ps, n);
        pcx.tmp.truncate(base);
        Ok(obj)
    }

    fn lower(lcx: &mut CLcx, obj: ObjRef<CALLX>, func: &Func, inputs: &[InsId]) -> InsId {
        lower_call(lcx, obj, func, inputs)
    }

    fn begin_emit(ccx: &mut Ccx) -> compile::Result<Self> {
        let lib = open_liblua(ccx)?;
        let (L, base) = unsafe {
            let L = lib.luaL_newstate();
            lib.luaL_openlibs(L);
            lib.lua_settop(L, 0);
            lib.luaL_loadbuffer(L, TENSOR_LUA.as_ptr(), TENSOR_LUA.len(), c"fhk:tensor".as_ptr());
            lib.lua_call(L, 0, 1); // STACK_TENSORLIB
            lib.lua_createtable(L, 0, 0); // STACK_FUNCS
            match makejumptab(ccx, &lib, L) {
                Ok(base) => (L, base),
                Err(()) => {
                    lib.lua_close(L);
                    return Err(());
                }
            }
        };
        Ok(Lua { L, lib, base })
    }

    fn emit(ecx: &mut Ecx, id: InsId, lop: u8) -> compile::Result<InsValue> {
        Ok(match lop {
            LOP_CALL => emitcall(ecx, id),
            LOP_RES  => emitres(ecx, id),
            _ => unreachable!()
        })
    }

    fn finish_emit(self, ccx: &mut Ccx<Emit>) -> compile::Result {
        let stack = match Mmap::new(CORO_STACK, Prot::Read | Prot::Write) {
            Some(stack) => stack,
            None => {
                // TODO: report error
                todo!()
            }
        };
        unsafe { init(&self, stack.base() as usize + CORO_STACK); }
        ccx.fin.push(LuaFinalizer {
            L: self.L,
            base: self.base,
            _stack: stack
        });
        Ok(())
    }

}
