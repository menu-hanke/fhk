//! Source -> Graph.

use core::cmp::max;
use core::ops::Range;

use enumset::{enum_set, EnumSet};

use crate::bump::BumpRef;
use crate::compile;
use crate::intern::IRef;
use crate::intrinsics::Intrinsic;
use crate::lang::Lang;
use crate::lex::Token;
use crate::obj::{cast_args, Obj, ObjRef, CALLN, CALLX, DIM, EXPR, GET, KINT, LOAD, MOD, TPRI, TTEN, TUPLE, VAR, VGET, VSET};
use crate::parser::{check, consume, langerr, next, redeferr, require, save, syntaxerr, tokenerr, Binding, Namespace, ParenCounter, Pcx, SyntaxError};
use crate::typing::Primitive;

pub const TOPLEVEL_KEYWORDS: EnumSet<Token> = enum_set!(
    Token::Model | Token::Table | Token::Func | Token::Macro | Token::Eof
);

fn parse_name(pcx: &mut Pcx) -> compile::Result<IRef<[u8]>> {
    let base = pcx.tmp.end();
    save(pcx);
    if check(pcx, Token::Scope)? { save(pcx); }
    consume(pcx, Token::Ident)?;
    if pcx.data.token == Token::Apostrophe {
        save(pcx);
        next(pcx)?;
        if (Token::LParen | Token::LBracket | Token::LCurly).contains(pcx.data.token) {
            let mut parens = ParenCounter::default();
            parens.token(pcx.data.token);
            loop {
                next(pcx)?;
                parens.token(pcx.data.token);
                if parens.balanced() { break; }
                save(pcx);
            }
        } else {
            save(pcx);
        }
        next(pcx)?; // skip subscript token or closing parenthesis
    }
    let name = pcx.intern.intern(&pcx.tmp[base..]);
    pcx.tmp.truncate(base);
    Ok(name)
}

fn parse_vref(pcx: &mut Pcx) -> compile::Result<ObjRef<VAR>> {
    let mut name = parse_name(pcx)?;
    let table = if check(pcx, Token::Dot)? {
        let tab = pcx.objs.tab(name).get_or_create();
        name = parse_name(pcx)?;
        tab
    } else {
        pcx.data.tab
    };
    Ok(pcx.objs.var(table, name).get_or_create())
}

fn builtincall(pcx: &mut Pcx, name: IRef<[u8]>, base: BumpRef<u8>) -> Option<ObjRef<EXPR>> {
    const IDENT: u8 = Token::Ident as _;
    const APOSTROPHE: u8 = Token::Apostrophe as _;
    let name @ [IDENT, _, _, _, _, rest @ .. ] = pcx.intern.get_slice(name.cast())
        else { return None };
    let stem: [u8; 4] = name[1..5].try_into().unwrap();
    let stem: &[u8] = pcx.intern.get_slice(zerocopy::transmute!(stem));
    let args: &[ObjRef<EXPR>] = &pcx.tmp[base.cast_up()..];
    if let Some(intrin) = Intrinsic::from_func(stem) {
        return match rest.is_empty() {
            true => Some(pcx.objs.push_args::<CALLN>(CALLN::new(intrin as _, ObjRef::NIL), args)
                .cast()),
            false => None
        };
    }
    if stem == b"load" {
        let tail @ [APOSTROPHE, IDENT, _, _, _, _] = rest else { return None };
        let ty: [u8; 4] = tail[2..].try_into().unwrap();
        let pri = pcx.objs.push(TPRI::new(Primitive::from_name(
                    pcx.intern.get_slice(zerocopy::transmute!(ty)))? as u8)).erase();
        let ann = match args.len() {
            1 => pri,
            n => pcx.objs.push(TTEN::new(n as u8 - 1, pri)).erase()
        };
        // TODO: allow some special syntax eg. `_` here to elide the size when returning
        // a full table variable.
        return Some(pcx.objs.push_args::<LOAD>(LOAD::new(ann, args[0]), &args[1..]).cast());
    }
    None
}

fn parse_call(pcx: &mut Pcx, name: IRef<[u8]>) -> compile::Result<ObjRef<EXPR>> {
    next(pcx)?; // skip '('
    let base = pcx.tmp.end();
    while pcx.data.token != Token::RParen {
        let param = parse_expr(pcx)?;
        pcx.tmp.push(param);
        if !check(pcx, Token::Comma)? { break }
    }
    consume(pcx, Token::RParen)?;
    let expr = match builtincall(pcx, name, base) {
        Some(expr) => expr,
        None => todo!("user function call")
    };
    pcx.tmp.truncate(base);
    Ok(expr)
}

fn parse_vget(pcx: &mut Pcx, var: ObjRef<VAR>) -> compile::Result<ObjRef<EXPR>> {
    if pcx.data.token == Token::LBracket {
        todo!("vget with index")
    }
    Ok(pcx.objs.push(VGET::new(ObjRef::NIL, var)).cast())
}

fn parse_callx(pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALLX>> {
    require(pcx, Token::Ident)?;
    let Some(lang) = Lang::from_name(&pcx.intern.get_slice(zerocopy::transmute!(pcx.data.tdata)))
        else { return langerr(pcx) };
    next(pcx)?; // skip name
    lang.parse_callx(pcx, n)
}

// ORDER BINOP
const PRIORITY: &'static [(u8, u8)] = &[
    (1,1), // or
    (2,2), // and
    (6,6),(6,6), // add sub
    (7,7),(7,7), // mul div
    (10,9), // pow
    (3,3),(3,3),(3,3),(3,3),(3,3),(3,3), // eq ne lt le gt ge
];

const UNARY_PRIORITY: u8 = 8;

fn parse_value(pcx: &mut Pcx) -> compile::Result<ObjRef<EXPR>> {
    match pcx.data.token {
        Token::Scope | Token::Ident => {
            let name = parse_name(pcx)?;
            match pcx.data.token {
                Token::LParen => parse_call(pcx, name),
                Token::Dot => {
                    next(pcx)?;
                    let tab = pcx.objs.tab(name).get_or_create();
                    let name = parse_name(pcx)?;
                    let var = pcx.objs.var(tab, name).get_or_create();
                    parse_vget(pcx, var)
                },
                _ => match pcx.data.bindings.iter().find(|b| b.name == name) {
                    Some(v) => Ok(v.value),
                    None => {
                        let var = pcx.objs.var(pcx.data.tab, name).get_or_create();
                        parse_vget(pcx, var)
                    }
                }
            }
        },
        Token::LParen => {
            next(pcx)?;
            let node = parse_expr(pcx)?;
            consume(pcx, Token::RParen)?;
            Ok(node)
        },
        Token::LBracket => {
            todo!("concat")
        },
        Token::Let => {
            next(pcx)?;
            let base = pcx.data.bindings.len();
            let name = parse_name(pcx)?;
            match pcx.data.token {
                Token::Eq => {
                    next(pcx)?;
                    let value = parse_expr(pcx)?;
                    pcx.data.bindings.push(Binding { name, value });
                },
                Token::Comma => {
                    pcx.data.bindings.push(Binding { name, value: ObjRef::NIL.cast() });
                    let mut n = 1;
                    while check(pcx, Token::Comma)? {
                        let name = parse_name(pcx)?;
                        pcx.data.bindings.push(Binding { name, value: ObjRef::NIL.cast() });
                        n += 1;
                    }
                    consume(pcx, Token::Eq)?;
                    consume(pcx, Token::Call)?;
                    let call = parse_callx(pcx, n)?;
                    for i in 0..n {
                        pcx.data.bindings[base+i].value = pcx.objs.push(
                            GET::new(i as _, ObjRef::NIL, call.cast())
                        ).cast();
                    }
                },
                _ => return tokenerr(pcx, Token::Eq | Token::Comma)
            }
            consume(pcx, Token::In)?;
            let value = parse_expr(pcx)?;
            pcx.data.bindings.truncate(base);
            Ok(value)
        },
        // Token::Minus | Token::Not => {
        //     let tok = pcx.data.token;
        //     next(pcx)?;
        //     let value = parse_binop(pcx, UNARY_PRIORITY)?;
        //     let (intr, ty) = match tok {
        //         Token::Minus => (Intrinsic::UNM, Type::INFER),
        //         Token::Not => (Intrinsic::NOT, Type::scalar(Primitive::B1)),
        //         _ => unreachable!()
        //     };
        //     Ok(pcx.objs.push(&INTR {
        //         op: Operator::INTR as _,
        //         ty,
        //         func: intr as _,
        //         n: 0,
        //         args: [value]
        //     }).erase())
        // },
        Token::Int | Token::Int64 | Token::Fp64 | Token::Literal => {
            let mut o = KINT::new(ObjRef::NIL, pcx.data.tdata as _);
            match pcx.data.token {
                Token::Int64   => o.op = Obj::KINT64,
                Token::Fp64    => o.op = Obj::KFP64,
                Token::Literal => o.op = Obj::KSTR,
                _ => {}
            }
            next(pcx)?;
            Ok(pcx.objs.push(o).cast())
        }
        Token::Call => { next(pcx)?; Ok(parse_callx(pcx, 1)?.cast()) },
        Token::True => { next(pcx)?; Ok(ObjRef::TRUE.cast()) },
        Token::False => { next(pcx)?; Ok(ObjRef::FALSE.cast()) },
        _ => syntaxerr(pcx, SyntaxError::ExpectedValue)
    }
}

fn parse_binop(pcx: &mut Pcx, limit: u8) -> compile::Result<ObjRef<EXPR>> {
    let mut lhs = parse_value(pcx)?;
    while pcx.data.token.is_binop() {
        let mut op = pcx.data.token;
        let (left, right) = PRIORITY[op as usize - Token::Or as usize];
        if left <= limit { break; }
        next(pcx)?;
        let mut rhs = parse_binop(pcx, right)?;
        if (Token::Ge | Token::Gt).contains(op) {
            // Ge => Le, Gt => Lt
            op = unsafe { core::mem::transmute(op as u8 - 2) };
            (lhs, rhs) = (rhs, lhs);
        }
        lhs = pcx.objs.push_args::<CALLN>(
            CALLN::new(Intrinsic::OR as u8 + (op as u8 - Token::Or as u8), ObjRef::NIL),
            &[lhs, rhs]
        ).cast();
    }
    Ok(lhs)
}

fn parse_table(pcx: &mut Pcx) -> compile::Result {
    next(pcx)?; // skip `table`
    let name = parse_name(pcx)?;
    let tab = pcx.objs.tab(name).get_or_create();
    if !pcx.objs[tab].shape.is_nil() {
        return redeferr(pcx, Namespace::Table, name);
    }
    let base = pcx.tmp.end();
    if check(pcx, Token::LBracket)? {
        pcx.data.tab = ObjRef::GLOBAL;
        while pcx.data.token != Token::RBracket {
            let value = parse_expr(pcx)?;
            pcx.tmp.push(value);
            if pcx.data.token == Token::Comma {
                next(pcx)?;
            } else {
                consume(pcx, Token::RBracket)?;
                break;
            }
        }
    }
    pcx.objs[tab].shape = pcx.objs.push_args::<TUPLE>(
        TUPLE::new(ObjRef::NIL),
        &pcx.tmp[base.cast_up()..]
    ).cast();
    pcx.tmp.truncate(base);
    Ok(())
}

fn deconstruct(pcx: &mut Pcx, value: ObjRef<EXPR>, num: usize) {
    match num {
        0 => {},
        1 => {
            pcx.tmp.push(value);
        },
        _ => for i in 0..num as u8 {
            pcx.tmp.push(pcx.objs.push(GET::new(i, ObjRef::NIL, value)));
        }
    }
}

fn parse_model_def(pcx: &mut Pcx) -> compile::Result {
    let base = pcx.tmp.end();
    loop {
        let var = parse_vref(pcx)?;
        if check(pcx, Token::LBracket)? {
            todo!(); // TODO: parse subset
            consume(pcx, Token::RBracket)?;
        }
        pcx.tmp.push(pcx.objs.push(VSET::new(var, ObjRef::NIL.cast())));
        match pcx.data.token {
            Token::Comma => { next(pcx)?; todo!("handle multiple outputs"); continue; },
            Token::Eq    => { next(pcx)?; break },
            _            => return tokenerr(pcx, Token::Comma | Token::Eq)
        }
    }
    let deco_base = pcx.tmp.align_for::<ObjRef<EXPR>>().end();
    let vset_base = base.cast_up::<ObjRef<VSET>>();
    let num = deco_base.size_index() - vset_base.size_index();
    let value = parse_expr(pcx)?;
    deconstruct(pcx, value, num);
    for i in (0..num as isize).rev() {
        let vset = pcx.tmp[vset_base.add_size(i)];
        pcx.objs[vset].value = pcx.tmp[deco_base.add_size(i)]
    }
    let guard = match check(pcx, Token::Where)? {
        true  => parse_expr(pcx)?,
        false => ObjRef::NIL.cast()
    };
    pcx.objs.push_args::<MOD>(
        MOD::new(IRef::EMPTY, pcx.data.tab, guard),
        cast_args(&pcx.tmp[vset_base..deco_base.cast::<ObjRef<VSET>>()])
    );
    pcx.tmp.truncate(base);
    Ok(())
}

fn parse_model(pcx: &mut Pcx) -> compile::Result {
    next(pcx)?; // skip `model`
    let table = parse_name(pcx)?;
    pcx.data.tab = pcx.objs.tab(table).get_or_create();
    debug_assert!(pcx.data.bindings.is_empty());
    if check(pcx, Token::LBracket)? {
        let mut axis = -1isize;
        while pcx.data.token != Token::RBracket {
            axis += 1;
            if pcx.data.token == Token::Colon {
                next(pcx)?;
                continue;
            }
            let name = parse_name(pcx)?;
            let value = pcx.objs.push(DIM::new(axis as _, ObjRef::NIL)).cast();
            pcx.data.bindings.push(Binding { name, value });
            if pcx.data.token == Token::Comma {
                next(pcx)?;
            } else {
                consume(pcx, Token::RBracket)?;
                break;
            }
        }
    }
    if check(pcx, Token::LCurly)? {
        while pcx.data.token != Token::RCurly {
            parse_model_def(pcx)?;
        }
        next(pcx)?;
    } else {
        parse_model_def(pcx)?;
    }
    pcx.data.bindings.clear();
    Ok(())
}

fn parse_func(pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_macro_body_rec(
    pcx: &mut Pcx,
    stop: EnumSet<Token>,
    template: bool
) -> compile::Result<u8> {
    let mut nextcap = 0;
    let mut parens = ParenCounter::default();
    while !(stop.contains(pcx.data.token) && parens.balanced()) {
        parens.token(pcx.data.token);
        match pcx.data.token {
            Token::CapName if template => return syntaxerr(pcx, SyntaxError::CapNameInTemplate),
            Token::CapPos | Token::Dollar if !template
                => return syntaxerr(pcx, SyntaxError::CapPosInBody),
            Token::Dollar => {
                pcx.tmp.push([Token::OpInsert as u8, nextcap]);
                nextcap += 1;
            },
            Token::DollarDollar => {
                pcx.tmp.push(Token::OpThis as u8);
            },
            Token::CapName => {
                let name: IRef<[u8]> = zerocopy::transmute!(pcx.data.tdata);
                let idx = match pcx.data.marg.iter().position(|a| *a == name) {
                    Some(i) => i,
                    None => return syntaxerr(pcx, SyntaxError::UndefCap)
                };
                pcx.tmp.push([Token::OpInsert as u8, idx as u8]);
                nextcap = max(nextcap, idx as u8+1);
            },
            Token::CapPos => {
                pcx.tmp.push([Token::OpInsert as u8, pcx.data.tdata as u8]);
            }
            Token::Literal => {
                // this mess should probably go somewhere in the lexer instead.
                let sid: IRef<[u8]> = zerocopy::transmute!(pcx.data.tdata);
                let Range { start, end } = pcx.intern.get_range(sid.cast());
                let mut data: &[u8] = pcx.intern.bump().as_slice();
                if let Some(mut cursor) = data[start..end].iter().position(|c| *c == '$' as _) {
                    pcx.tmp.push(Token::OpLiteralBoundary as u8);
                    let mut base = start;
                    cursor += base;
                    loop {
                        // INVARIANT: here cursor points at '$'
                        if cursor > base {
                            pcx.tmp.push(Token::Literal as u8);
                            pcx.tmp.push(pcx.intern.intern_range(base..cursor));
                            data = pcx.intern.bump().as_slice();
                        }
                        if cursor >= end { break; }
                        assert!(end <= data.len()); // eliminate some bound checks.
                        cursor += 1;
                        match data.get(cursor) {
                            Some(b'$') => {
                                pcx.tmp.push(Token::OpThis as u8);
                                cursor += 1;
                            },
                            Some(&(mut c)) if c.is_ascii_digit() => {
                                if !template { return syntaxerr(pcx, SyntaxError::CapPosInBody) }
                                let mut idx = 0;
                                loop {
                                    idx = 10*idx + c-b'0';
                                    cursor += 1;
                                    if cursor >= end { break }
                                    c = data[cursor];
                                    if !c.is_ascii_digit() { break }
                                }
                                pcx.tmp.push([Token::OpInsert as u8, idx]);
                                nextcap = max(nextcap, idx+1);
                            },
                            Some(&(mut c)) if c.is_ascii_alphanumeric() || c == b'_' => {
                                if template { return syntaxerr(pcx, SyntaxError::CapNameInTemplate) }
                                let start = cursor;
                                loop {
                                    cursor += 1;
                                    if cursor >= end { break }
                                    c = data[cursor];
                                    if !(c.is_ascii_alphanumeric() || c == b'_') { break }
                                }
                                let cap = match pcx.intern.find(&data[start..cursor]) {
                                    Some(r) => r,
                                    None => return syntaxerr(pcx, SyntaxError::UndefCap)
                                }.cast();
                                let idx = match pcx.data.marg.iter().position(|a| *a == cap) {
                                    Some(i) => i,
                                    None => return syntaxerr(pcx, SyntaxError::UndefCap)
                                };
                                pcx.tmp.push([Token::OpInsert as u8, idx as _]);
                            },
                            _ => {
                                if !template { return syntaxerr(pcx, SyntaxError::CapPosInBody) }
                                pcx.tmp.push([Token::OpInsert as u8, nextcap]);
                                nextcap += 1;
                            }
                        }
                        base = cursor;
                        while cursor < end && data[cursor] != b'$' { cursor += 1 }
                    }
                } else {
                    save(pcx);
                }
            },
            _ => save(pcx)
        }
        next(pcx)?;
    }
    Ok(nextcap)
}

fn parse_macro_body(pcx: &mut Pcx, stop: EnumSet<Token>, template: bool) -> compile::Result<u8> {
    pcx.data.rec = true;
    let r = parse_macro_body_rec(pcx, stop, template);
    pcx.data.rec = false;
    r
}

fn parse_macro_table(pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_macro_model(pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_macro_func(pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_snippet(pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_toplevel(pcx: &mut Pcx) -> compile::Result {
    loop {
        match pcx.data.token {
            Token::Eof   => return Ok(()),
            Token::Table => parse_table(pcx)?,
            Token::Model => parse_model(pcx)?,
            Token::Func  => parse_func(pcx)?,
            Token::Macro => {
                next(pcx)?;
                match pcx.data.token {
                    Token::Table => parse_macro_table(pcx),
                    Token::Model => parse_macro_model(pcx),
                    Token::Func  => parse_macro_func(pcx),
                    _            => parse_snippet(pcx)
                }?
            },
            _ => return tokenerr(pcx, TOPLEVEL_KEYWORDS)
        }
        pcx.data.bindings.clear();
    }
}

/* -------------------------------------------------------------------------- */

pub fn parse_def(pcx: &mut Pcx) -> compile::Result {
    parse_toplevel(pcx)
}

pub fn parse_expr(pcx: &mut Pcx) -> compile::Result<ObjRef<EXPR>> {
    parse_binop(pcx, 0)
}

pub fn parse_template(pcx: &mut Pcx) -> compile::Result<IRef<[u8]>> {
    let base = pcx.tmp.end();
    parse_macro_body(pcx, Token::Eof.into(), true)?;
    let template = pcx.intern.intern(&pcx.tmp[base..]);
    pcx.tmp.truncate(base);
    Ok(template)
}
