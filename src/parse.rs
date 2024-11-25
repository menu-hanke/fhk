//! Source -> Graph.

use core::cmp::max;
use core::ops::Range;

use enumset::{enum_set, EnumSet};
use zerocopy::IntoBytes;

use crate::compile::{self, Const, Seq};
use crate::index::IndexOption;
use crate::intern::{Intern, InternRef};
use crate::intrinsics::Intrinsic;
use crate::lex::Token;
use crate::obj::{cast_args, ObjRef, CALLN, DIM, EXPR, GET, KINT, MOD, TUPLE, VAR, VGET, VSET};
use crate::parser::{check, consume, next, redeferr, save, syntaxerr, tokenerr, Binding, Namespace, ParenCounter, Pcx, ScopeId, SyntaxError};

pub const TOPLEVEL_KEYWORDS: EnumSet<Token> = enum_set!(
    Token::Model | Token::Table | Token::Func | Token::Macro | Token::Eof
);

fn parse_maybe_scope(pcx: &mut Pcx) -> compile::Result<IndexOption<ScopeId>> {
    Ok(match pcx.data.token {
        Token::Scope => {
            let id = pcx.data.tdata;
            next(pcx)?;
            Some(zerocopy::transmute!(id))
        },
        _ => None
    }.into())
}

fn parse_name(pcx: &mut Pcx) -> compile::Result<InternRef<Seq>> {
    let start = pcx.sequences.bump().end();
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
    Ok(pcx.sequences.intern_consume_from(start).cast())
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

fn getintrinsic(seq: &Intern, constants: &Intern, name: InternRef<Seq>) -> Option<Intrinsic> {
    const IDENT: u8 = Token::Ident as _;
    if let name @ [IDENT, _, _, _, _] = seq.get_slice(name.cast()) {
        let name: [u8; 4] = name[1..].try_into().unwrap();
        let name: InternRef<Const> = zerocopy::transmute!(name);
        Intrinsic::from_func(constants.get_slice(name.cast()))
    } else {
        None
    }
}

fn parse_call(pcx: &mut Pcx, name: InternRef<Seq>) -> compile::Result<ObjRef<EXPR>> {
    next(pcx)?; // skip '('
    let base = pcx.data.tmpref.len();
    while pcx.data.token != Token::RParen {
        let param = parse_expr(pcx)?;
        pcx.data.tmpref.push(param.erase());
        if pcx.data.token == Token::Comma {
            next(pcx)?;
        } else {
            consume(pcx, Token::RParen)?;
            break;
        }
    }
    let expr = if let Some(intrin) = getintrinsic(&pcx.sequences, &pcx.constants, name) {
        pcx.objs.push(&CALLN::new(
                intrin as _,
                ObjRef::NIL,
                cast_args(&pcx.data.tmpref[base..])
        )).cast()
    } else {
        todo!("user function call")
    };
    pcx.data.tmpref.truncate(base);
    Ok(expr)
}

fn parse_vget(pcx: &mut Pcx, var: ObjRef<VAR>) -> compile::Result<ObjRef<EXPR>> {
    if pcx.data.token == Token::LBracket {
        todo!("vget with index")
    }
    Ok(pcx.objs.push(&VGET::new(ObjRef::NIL, var, [])).cast())
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
            todo!("let-in")
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
        Token::Int     => {
            let value = pcx.data.tdata;
            next(pcx)?;
            Ok(pcx.objs.push(&KINT::new(ObjRef::NIL, value as _)).cast())
        }
        // Token::Int64 | Token::Fp64
        //                => Ok(pcx.objs.push(&obj!(KREF k=zerocopy::transmute!(pcx.data.tdata)))
        //                    .erase()),
        // Token::Literal => Ok(pcx.objs.push(&obj!(KREF.STR k=zerocopy::transmute!(pcx.data.tdata)))
        //                    .erase()),
        Token::True    => { next(pcx)?; Ok(ObjRef::TRUE.cast()) },
        Token::False   => { next(pcx)?; Ok(ObjRef::FALSE.cast()) },
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
        lhs = pcx.objs.push(&CALLN::new(
                Intrinsic::OR as u8 + (op as u8 - Token::Or as u8),
                ObjRef::NIL,
                [lhs, rhs]
        )).cast();
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
    debug_assert!(pcx.data.tmpref.is_empty());
    if check(pcx, Token::LBracket)? {
        pcx.data.tab = ObjRef::GLOBAL;
        while pcx.data.token != Token::RBracket {
            let value = parse_expr(pcx)?;
            pcx.data.tmpref.push(value.erase());
            if pcx.data.token == Token::Comma {
                next(pcx)?;
            } else {
                consume(pcx, Token::RBracket)?;
                break;
            }
        }
    }
    pcx.objs[tab].shape = pcx.objs.push(&TUPLE::new(ObjRef::NIL, cast_args(&pcx.data.tmpref))).cast();
    pcx.data.tmpref.clear();
    Ok(())
}

fn deconstruct(pcx: &mut Pcx, value: ObjRef<EXPR>, num: usize) {
    match num {
        0 => {},
        1 => pcx.data.tmpref.push(value.cast()),
        _ => for i in 0..num as u8 {
            let get = pcx.objs.push(&GET::new(i, ObjRef::NIL, value));
            pcx.data.tmpref.push(get.erase());
        }
    }
}

fn parse_model_def(pcx: &mut Pcx) -> compile::Result {
    let base = pcx.data.tmpref.len();
    loop {
        let var = parse_vref(pcx)?;
        if check(pcx, Token::LBracket)? {
            todo!(); // TODO: parse subset
            consume(pcx, Token::RBracket)?;
        }
        let vset = pcx.objs.push(&VSET::new(var, ObjRef::NIL.cast(), []));
        pcx.data.tmpref.push(vset.erase());
        match pcx.data.token {
            Token::Comma => { next(pcx)?; todo!("handle multiple outputs"); continue; },
            Token::Eq    => { next(pcx)?; break },
            _            => return tokenerr(pcx, Token::Comma | Token::Eq)
        }
    }
    let value = parse_expr(pcx)?;
    let num = pcx.data.tmpref.len() - base;
    deconstruct(pcx, value, num);
    for i in (base..base+num).rev() {
        let vset: ObjRef<VSET> = pcx.data.tmpref[i].cast();
        pcx.objs[vset].value = pcx.data.tmpref.pop().unwrap().cast();
    }
    let guard = match pcx.data.token {
        Token::Where => { next(pcx)?; parse_expr(pcx)? },
        _ => ObjRef::NIL.cast()
    };
    pcx.objs.push(&MOD::new(
            InternRef::EMPTY,
            pcx.data.tab,
            guard,
            cast_args(&pcx.data.tmpref[base..])
    ));
    pcx.data.tmpref.truncate(base);
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
            let value = pcx.objs.push(&DIM::new(axis as _, ObjRef::NIL)).cast();
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

fn parse_macro_body_rec(pcx: &mut Pcx, stop: EnumSet<Token>, template: bool) -> compile::Result {
    let mut nextcap = 0;
    let mut parens = ParenCounter::default();
    while !(stop.contains(pcx.data.token) && parens.balanced()) {
        parens.token(pcx.data.token);
        match pcx.data.token {
            Token::CapName if template => return syntaxerr(pcx, SyntaxError::CapNameInTemplate),
            Token::CapPos | Token::Dollar if !template
                => return syntaxerr(pcx, SyntaxError::CapPosInBody),
            Token::Dollar => {
                pcx.sequences.push(&[Token::OpInsert as u8, nextcap]);
                nextcap += 1;
            },
            Token::DollarDollar => {
                pcx.sequences.push(&(Token::OpThis as u8));
            },
            Token::CapName => {
                let name: InternRef<Const> = zerocopy::transmute!(pcx.data.tdata);
                let idx = match pcx.data.marg.iter().position(|a| *a == name) {
                    Some(i) => i,
                    None => return syntaxerr(pcx, SyntaxError::UndefCap)
                };
                pcx.sequences.push(&[Token::OpInsert as u8, idx as u8]);
                nextcap = max(nextcap, idx as u8+1);
            },
            Token::CapPos => {
                pcx.sequences.push(&[Token::OpInsert as u8, pcx.data.tdata as u8]);
            }
            Token::Literal => {
                // this mess should probably go somewhere in the lexer instead.
                let sid: InternRef<Const> = zerocopy::transmute!(pcx.data.tdata);
                let Range { start, end } = pcx.constants.get_range(sid.cast());
                let mut data: &[u8] = pcx.constants.bump().as_slice();
                if let Some(mut cursor) = data[start..end].iter().position(|c| *c == '$' as _) {
                    pcx.sequences.push(&(Token::OpLiteralBoundary as u8));
                    let mut base = start;
                    cursor += base;
                    loop {
                        // INVARIANT: here cursor points at '$'
                        if cursor > base {
                            pcx.sequences.push(&(Token::Literal as u8));
                            pcx.sequences.push(pcx.constants.intern_range(base..cursor).as_bytes());
                            data = pcx.constants.bump().as_slice();
                        }
                        if cursor >= end { break; }
                        assert!(end <= data.len()); // eliminate some bound checks.
                        cursor += 1;
                        match data.get(cursor) {
                            Some(b'$') => {
                                pcx.sequences.push(&(Token::OpThis as u8));
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
                                pcx.sequences.push(&[Token::OpInsert as u8, idx]);
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
                                let cap = match pcx.constants.find(&data[start..cursor]) {
                                    Some(r) => r,
                                    None => return syntaxerr(pcx, SyntaxError::UndefCap)
                                }.cast();
                                let idx = match pcx.data.marg.iter().position(|a| *a == cap) {
                                    Some(i) => i,
                                    None => return syntaxerr(pcx, SyntaxError::UndefCap)
                                };
                                pcx.sequences.push(&[Token::OpInsert as u8, idx as _]);
                            },
                            _ => {
                                if !template { return syntaxerr(pcx, SyntaxError::CapPosInBody) }
                                pcx.sequences.push(&[Token::OpInsert as u8, nextcap]);
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
    Ok(())
}

fn parse_macro_body(pcx: &mut Pcx, stop: EnumSet<Token>, template: bool) -> compile::Result {
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

pub fn parse_template(pcx: &mut Pcx) -> compile::Result<InternRef<Seq>> {
    let start = pcx.sequences.bump().end();
    parse_macro_body(pcx, Token::Eof.into(), true)?;
    Ok(pcx.sequences.intern_consume_from(start).cast())
}
