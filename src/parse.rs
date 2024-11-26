//! Source -> Graph.

use core::cmp::max;
use core::ops::Range;

use enumset::{enum_set, EnumSet};

use crate::bump::BumpRef;
use crate::compile;
use crate::intern::IRef;
use crate::lang::Lang;
use crate::lex::Token;
use crate::obj::{cast_args, BinOp, Intrinsic, LookupEntry, Obj, ObjRef, ObjectRef, BINOP, CALLX, CAT, DIM, EXPR, GET, INTR, KINT, LOAD, MOD, TAB, TPRI, TTEN, TUPLE, VAR, VGET, VSET};
use crate::parser::{check, consume, defmacro, langerr, next, parse_name, parse_name_pattern, pushmacro, redeferr, require, save, syntaxerr, tokenerr, Binding, Namespace, ParenCounter, Pcx, SyntaxError};
use crate::typing::Primitive;

const TOPLEVEL_KEYWORDS: EnumSet<Token> = enum_set!(
    Token::Model | Token::Table | Token::Func | Token::Macro | Token::Eof
);

fn parse_dotname(pcx: &mut Pcx) -> compile::Result<(IRef<[u8]>, IRef<[u8]>)> {
    let name = parse_name(pcx)?;
    Ok(match check(pcx, Token::Dot)? {
        true  => (name, parse_name(pcx)?),
        false => (IRef::EMPTY, name)
    })
}

fn implicittab(pcx: &mut Pcx) -> compile::Result<ObjRef<TAB>> {
    let tab = pcx.data.tab;
    if tab.is_nil() {
        return syntaxerr(pcx, SyntaxError::BadImplicitTab);
    }
    Ok(tab)
}

fn newundef(pcx: &mut Pcx, id: ObjRef) -> ObjRef {
    pcx.objs[id].mark = 1;
    pcx.data.undef.push(id);
    id
}

fn reftab(pcx: &mut Pcx, name: IRef<[u8]>) -> ObjRef<TAB> {
    let id = match pcx.objs.tab(name) {
        LookupEntry::Occupied(id) => return id,
        LookupEntry::Vacant(e) => e.create()
    };
    newundef(pcx, id.erase()).cast()
}

fn refvar(pcx: &mut Pcx, tab: ObjRef<TAB>, name: IRef<[u8]>) -> ObjRef<VAR> {
    let id = match pcx.objs.var(tab, name) {
        LookupEntry::Occupied(id) => return id,
        LookupEntry::Vacant(e) => e.create()
    };
    newundef(pcx, id.erase()).cast()
}

fn parse_vref(pcx: &mut Pcx) -> compile::Result<ObjRef<VAR>> {
    if pcx.data.token == Token::OpThis {
        match pcx.objs[pcx.data.this].op {
            Obj::VAR => {
                next(pcx)?;
                return Ok(pcx.data.this.cast());
            },
            Obj::TAB => {
                next(pcx)?;
                // TODO: `$$.var` where $$ is the this of a macro table.
                todo!()
            },
            _ => {}
        }
    }
    let (tab, name) = parse_dotname(pcx)?;
    let tab = match tab == IRef::EMPTY {
        true  => implicittab(pcx)?,
        false => reftab(pcx, tab)
    };
    Ok(refvar(pcx, tab, name))
}

fn builtincall(pcx: &mut Pcx, name: IRef<[u8]>, base: BumpRef<u8>) -> Option<ObjRef<EXPR>> {
    const IDENT: u8 = Token::Ident as _;
    const APOSTROPHE: u8 = Token::Apostrophe as _;
    const LCURLY: u8 = Token::LCurly as _;
    const RCURLY: u8 = Token::RCurly as _;
    let name @ [IDENT, _, _, _, _, rest @ .. ] = pcx.intern.get_slice(name.cast())
        else { return None };
    let stem: [u8; 4] = name[1..5].try_into().unwrap();
    let stem: &[u8] = pcx.intern.get_slice(zerocopy::transmute!(stem));
    let args: &[ObjRef<EXPR>] = &pcx.tmp[base.cast_up()..];
    if let Some(intrin) = Intrinsic::from_func(stem) {
        return match rest.is_empty() {
            true => Some(pcx.objs.push_args::<INTR>(INTR::new(intrin as _, ObjRef::NIL), args)
                .cast()),
            false => None
        };
    }
    if stem == b"load" {
        let tail @ [APOSTROPHE, LCURLY, IDENT, _, _, _, _, RCURLY] = rest else { return None };
        let ty: [u8; 4] = tail[3..7].try_into().unwrap();
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

fn parse_vget(pcx: &mut Pcx, var: ObjRef<VAR>) -> compile::Result<ObjRef<VGET>> {
    Ok(if pcx.data.token == Token::LBracket {
        next(pcx)?;
        let base = pcx.tmp.end();
        while pcx.data.token != Token::RBracket {
            let idx = parse_expr(pcx)?;
            pcx.tmp.push(idx);
            if !check(pcx, Token::Comma)? { break }
        }
        consume(pcx, Token::RBracket)?;
        let vget = pcx.objs.push_args(VGET::new(ObjRef::NIL, var), &pcx.tmp[base.cast_up()..]);
        pcx.tmp.truncate(base);
        vget
    } else {
        pcx.objs.push(VGET::new(ObjRef::NIL, var)).cast()
    })
}

fn parse_callx(pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALLX>> {
    require(pcx, Token::Ident)?;
    let Some(lang) = Lang::from_name(&pcx.intern.get_slice(zerocopy::transmute!(pcx.data.tdata)))
        else { return langerr(pcx) };
    next(pcx)?; // skip name
    lang.parse(pcx, n)
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
                    let tab = reftab(pcx, name);
                    let name = parse_name(pcx)?;
                    let var = refvar(pcx, tab, name);
                    let vget = parse_vget(pcx, var)?;
                    Ok(vget.cast())
                },
                _ => match pcx.data.bindings.iter().find(|b| b.name == name) {
                    Some(v) => Ok(v.value),
                    None => {
                        let tab = implicittab(pcx)?;
                        let var = refvar(pcx, tab, name);
                        let vget = parse_vget(pcx, var)?;
                        Ok(vget.cast())
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
            next(pcx)?;
            let base = pcx.tmp.end();
            while pcx.data.token != Token::RBracket {
                let value = parse_expr(pcx)?;
                pcx.tmp.push(value);
                if !check(pcx, Token::Comma)? { break }
            }
            consume(pcx, Token::RBracket)?;
            let cat = pcx.objs.push_args::<CAT>(CAT::new(ObjRef::NIL), &pcx.tmp[base.cast_up()..]);
            pcx.tmp.truncate(base);
            Ok(cat.cast())
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
        tok @ (Token::Minus | Token::Not) => {
            next(pcx)?;
            let value = parse_binop(pcx, UNARY_PRIORITY)?;
            let func = match tok {
                Token::Minus     => Intrinsic::UNM,
                _ /* Not */      => Intrinsic::NOT,
            };
            Ok(pcx.objs.push_args::<INTR>(INTR::new(func as _, ObjRef::NIL), &[value]).cast())
        },
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
        lhs = pcx.objs.push(BINOP::new(
                BinOp::OR as u8 + (op as u8 - Token::Or as u8),
                ObjRef::NIL,
                lhs,
                rhs
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
    pcx.objs[tab].mark = 0;
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

fn parse_model_def(pcx: &mut Pcx, blockguard: Option<ObjRef<EXPR>>) -> compile::Result {
    let base = pcx.tmp.end();
    loop {
        let var = parse_vref(pcx)?;
        pcx.objs[var].mark = 0;
        if check(pcx, Token::LBracket)? {
            if true { todo!(); } // TODO: parse subset
            consume(pcx, Token::RBracket)?;
        }
        pcx.tmp.push(pcx.objs.push(VSET::new(var, ObjRef::NIL.cast())));
        match pcx.data.token {
            Token::Comma => { next(pcx)?; if true { todo!("handle multiple outputs"); } continue; },
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
        true  => Some(parse_expr(pcx)?),
        false => None
    };
    let guard = match (blockguard, guard) {
        (Some(g), None) | (None, Some(g)) => g,
        (Some(b), Some(g)) => pcx.objs.push(BINOP::new(BinOp::AND as _, ObjRef::NIL, b, g)).cast(),
        (None, None) => ObjRef::NIL.cast()
    };
    // pcx.data.tab is guaranteed to be set here because we came here from parse_model
    pcx.objs.push_args::<MOD>(
        MOD::new(IRef::EMPTY, pcx.data.tab, guard),
        cast_args(&pcx.tmp[vset_base..deco_base.cast::<ObjRef<VSET>>()])
    );
    pcx.tmp.truncate(base);
    Ok(())
}

fn parse_model(pcx: &mut Pcx) -> compile::Result {
    next(pcx)?; // skip `model`
    let tab = match pcx.data.token {
        Token::OpThis => match pcx.objs[pcx.data.this].op {
            Obj::VAR => {
                // do not consume the token here, it's going to also be used for the var itself.
                pcx.objs[pcx.data.this.cast::<VAR>()].tab
            },
            Obj::TAB => {
                next(pcx)?;
                pcx.data.this.cast()
            },
            _ => return tokenerr(pcx, Token::Ident)
        },
        _ => {
            let name = parse_name(pcx)?;
            reftab(pcx, name)
        }
    };
    pcx.data.tab = tab;
    debug_assert!(pcx.data.bindings.is_empty());
    let blockguard = match check(pcx, Token::Where)? {
        true => Some(parse_expr(pcx)?),
        false => None
    };
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
            parse_model_def(pcx, blockguard)?;
        }
        next(pcx)?;
    } else {
        parse_model_def(pcx, blockguard)?;
    }
    pcx.data.bindings.clear();
    Ok(())
}

fn parse_func(_pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_macro_body_rec(
    pcx: &mut Pcx,
    stop: EnumSet<Token>,
    template: bool
) -> compile::Result {
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
    Ok(())
}

fn parse_macro_body(pcx: &mut Pcx, stop: EnumSet<Token>, template: bool) -> compile::Result {
    pcx.data.rec = true;
    let r = parse_macro_body_rec(pcx, stop, template);
    pcx.data.rec = false;
    r
}

fn checkopenparen(pcx: &mut Pcx) -> compile::Result<Option<Token>> {
    let close = match pcx.data.token {
        Token::LParen   => Token::RParen,
        Token::LBracket => Token::RBracket,
        Token::LCurly   => Token::RCurly,
        _ => return Ok(None)
    };
    next(pcx)?;
    Ok(Some(close))
}

fn parse_macro_var(pcx: &mut Pcx) -> compile::Result {
    next(pcx)?; // skip `var`
    pcx.data.undef_base = 0;
    pcx.data.marg.clear();
    let table_pattern = parse_name_pattern(pcx)?;
    let name_pattern = parse_name_pattern(pcx)?;
    let base = pcx.tmp.end();
    if let Some(stop) = checkopenparen(pcx)? {
        parse_macro_body(pcx, stop.into(), false)?;
        consume(pcx, stop)?;
    } else {
        pcx.tmp.push(Token::Model as u8);
        pcx.tmp.push(Token::OpThis as u8);
        parse_macro_body(pcx, TOPLEVEL_KEYWORDS, false)?;
    }
    let body = pcx.intern.intern(&pcx.tmp[base..]);
    pcx.tmp.truncate(base);
    defmacro(pcx, Namespace::Var, table_pattern, name_pattern, body);
    Ok(())
}

fn parse_macro_table(_pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_macro_model(_pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_macro_func(_pcx: &mut Pcx) -> compile::Result {
    todo!()
}

fn parse_snippet(pcx: &mut Pcx) -> compile::Result {
    pcx.data.marg.clear();
    let name = parse_name_pattern(pcx)?;
    let stop = checkopenparen(pcx)?;
    let base = pcx.tmp.end();
    parse_macro_body(
        pcx,
        match stop { Some(stop) => stop.into(), None => TOPLEVEL_KEYWORDS},
        false
    )?;
    let body = pcx.intern.intern(&pcx.tmp[base..]);
    pcx.tmp.truncate(base);
    defmacro(pcx, Namespace::Snippet, IRef::EMPTY, name, body);
    if let Some(stop) = stop {
        consume(pcx, stop)?;
    }
    Ok(())
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
                    Token::Var   => parse_macro_var(pcx),
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

fn parse_toplevel_objdef(pcx: &mut Pcx, o: ObjRef) -> compile::Result {
    pcx.data.this = o;
    debug_assert!(pcx.objs[o].mark == 1);
    next(pcx)?;
    parse_toplevel(pcx)?;
    if pcx.objs[o].mark != 0 {
        // TODO: report error (macro didn't define object)
        todo!()
    }
    Ok(())
}

fn expandobjs(pcx: &mut Pcx) -> compile::Result {
    loop {
        let i = pcx.data.undef_base;
        let Some(&o) = pcx.data.undef.get(i) else { return Ok(()) };
        if pcx.objs[o].mark != 0 {
            let (ns, table, name) = match pcx.objs.get(o) {
                ObjectRef::VAR(&VAR { tab, name, .. }) => (Namespace::Var, pcx.objs[tab].name, name),
                ObjectRef::TAB(&TAB { name, .. }) => (Namespace::Table, IRef::EMPTY, name),
                ObjectRef::FUNC(_) => todo!(),
                _ => unreachable!()
            };
            match pushmacro(&mut pcx.data, &pcx.intern, ns, table, name) {
                Some(_) => {
                    parse_toplevel_objdef(pcx, o)?;
                },
                None => {
                    pcx.data.undef_base = i+1;
                    continue;
                }
            }
        }
        pcx.data.undef.swap_remove(i);
    }
}

/* ---- Expanded object refs ------------------------------------------------ */

pub enum ExpandResult<O,N> {
    Defined(ObjRef<O>),
    Undefined(N)
}

fn expandtab(pcx: &mut Pcx, name: IRef<[u8]>) -> compile::Result<ExpandResult<TAB, IRef<[u8]>>> {
    let id = match pcx.objs.tab(name) {
        LookupEntry::Occupied(id) => return Ok(ExpandResult::Defined(id)),
        LookupEntry::Vacant(e) => match pushmacro(
            &mut pcx.data,
            &pcx.intern,
            Namespace::Table,
            IRef::EMPTY,
            name
        ) {
            Some(_) => e.create(),
            None => return Ok(ExpandResult::Undefined(name))
        }
    };
    pcx.objs[id].mark = 1;
    parse_toplevel_objdef(pcx, id.erase())?;
    Ok(ExpandResult::Defined(id))
}

fn expandvar(
    pcx: &mut Pcx,
    tab: ObjRef<TAB>,
    name: IRef<[u8]>
) -> compile::Result<ExpandResult<VAR, (IRef<[u8]>, IRef<[u8]>)>> {
    let tabname = pcx.objs[tab].name;
    let id = match pcx.objs.var(tab, name) {
        LookupEntry::Occupied(id) => return Ok(ExpandResult::Defined(id)),
        LookupEntry::Vacant(e) => match pushmacro(
            &mut pcx.data,
            &pcx.intern,
            Namespace::Var,
            tabname,
            name
        ) {
            Some(_) => e.create(),
            None => return Ok(ExpandResult::Undefined((tabname, name)))
        }
    };
    pcx.objs[id].mark = 1;
    parse_toplevel_objdef(pcx, id.erase())?;
    Ok(ExpandResult::Defined(id))
}

pub fn parse_expand_tab(pcx: &mut Pcx) -> compile::Result<ExpandResult<TAB, IRef<[u8]>>> {
    let name = parse_name(pcx)?;
    expandtab(pcx, name)
}

pub fn parse_expand_var(
    pcx: &mut Pcx
) -> compile::Result<ExpandResult<VAR, (IRef<[u8]>, IRef<[u8]>)>> {
    let (tab, name) = parse_dotname(pcx)?;
    let table = match tab == IRef::EMPTY {
        true  => pcx.data.tab,
        false => match expandtab(pcx, tab)? {
            ExpandResult::Defined(t) => t,
            ExpandResult::Undefined(_) => return Ok(ExpandResult::Undefined((tab, name)))
        }
    };
    expandvar(pcx, table, name)
}

/* -------------------------------------------------------------------------- */

pub fn parse_toplevel_def(pcx: &mut Pcx) -> compile::Result {
    parse_toplevel(pcx)?;
    expandobjs(pcx)?;
    Ok(())
}

pub fn parse_expr(pcx: &mut Pcx) -> compile::Result<ObjRef<EXPR>> {
    parse_binop(pcx, 0)
}

pub fn parse_toplevel_expr(pcx: &mut Pcx) -> compile::Result<ObjRef<EXPR>> {
    let expr = parse_expr(pcx)?;
    expandobjs(pcx)?;
    Ok(expr)
}

pub fn parse_template(pcx: &mut Pcx) -> compile::Result<IRef<[u8]>> {
    let base = pcx.tmp.end();
    parse_macro_body(pcx, Token::Eof.into(), true)?;
    let template = pcx.intern.intern(&pcx.tmp[base..]);
    pcx.tmp.truncate(base);
    Ok(template)
}
