//! Source -> Graph.

use core::cmp::max;
use core::iter::repeat_n;
use core::ops::Range;

use enumset::{enum_set, EnumSet};

use crate::bump::BumpRef;
use crate::compile;
use crate::intern::Interned;
use crate::lang::Lang;
use crate::lex::Token;
use crate::obj::{cast_args, BinOp, Intrinsic, LocalId, LookupEntry, Obj, ObjRef, ObjectRef, APPLY, BINOP, CALL, CAT, EXPR, FLAT, FUNC, INTR, KINT, LEN, LET, LGET, LOAD, MOD, PGET, SPLAT, TAB, TGET, TPRI, TTEN, TTUP, TUPLE, VAR, VGET, VSET};
use crate::parser::{check, consume, defmacro, next, parse_name, parse_name_pattern, pushmacro, require, save, DefinitionError, DefinitionErrorType, SyntaxError, LangError, Namespace, ParenCounter, Pcx, TokenError};
use crate::typing::Primitive;

const TOPLEVEL_KEYWORDS: EnumSet<Token> = enum_set!(
    Token::Model | Token::Table | Token::Func | Token::Macro | Token::Eof
);

fn parse_dotname(pcx: &mut Pcx) -> compile::Result<(Interned<[u8]>, Interned<[u8]>)> {
    let name = parse_name(pcx)?;
    Ok(match check(pcx, Token::Dot)? {
        true  => (name, parse_name(pcx)?),
        false => (Interned::EMPTY, name)
    })
}

fn implicittab(pcx: &mut Pcx) -> compile::Result<ObjRef<TAB>> {
    let tab = pcx.data.tab;
    if tab.is_nil() {
        return pcx.error(SyntaxError::BadImplicitTab);
    }
    Ok(tab)
}

fn newundef(pcx: &mut Pcx, id: ObjRef) -> ObjRef {
    pcx.objs[id].mark = 1;
    pcx.data.undef.push(id);
    id
}

fn reftab(pcx: &mut Pcx, name: Interned<[u8]>) -> ObjRef<TAB> {
    let id = match pcx.objs.tab(name) {
        LookupEntry::Occupied(id) => return id,
        LookupEntry::Vacant(e) => e.create()
    };
    newundef(pcx, id.erase()).cast()
}

fn reffunc(pcx: &mut Pcx, name: Interned<[u8]>) -> ObjRef<FUNC> {
    let id = match pcx.objs.func(name) {
        LookupEntry::Occupied(id) => return id,
        LookupEntry::Vacant(e) => e.create()
    };
    newundef(pcx, id.erase()).cast()
}

fn refvar(pcx: &mut Pcx, tab: ObjRef<TAB>, name: Interned<[u8]>) -> ObjRef<VAR> {
    let id = match pcx.objs.var(tab, name) {
        LookupEntry::Occupied(id) => return id,
        LookupEntry::Vacant(e) => e.create()
    };
    newundef(pcx, id.erase()).cast()
}

fn newanonvar(pcx: &mut Pcx, tab: ObjRef<TAB>, ann: ObjRef/*TY*/, value: ObjRef<EXPR>) -> ObjRef<VAR> {
    let var = pcx.objs.push(VAR::new(Interned::EMPTY, tab, ann));
    let vset = pcx.objs.push_args::<VSET>(VSET::new(0, var), &[]);
    pcx.objs.push_args::<MOD>(MOD::new(tab, ObjRef::NIL.cast(), value), &[vset]);
    var
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
    let tab = match tab.is_empty() {
        true  => implicittab(pcx)?,
        false => reftab(pcx, tab)
    };
    Ok(refvar(pcx, tab, name))
}

fn builtincall(pcx: &mut Pcx, name: Interned<[u8]>, base: BumpRef<u8>) -> Option<ObjRef<EXPR>> {
    const IDENT: u8 = Token::Ident as _;
    const INT: u8 = Token::Int as _;
    const APOSTROPHE: u8 = Token::Apostrophe as _;
    const LCURLY: u8 = Token::LCurly as _;
    const RCURLY: u8 = Token::RCurly as _;
    let name @ [IDENT, _, _, _, _, rest @ .. ] = &pcx.intern[name] else { return None };
    let stem: [u8; 4] = name[1..5].try_into().unwrap();
    let stem: Interned<[u8]> = zerocopy::transmute!(stem);
    let stem: &[u8] = &pcx.intern[stem];
    let args: &[ObjRef<EXPR>] = &pcx.tmp[base.cast_up()..];
    if let Some(intrin) = Intrinsic::from_func(stem) {
        return match rest.is_empty() {
            true => Some(pcx.objs.push_args::<INTR>(INTR::new(intrin as _, ObjRef::NIL), args)
                .cast()),
            false => None
        };
    }
    // TODO: this needs some cleanup
    match stem {
        b"load" => {
            let tail @ [APOSTROPHE, LCURLY, IDENT, _, _, _, _, RCURLY] = rest else { return None };
            let ty: [u8; 4] = tail[3..7].try_into().unwrap();
            let ty: Interned<[u8]> = zerocopy::transmute!(ty);
            let pri = pcx.objs.push(TPRI::new(Primitive::from_name(&pcx.intern[ty])? as u8)).erase();
            let ann = match args.len() {
                1 => pri,
                n => pcx.objs.push(TTEN::new(n as u8 - 1, pri)).erase()
            };
            // TODO: allow some special syntax eg. `_` here to elide the size when returning
            // a full table variable.
            Some(pcx.objs.push_args::<LOAD>(LOAD::new(ann, args[0]), &args[1..]).cast())
        },
        b"len" => {
            let dim: u32 = match rest {
                &[] => 0,
                &[APOSTROPHE, LCURLY, INT, x0, x1, x2, x3, RCURLY] =>
                    zerocopy::transmute!([x0, x1, x2, x3]),
                _ => return None
            };
            Some(pcx.objs.push(LEN::new(dim as _, ObjRef::NIL, args[0])).cast())
        },
        _ => None
    }
}

fn usercall(
    pcx: &mut Pcx,
    name: Interned<[u8]>,
    base: BumpRef<ObjRef<EXPR>>
) -> ObjRef<APPLY> {
    let func = reffunc(pcx, name);
    pcx.objs.push_args(APPLY::new(ObjRef::NIL, func), &pcx.tmp[base..])
}

fn parse_apply(pcx: &mut Pcx, name: Interned<[u8]>) -> compile::Result<ObjRef<EXPR>> {
    next(pcx)?; // skip '('
    let base = pcx.tmp.end();
    while pcx.data.token != Token::RParen {
        let param = parse_expr(pcx)?;
        pcx.tmp.push(param);
        if !check(pcx, Token::Comma)? { break }
    }
    consume(pcx, Token::RParen)?;
    // TODO: remove the builtin check here, and make then normal functions
    let expr = match builtincall(pcx, name, base) {
        Some(expr) => expr,
        None => usercall(pcx, name, base.cast_up()).cast()
    };
    pcx.tmp.truncate(base);
    Ok(expr)
}

fn parse_idxelem(pcx: &mut Pcx, ingroup: bool) -> compile::Result<usize> {
    let mut dim = 0;
    while check(pcx, Token::Colon)? {
        dim += 1;
    }
    if (Token::Comma|Token::RParen|Token::RBracket).contains(pcx.data.token) {
        match dim {
            0 => return pcx.error(SyntaxError::ExpectedValue),
            1 => {
                pcx.tmp.push(ObjRef::NIL);
            },
            _ if ingroup => {
                pcx.tmp.extend(repeat_n(ObjRef::NIL, dim));
            },
            _ => {
                let flat = pcx.objs.push_extend::<FLAT,_>(FLAT::new(ObjRef::UNIT),
                    repeat_n(ObjRef::NIL.cast(), dim));
                pcx.tmp.push(flat);
            }
        }
    } else {
        if dim > 0 {
            pcx.tmp.extend(repeat_n(ObjRef::SLURP, dim));
        }
        let value = parse_expr(pcx)?;
        pcx.tmp.push(value);
        dim += 1;
    }
    Ok(dim)
}

// pushes indices on pcx.tmp, return total number of mentioned axes
// note: lower and typeinfer assume that NIL may not preceded by a SLURP, ie they assume
// the following canonicalization:
//   * A[::]   -> A[(:,:)]
//   * A[(::)] -> A[(:,:)]
fn parse_vrefidx(pcx: &mut Pcx) -> compile::Result<u8> {
    let mut dim = 0;
    if check(pcx, Token::LBracket)? {
        while pcx.data.token != Token::RBracket {
            if check(pcx, Token::LParen)? {
                if pcx.data.token != Token::Colon {
                    let value = parse_expr(pcx)?;
                    dim += 1;
                    match pcx.data.token {
                        Token::RParen => {
                            next(pcx)?;
                            let value = parse_binop_rhs(pcx, 0, value)?;
                            pcx.tmp.push(value);
                        },
                        Token::Comma => {
                            next(pcx)?;
                            let base = pcx.tmp.end();
                            pcx.tmp.push(value);
                            while pcx.data.token != Token::RParen {
                                dim += parse_idxelem(pcx, true)?;
                                if !check(pcx, Token::Comma)? { break }
                            }
                            consume(pcx, Token::RParen)?;
                            let flat = pcx.objs.push_args::<FLAT>(FLAT::new(ObjRef::UNIT),
                                &pcx.tmp[base.cast_up()..]);
                            pcx.tmp.truncate(base);
                            pcx.tmp.push(flat);
                        },
                        _ => return pcx.error(TokenError { want: Token::RParen | Token::Comma })
                    }
                }
            } else {
                dim += parse_idxelem(pcx, false)?;
            }
            if !check(pcx, Token::Comma)? { break }
        }
        consume(pcx, Token::RBracket)?;
    }
    Ok(dim as _)
}

fn parse_vget(pcx: &mut Pcx, var: ObjRef<VAR>) -> compile::Result<ObjRef<VGET>> {
    let base = pcx.tmp.end();
    let dim = parse_vrefidx(pcx)?;
    let vget = pcx.objs.push_args(VGET::new(dim as _, ObjRef::NIL, var), &pcx.tmp[base.cast_up()..]);
    pcx.tmp.truncate(base);
    Ok(vget)
}

fn parse_callx(pcx: &mut Pcx, n: usize) -> compile::Result<ObjRef<CALL>> {
    consume(pcx, Token::Call)?;
    require(pcx, Token::Ident)?;
    let lang: Interned<[u8]> = zerocopy::transmute!(pcx.data.tdata);
    let Some(lang) = Lang::from_name(&pcx.intern[lang]) else { return pcx.error(LangError) };
    next(pcx)?; // skip name
    lang.parse(pcx, n)
}

// TODO: this can't parse nested arrays etc. (should those even be exposed to the user?)
fn parse_typeann(pcx: &mut Pcx) -> compile::Result<ObjRef/*TY*/> {
    let mut ty = match check(pcx, Token::Ident)? {
        true => {
            let name: Interned<[u8]> = zerocopy::transmute!(pcx.data.tdata);
            match Primitive::from_name(&pcx.intern[name]) {
                Some(pri) => pcx.objs.push(TPRI::new(pri as _)).erase(),
                None => return pcx.error(SyntaxError::ExpectedPrimitive)
            }
        },
        false => ObjRef::NIL
    };
    if check(pcx, Token::LBracket)? {
        let mut dim = 0;
        while pcx.data.token != Token::RBracket {
            consume(pcx, Token::Colon)?;
            dim += 1;
            if !check(pcx, Token::Comma)? { break }
        }
        consume(pcx, Token::RBracket)?;
        // shorthand: [] is the same as [:]
        dim = max(dim, 1);
        ty = pcx.objs.push(TTEN::new(dim as _, ty)).erase();
    }
    if ty.is_nil() {
        return pcx.error(SyntaxError::ExpectedType);
    }
    Ok(ty)
}

fn parse_maybeann(pcx: &mut Pcx) -> compile::Result<ObjRef/*TY*/> {
    Ok(match check(pcx, Token::Colon)? {
        true  => parse_typeann(pcx)?,
        false => ObjRef::NIL
    })
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

fn parse_maybesuffix(pcx: &mut Pcx, expr: ObjRef<EXPR>) -> compile::Result<ObjRef<EXPR>> {
    if check(pcx, Token::LBracket)? {
        // TODO: emit IDX
        todo!()
    }
    Ok(expr)
}

fn parse_nameref(pcx: &mut Pcx, name: Interned<[u8]>) -> compile::Result<ObjRef<EXPR>> {
    let bindings = &pcx.data.bindings;
    let npar = pcx.data.bindparams as usize;
    for i in (npar..bindings.len()).rev() {
        if bindings[i] == name {
            return Ok(pcx.objs.push(LGET::new(ObjRef::NIL,
                        zerocopy::transmute!((i-npar) as u32))).cast());
        }
    }
    for i in (0..npar).rev() {
        if pcx.data.bindings[i] == name {
            return Ok(pcx.objs.push(PGET::new(i as _, ObjRef::NIL)).cast());
        }
    }
    let tab = implicittab(pcx)?;
    let var = refvar(pcx, tab, name);
    let vget = parse_vget(pcx, var)?;
    Ok(vget.cast())
}

fn parse_letin(pcx: &mut Pcx) -> compile::Result<ObjRef<EXPR>> {
    next(pcx)?;
    let bindbase = pcx.data.bindings.len();
    let binddim = pcx.data.bindparams as usize;
    let name = parse_name(pcx)?;
    let ann = parse_maybeann(pcx)?;
    let outer = pcx.objs.push(LET::new(ann, ObjRef::NIL.cast(), ObjRef::NIL.cast()));
    let mut inner = outer;
    match pcx.data.token {
        Token::Eq => {
            next(pcx)?;
            pcx.data.bindings.push(name);
            pcx.objs[inner].value = parse_expr(pcx)?;
        },
        Token::Comma => {
            let base = pcx.tmp.end();
            let bslot: LocalId = zerocopy::transmute!((bindbase-binddim) as u32);
            let (mut name, mut ann, mut idx) = (name, ann, 0usize);
            loop {
                pcx.tmp.push(name);
                let lgeto = pcx.objs.push(LGET::new(ann, bslot));
                let geti = pcx.objs.push(TGET::new(idx as _, ann, lgeto.cast())).cast();
                let chain = pcx.objs.push(LET::new(ann, geti, ObjRef::NIL.cast()));
                pcx.objs[inner].expr = chain.cast();
                inner = chain;
                idx += 1;
                if !check(pcx, Token::Comma)? { break }
                name = parse_name(pcx)?;
                ann = parse_maybeann(pcx)?;
            }
            consume(pcx, Token::Eq)?;
            let call = parse_callx(pcx, idx)?;
            pcx.objs[outer].value = call.cast();
            pcx.data.bindings.extend_from_slice(&pcx.tmp[base.cast_up()..]);
            pcx.tmp.truncate(base);
        },
        _ => return pcx.error(TokenError { want: Token::Eq | Token::Comma })
    };
    consume(pcx, Token::In)?;
    pcx.objs[inner].expr = parse_expr(pcx)?;
    pcx.data.bindings.truncate(bindbase);
    Ok(outer.cast())
}

fn parse_value(pcx: &mut Pcx) -> compile::Result<ObjRef<EXPR>> {
    match pcx.data.token {
        Token::Scope | Token::Ident => {
            let name = parse_name(pcx)?;
            let expr = match pcx.data.token {
                Token::LParen => parse_apply(pcx, name)?,
                Token::Dot => {
                    next(pcx)?;
                    let tab = reftab(pcx, name);
                    let name = parse_name(pcx)?;
                    let var = refvar(pcx, tab, name);
                    let vget = parse_vget(pcx, var)?;
                    vget.cast()
                },
                _ => parse_nameref(pcx, name)?
            };
            parse_maybesuffix(pcx, expr)
        },
        Token::LParen => {
            next(pcx)?;
            let node = parse_expr(pcx)?;
            consume(pcx, Token::RParen)?;
            parse_maybesuffix(pcx,node)
        },
        Token::LBracket => {
            next(pcx)?;
            let base = pcx.tmp.end();
            while pcx.data.token != Token::RBracket {
                let value = if check(pcx, Token::DotDot)? {
                    // UNARY_PRIORITY here makes it behave like an unary operator, so that eg.
                    //   [..a+b]
                    // is not syntactically valid, you need to say
                    //   [..(a+b)]
                    // just in case this becomes an actual unary operator later.
                    // plus it looks cleaner anyway.
                    let value = parse_binop(pcx, UNARY_PRIORITY)?;
                    pcx.objs.push(SPLAT::new(ObjRef::NIL, value)).cast()
                } else {
                    parse_expr(pcx)?
                };
                pcx.tmp.push(value);
                if !check(pcx, Token::Comma)? { break }
            }
            consume(pcx, Token::RBracket)?;
            let cat = pcx.objs.push_args::<CAT>(CAT::new(ObjRef::NIL), &pcx.tmp[base.cast_up()..]);
            pcx.tmp.truncate(base);
            parse_maybesuffix(pcx, cat.cast())
        },
        Token::Let => parse_letin(pcx),
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
        Token::Call => Ok(parse_callx(pcx, 1)?.cast()),
        Token::True => { next(pcx)?; Ok(ObjRef::TRUE.cast()) },
        Token::False => { next(pcx)?; Ok(ObjRef::FALSE.cast()) },
        _ => return pcx.error(SyntaxError::ExpectedValue)
    }
}

fn parse_binop_rhs(
    pcx: &mut Pcx,
    limit: u8,
    mut lhs: ObjRef<EXPR>
) -> compile::Result<ObjRef<EXPR>> {
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

fn parse_binop(pcx: &mut Pcx, limit: u8) -> compile::Result<ObjRef<EXPR>> {
    let lhs = parse_value(pcx)?;
    parse_binop_rhs(pcx, limit, lhs)
}

fn parse_table(pcx: &mut Pcx) -> compile::Result {
    next(pcx)?; // skip `table`
    let name = parse_name(pcx)?;
    let tab = pcx.objs.tab(name).get_or_create();
    if !pcx.objs[tab].shape.is_nil() {
        return pcx.error(DefinitionError {
            ns: Namespace::Table,
            body: name,
            what: DefinitionErrorType::Redefinition
        });
    }
    pcx.objs[tab].mark = 0;
    let base = pcx.tmp.end();
    if check(pcx, Token::LBracket)? {
        pcx.data.tab = ObjRef::GLOBAL;
        while pcx.data.token != Token::RBracket {
            let value = match pcx.data.token {
                Token::Colon => {
                    next(pcx)?;
                    ObjRef::NIL
                },
                _ => parse_expr(pcx)?.erase()
            };
            pcx.tmp.push(value);
            if !check(pcx, Token::Comma)? { break }
        }
        consume(pcx, Token::RBracket)?;
    }
    pcx.objs[tab].shape = pcx.objs.push_args::<TUPLE>(
        TUPLE::new(ObjRef::NIL),
        &pcx.tmp[base.cast_up()..]
    ).cast();
    pcx.tmp.truncate(base);
    Ok(())
}

fn parse_model_def(pcx: &mut Pcx, blockguard: Option<ObjRef<VAR>>) -> compile::Result {
    let base = pcx.tmp.end();
    // push (vset, ann) pairs
    loop {
        let var = parse_vref(pcx)?;
        pcx.objs[var].mark = 0;
        let base2 = pcx.tmp.end();
        let dim = parse_vrefidx(pcx)?;
        let ann = parse_maybeann(pcx)?;
        let vset = pcx.objs.push_args::<VSET>(VSET::new(dim as _, var), &pcx.tmp[base2.cast_up()..]);
        pcx.tmp.truncate(base2);
        pcx.tmp.push(vset);
        pcx.tmp.push(ann);
        match pcx.data.token {
            Token::Comma => { next(pcx)?; continue; },
            Token::Eq    => { next(pcx)?; break },
            _            => return pcx.error(TokenError { want: Token::Comma | Token::Eq })
        }
    }
    let mut ref_base = base.cast_up::<ObjRef>();
    let n = pcx.tmp[ref_base..].len()/2;
    debug_assert!(n > 0);
    let value = match n {
        1 => {
            let value = parse_expr(pcx)?;
            let ann = pcx.tmp.pop().unwrap();
            pcx.objs.annotate(value, ann);
            value
        },
        _ => {
            let value = parse_callx(pcx, n)?;
            // transform [vset1, ann1, ..., vsetN, annN] -> [vset1, ..., vsetN, ann1, ..., annN]
            let (new, _) = pcx.tmp.reserve_dst::<[ObjRef]>(2*n);
            for i in 0..n {
                pcx.tmp[new.elem(i)] = pcx.tmp[ref_base.add(2*i)];
                pcx.tmp[new.elem(n+i)] = pcx.tmp[ref_base.add(2*i+1)];
            }
            let anns = new.elem(n);
            if pcx.tmp[anns..].iter().any(|i| !i.is_nil()) {
                let ann = pcx.objs.push_args::<TTUP>(TTUP::new(), &pcx.tmp[anns..]);
                pcx.objs.annotate(value.cast(), ann.erase());
            }
            pcx.tmp.truncate(anns);
            ref_base = new.base();
            value.cast()
        }
    };
    let guard = match check(pcx, Token::Where)? {
        true  => Some(parse_expr(pcx)?),
        false => None
    };
    let blockguard = blockguard
        .map(|v| pcx.objs.push_args::<VGET>(VGET::new(0, ObjRef::B1.erase(), v), &[]).cast());
    let guard = match (blockguard, guard) {
        (Some(g), None) | (None, Some(g)) => g,
        (Some(b), Some(g)) => pcx.objs.push(BINOP::new(BinOp::AND as _, ObjRef::NIL, b, g)).cast(),
        (None, None) => ObjRef::NIL.cast()
    };
    // pcx.data.tab is guaranteed to be set here because we came here from parse_model
    pcx.objs.push_args::<MOD>(MOD::new(pcx.data.tab, guard, value), cast_args(&pcx.tmp[ref_base..]));
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
            _ => return pcx.error(TokenError { want: Token::Ident.into() })
        },
        _ => {
            let name = parse_name(pcx)?;
            reftab(pcx, name)
        }
    };
    pcx.data.tab = tab;
    debug_assert!(pcx.data.bindings.is_empty());
    let blockguard = match check(pcx, Token::Where)? {
        true => {
            let value = parse_expr(pcx)?;
            Some(newanonvar(pcx, tab, ObjRef::B1.erase(), value))
        },
        false => None
    };
    if check(pcx, Token::LBracket)? {
        while pcx.data.token != Token::RBracket {
            if pcx.data.token == Token::Colon {
                next(pcx)?;
                continue;
            }
            let name = parse_name(pcx)?;
            pcx.data.bindings.push(name);
            if pcx.data.token == Token::Comma {
                next(pcx)?;
            } else {
                consume(pcx, Token::RBracket)?;
                break;
            }
        }
    }
    pcx.data.bindparams = pcx.data.bindings.len() as _;
    if check(pcx, Token::LCurly)? {
        while pcx.data.token != Token::RCurly {
            parse_model_def(pcx, blockguard)?;
        }
        next(pcx)?;
    } else {
        parse_model_def(pcx, blockguard)?;
    }
    pcx.data.bindings.clear();
    pcx.data.bindparams = 0;
    Ok(())
}

fn parse_func(pcx: &mut Pcx) -> compile::Result {
    pcx.data.tab = ObjRef::GLOBAL;
    next(pcx)?; // skip `func`
    let name = parse_name(pcx)?;
    let func = reffunc(pcx, name);
    consume(pcx, Token::LParen)?;
    while pcx.data.token != Token::RParen {
        let name = parse_name(pcx)?;
        pcx.data.bindings.push(name);
        if !check(pcx, Token::Comma)? { break }
    }
    consume(pcx, Token::RParen)?;
    consume(pcx, Token::Eq)?;
    pcx.objs[func].arity = pcx.data.bindings.len() as _;
    pcx.objs[func].mark = 0;
    pcx.data.bindparams = pcx.data.bindings.len() as _;
    let value = parse_expr(pcx)?;
    pcx.objs[func].expr = value;
    pcx.data.bindings.clear();
    pcx.data.bindparams = 0;
    Ok(())
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
            Token::CapName if template => return pcx.error(SyntaxError::CapNameInTemplate),
            Token::CapPos | Token::Dollar if !template
                => return pcx.error(SyntaxError::CapPosInBody),
            Token::Dollar => {
                pcx.tmp.push([Token::OpInsert as u8, nextcap]);
                nextcap += 1;
            },
            Token::DollarDollar => {
                pcx.tmp.push(Token::OpThis as u8);
            },
            Token::CapName => {
                let name: Interned<[u8]> = zerocopy::transmute!(pcx.data.tdata);
                let idx = match pcx.data.marg.iter().position(|a| *a == name) {
                    Some(i) => i,
                    None => return pcx.error(SyntaxError::UndefCap),
                };
                pcx.tmp.push([Token::OpInsert as u8, idx as u8]);
                nextcap = max(nextcap, idx as u8+1);
            },
            Token::CapPos => {
                pcx.tmp.push([Token::OpInsert as u8, pcx.data.tdata as u8]);
            }
            Token::Literal => {
                // this mess should probably go somewhere in the lexer instead.
                let sid: Interned<[u8]> = zerocopy::transmute!(pcx.data.tdata);
                let Range { start, end } = pcx.intern.get_range(sid);
                let mut data: &[u8] = pcx.intern.as_slice();
                if let Some(mut cursor) = data[start..end].iter().position(|c| *c == '$' as _) {
                    pcx.tmp.push(Token::OpLiteralBoundary as u8);
                    let mut base = start;
                    cursor += base;
                    loop {
                        // INVARIANT: here cursor points at '$'
                        if cursor > base {
                            pcx.tmp.push(Token::Literal as u8);
                            // write it this way so that it doesn't add padding for alignment.
                            let lit: [u8; 4] = zerocopy::transmute!(pcx.intern.intern_range(base..cursor));
                            pcx.tmp.push(lit);
                            data = pcx.intern.as_slice();
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
                                if !template { return pcx.error(SyntaxError::CapPosInBody) }
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
                                if template { return pcx.error(SyntaxError::CapNameInTemplate) }
                                let start = cursor;
                                loop {
                                    cursor += 1;
                                    if cursor >= end { break }
                                    c = data[cursor];
                                    if !(c.is_ascii_alphanumeric() || c == b'_') { break }
                                }
                                let cap = match pcx.intern.find(&data[start..cursor]) {
                                    Some(r) => r,
                                    None => return pcx.error(SyntaxError::UndefCap)
                                };
                                let idx = match pcx.data.marg.iter().position(|a| *a == cap) {
                                    Some(i) => i,
                                    None => return pcx.error(SyntaxError::UndefCap)
                                };
                                pcx.tmp.push([Token::OpInsert as u8, idx as _]);
                            },
                            _ => {
                                if !template { return pcx.error(SyntaxError::CapPosInBody) }
                                pcx.tmp.push([Token::OpInsert as u8, nextcap]);
                                nextcap += 1;
                            }
                        }
                        base = cursor;
                        while cursor < end && data[cursor] != b'$' { cursor += 1 }
                    }
                    pcx.tmp.push(Token::OpLiteralBoundary as u8);
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

fn parse_pattern(pcx: &mut Pcx) -> compile::Result<Interned<[u8]>> {
    match pcx.data.token {
        Token::CapName => {
            let name: Interned<[u8]> = zerocopy::transmute!(pcx.data.tdata);
            pcx.data.marg.push(name);
            next(pcx)?;
            Ok(pcx.intern.intern(&[Token::OpInsert as u8]))
        },
        _ => parse_name_pattern(pcx)
    }
}

fn parse_macro_var(pcx: &mut Pcx) -> compile::Result {
    next(pcx)?; // skip `var`
    pcx.data.undef_base = 0;
    pcx.data.marg.clear();
    let table_pattern = parse_pattern(pcx)?;
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
    defmacro(pcx, Namespace::Snippet, Interned::EMPTY, name, body);
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
            _ => return pcx.error(TokenError { want: TOPLEVEL_KEYWORDS })
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
                ObjectRef::TAB(&TAB { name, .. }) => (Namespace::Table, Interned::EMPTY, name),
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

fn expandtab(pcx: &mut Pcx, name: Interned<[u8]>) -> compile::Result<ExpandResult<TAB, Interned<[u8]>>> {
    let id = match pcx.objs.tab(name) {
        LookupEntry::Occupied(id) => return Ok(ExpandResult::Defined(id)),
        LookupEntry::Vacant(e) => match pushmacro(
            &mut pcx.data,
            &pcx.intern,
            Namespace::Table,
            Interned::EMPTY,
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
    name: Interned<[u8]>
) -> compile::Result<ExpandResult<VAR, (Interned<[u8]>, Interned<[u8]>)>> {
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

pub fn parse_expand_tab(pcx: &mut Pcx) -> compile::Result<ExpandResult<TAB, Interned<[u8]>>> {
    let name = parse_name(pcx)?;
    expandtab(pcx, name)
}

pub fn parse_expand_var(
    pcx: &mut Pcx
) -> compile::Result<ExpandResult<VAR, (Interned<[u8]>, Interned<[u8]>)>> {
    let (tab, name) = parse_dotname(pcx)?;
    let table = match tab.is_empty() {
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

pub fn parse_template(pcx: &mut Pcx) -> compile::Result<Interned<[u8]>> {
    let base = pcx.tmp.end();
    parse_macro_body(pcx, Token::Eof.into(), true)?;
    let template = pcx.intern.intern(&pcx.tmp[base..]);
    pcx.tmp.truncate(base);
    Ok(template)
}
