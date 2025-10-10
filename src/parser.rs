//! Parser and macro engine.

use core::fmt::Write;
use core::mem::{replace, transmute, ManuallyDrop};
use core::ops::Range;

use alloc::vec::Vec;
use enumset::EnumSet;
use hashbrown::hash_map::Entry;
use logos::Logos;

use crate::bump::Bump;
use crate::compile::{self, Ccx, CompileError, Stage};
use crate::hash::HashMap;
use crate::index::{index, IndexOption, IndexVec};
use crate::intern::{InternPtr, Interned};
use crate::lex::{self, Token};
use crate::obj::{ObjRef, TAB};
use crate::typestate::{typestate_union, Absent, R};

index!(pub struct ScopeId(u32) invalid(!0));
index!(struct MacroId(u32) invalid(!0));

struct Macro {
    table_pattern: Interned<[u8]>, // only for model/var
    name_pattern: Interned<[u8]>,
    body: Interned<[u8]>,
    next: IndexOption<MacroId> // next with same namespace and stem
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Namespace {
    Var,
    Table,
    Snippet,
    // the following are only used for debug messages:
    Capture,
    Template
}

pub type TokenData = u32;

pub struct Frame {
    base: u32,   // index of first capture
    cursor: u32, // byte offset in pcx.intern
    end: u32,    // byte offset in pcx.intern
    lookahead: Option<Token>, // next token after this frame (only used for snippets)
    lookahead_data: TokenData, // next token data
    // only used for debug messages:
    this: u32, // the macro, capture or template we are expanding
    ns: Namespace, // namespace of the macro we are expanding
}

typestate_union!(pub union LexData:_LexData {
    lexer: ManuallyDrop<logos::Lexer<'static, Token>>
});

#[repr(C)] // need repr(C) for transmuting references
pub struct Parser<L=Absent> {
    pub token: Token,
    pub tdata: TokenData,
    pub lex: LexData<L>,
    pub scope: ScopeId,
    pub bindings: Vec<Interned<[u8]>>,
    pub tab: ObjRef<TAB>,
    pub marg: Vec<Interned<[u8]>>,
    pub undef: Vec<ObjRef>,
    pub undef_base: usize,
    pub this: ObjRef,
    pub rec: bool,
    pub bindparams: u8,
    macros: IndexVec<MacroId, Macro>,
    chain: HashMap<(Interned<[u8]>, Namespace), (MacroId, MacroId)>, // stem -> (head, tail)
    stack: Vec<Frame>,
    captures: Vec<Range<u32>>,
    snippet: Vec<u8>,
}

pub type PcxData<'a> = Parser<logos::Lexer<'a, Token>>;
pub type Pcx<'a> = Ccx<PcxData<'a>>;

/* ---- Stringify ----------------------------------------------------------- */

#[derive(Clone, Copy)]
pub enum SequenceType {
    Pattern,  // OpInsert is *not* followed by an index
    Body      // OpInsert is followed by an index
}

const SPACE_BETWEEN: u64 = {
    use Token::*;
    (1 << Ident as u64) | (1 << Dollar as u64) | (1 << CapName as u64) | (1 << CapPos as u64)
        | (1 << Literal as u64) | (1 << Scope as u64) | (1 << Int as u64) | (1 << Int64 as u64)
        | (1 << Fp64 as u64) | (1 << Not as u64) | (1 << Call as u64) | (1 << Macro as u64)
        | (1 << Var as u64) | (1 << Model as u64) | (1 << Table as u64) | (1 << Func as u64)
        | (1 << Where as u64) | (1 << Out as u64) | (1 << Let as u64) | (1 << In as u64)
        | (1 << True as u64) | (1 << False as u64)
};

const TK_DATA: u8 = Token::Literal as _;
const TK_DATALEN: usize = 4;
const TK_CAPTURE: u8 = Token::OpInsert as _;

pub fn stringify(buf: &mut Bump, intern: &InternPtr, body: &[u8], sty: SequenceType) {
    let mut i = 0;
    let mut space = false;
    let mut data = 0;
    while let Some(t) = body.get(i).cloned() {
        let tsp = SPACE_BETWEEN & (1 << t as u64) != 0;
        if space && tsp {
            buf.push(b' ');
        }
        space = tsp;
        i += 1;
        if t < Token::OpInsert as _ {
            let token: Token = unsafe { transmute(t) };
            if token.has_data() {
                data = u32::from_ne_bytes(body[i..i+4].try_into().unwrap());
                i += TK_DATALEN;
            }
            match token {
                tk @ (Token::Ident | Token::Literal | Token::CapName) => {
                    if tk == Token::CapName { buf.push(b'$'); }
                    // TODO: this doesn't properly quote idents or escape quotes in strings.
                    if tk == Token::Literal { buf.push(b'"'); }
                    let data: Interned<[u8]> = zerocopy::transmute!(data);
                    buf.write(&intern[data]);
                    if tk == Token::Literal { buf.push(b'"'); }
                },
                Token::CapPos => {
                    write!(buf, "${}", data).unwrap();
                },
                Token::Scope => {
                    write!(buf, "%{}", data).unwrap();
                },
                Token::Int => write!(buf, "{}", data as i32).unwrap(),
                Token::Int64 => {
                    let data: Interned<i64> = zerocopy::transmute!(data);
                    write!(buf, "{}", intern[data]).unwrap();
                },
                Token::Fp64 => {
                    let data: Interned<f64> = zerocopy::transmute!(data);
                    write!(buf, "{}", intern[data]).unwrap();
                },
                tk => {
                    buf.write(tk.str());
                }
            }
        } else {
            debug_assert!(t == Token::OpInsert as _);
            match sty {
                SequenceType::Pattern => {
                    buf.push(b'$');
                },
                SequenceType::Body => {
                    write!(buf, "${}", body[i]).unwrap();
                    i += 1;
                },
            }
        }
    }
}

/* ---- Error messages ------------------------------------------------------ */

#[derive(Clone, Copy)]
pub enum SyntaxError {
    InvalidToken,
    ExpectedValue,
    ExpectedPrimitive,
    ExpectedType,
    CapNameInTemplate,
    CapPosInBody,
    UndefCap,
    BadImplicitTab
}

impl SyntaxError {

    fn str(self) -> &'static str {
        use SyntaxError::*;
        match self {
            InvalidToken       => "invalid token",
            ExpectedValue      => "expected value",
            ExpectedPrimitive  => "expected scalar type name",
            ExpectedType       => "expected type",
            CapNameInTemplate  => "named capture not allowed in templates",
            CapPosInBody       => "positional capture not allowed in macro body",
            UndefCap           => "undefined capture",
            BadImplicitTab     => "implicit table not allowed here"
        }
    }

}

fn nsname(ns: Namespace) -> &'static str {
    use Namespace::*;
    match ns {
        Var      => "var",
        Table    => "table",
        Snippet  => "snippet",
        Capture  => "capture",
        Template => "template"
    }
}

fn traceback(pcx: &mut Ccx<PcxData, R, R>) {
    use Namespace::*;
    for frame in pcx.data.stack.iter().rev() {
        pcx.tmp.write(nsname(frame.ns));
        pcx.tmp.push(b' ');
        match frame.ns {
            Var | Table | Snippet => {
                let macro_ = &pcx.data.macros[zerocopy::transmute!(frame.this)];
                if !macro_.table_pattern.is_empty() {
                    stringify(
                        &mut pcx.tmp,
                        &pcx.intern,
                        &pcx.intern[macro_.table_pattern],
                        SequenceType::Pattern
                    );
                    pcx.tmp.push(b'.');
                }
                stringify(
                    &mut pcx.tmp,
                    &pcx.intern,
                    &pcx.intern[macro_.name_pattern],
                    SequenceType::Pattern
                );
            },
            Capture => {
                let Range { start, end } = pcx.data.captures[frame.this as usize];
                stringify(
                    &mut pcx.tmp,
                    &pcx.intern,
                    &pcx.intern.as_slice()[start as usize .. end as usize],
                    SequenceType::Body
                );
            },
            Template => {
                let template: Interned<[u8]> = zerocopy::transmute!(frame.this);
                stringify(
                    &mut pcx.tmp,
                    &pcx.intern,
                    &pcx.intern[template],
                    SequenceType::Body
                );
            }
        }
        pcx.tmp.push(b'\n');
    }
    let loc = lex::loc(&pcx.data.lex);
    write!(pcx.tmp, "on line {} col {}", loc.line, loc.col).unwrap();
}

impl<'a> CompileError<PcxData<'a>> for SyntaxError {
    fn report(self, pcx: &mut Ccx<PcxData<'a>, R, R>) {
        let base = pcx.tmp.end();
        write!(pcx.tmp, "syntax error: {}\n", self.str()).unwrap();
        traceback(pcx);
        pcx.host.set_error_bytes(&pcx.tmp[base..]);
        pcx.tmp.truncate(base);
    }
}

#[derive(Clone, Copy)]
pub struct TokenError {
    pub want: EnumSet<Token>
}

impl<'a> CompileError<PcxData<'a>> for TokenError {
    fn report(self, pcx: &mut Ccx<PcxData<'a>, R, R>) {
        let base = pcx.tmp.end();
        write!(pcx.tmp, "unexpected token: `{}` (expected ", pcx.data.token.str()).unwrap();
        let mut comma = "";
        for tok in self.want {
            write!(pcx.tmp, "{}`{}`", comma, tok.str()).unwrap();
            comma = ", ";
        }
        pcx.tmp.write(b")\n");
        traceback(pcx);
        pcx.host.set_error_bytes(&pcx.tmp[base..]);
        pcx.tmp.truncate(base);
    }
}

#[derive(Clone, Copy)]
pub enum DefinitionErrorType {
    Undefined,
    Redefinition
}

pub struct DefinitionError {
    pub ns: Namespace,
    pub body: Interned<[u8]>,
    pub what: DefinitionErrorType
}

impl<'a> CompileError<PcxData<'a>> for DefinitionError {
    fn report(self, pcx: &mut Ccx<PcxData<'a>, R, R>) {
        let base = pcx.tmp.end();
        pcx.tmp.write(match self.what {
            DefinitionErrorType::Undefined => "undefined ",
            DefinitionErrorType::Redefinition => "redefinition of"
        });
        pcx.tmp.write(nsname(self.ns));
        pcx.tmp.write(b": ");
        stringify(
            &mut pcx.tmp,
            &pcx.intern,
            &pcx.intern[self.body],
            SequenceType::Body
        );
        pcx.tmp.push(b'\n');
        traceback(pcx);
        pcx.host.set_error_bytes(&pcx.tmp[base..]);
        pcx.tmp.truncate(base);
    }
}

/* ---- Macros -------------------------------------------------------------- */

fn splitstem(mut name: &[u8]) -> Interned<[u8]> {
    if name[0] == Token::Scope as _ {
        name = &name[5..];
    }
    debug_assert!(name[0] == Token::Ident as _);
    let stem: [u8; TK_DATALEN] = name[1..5].try_into().unwrap();
    zerocopy::transmute!(stem)
}

pub fn defmacro(
    pcx: &mut Pcx,
    ns: Namespace,
    table_pattern: Interned<[u8]>,
    name_pattern: Interned<[u8]>,
    body: Interned<[u8]>
) {
    let parser = &mut *pcx.data;
    let id = parser.macros.push(Macro {
        table_pattern,
        name_pattern,
        body,
        next: None.into()
    });
    let stem = splitstem(&pcx.intern[name_pattern]);
    match parser.chain.entry((stem, ns)) {
        Entry::Occupied(mut e) => {
            let tail = replace(&mut e.get_mut().1, id);
            parser.macros[tail].next = Some(id).into();
        },
        Entry::Vacant(e) => {
            e.insert((id, id));
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct ParenCounter(i64);

impl ParenCounter {

    pub fn token(&mut self, token: Token) {
        self.token_raw(token as _);
    }

    pub fn token_raw(&mut self, token: u8) {
        const LPAREN: u8 = Token::LParen as u8;
        const RPAREN: u8 = Token::RParen as u8;
        const LBRACKET: u8 = Token::LBracket as u8;
        const RBRACKET: u8 = Token::RBracket as u8;
        const LCURLY: u8 = Token::LCurly as u8;
        const RCURLY: u8 = Token::RCurly as u8;
        match token {
             LPAREN   => self.0 += 0x1,
             RPAREN   => self.0 -= 0x1,
             LBRACKET => self.0 += 0x10000,
             RBRACKET => self.0 -= 0x10000,
             LCURLY   => self.0 += 0x100000000,
             RCURLY   => self.0 -= 0x100000000,
            _ => {}
        }
    }

    pub fn balanced(self) -> bool {
        self.0 == 0
    }

}

// adapted from https://research.swtch.com/glob
fn try_match(
    captures: &mut Vec<Range<u32>>,
    candidate: &[u8],
    pattern: &[u8],
    offset: usize
) -> bool {
    let mut cap: Option<(usize, usize, ParenCounter, ParenCounter)> = None;
    let mut px = 0; // NEXT in pattern
    let mut cx = 0; // NEXT in candidate
    let mut pp = ParenCounter::default(); // CURRENT pattern balance
    let mut cp = ParenCounter::default(); // CURRENT candidate balance
    loop {
        let p = pattern.get(px).cloned();
        let c = candidate.get(cx).cloned();
        if p.is_none() && c.is_none() {
            // we are done.
            // finish up pending capture, if any.
            if let Some((_, ccx, _, _)) = cap {
                let s = captures.last_mut().unwrap();
                *s = (offset as u32 + s.start) .. (offset+ccx) as _;
            }
            return true;
        }
        // check pattern only if nesting matches and both sequences have a token available,
        // otherwise the match is guaranteed to fail since either a capture or literal match
        // always consumes a candidate token.
        if pp == cp {
            if let (Some(p), Some(c)) = (p, c) {
                if p >= TK_CAPTURE {
                    debug_assert!(p == TK_CAPTURE);
                    // we can consume any other token except a closing parenthesis.
                    // note that an open parenthesis is fine here.
                    if (Token::RParen | Token::RBracket | Token::RCurly).as_u64_truncated()
                            & (1u64 << c) == 0 {
                        // finish the pending capture if there is one.
                        // the capture ends at the saved starting offset.
                        if let Some((_, ccx, _, _)) = cap {
                            let s = captures.last_mut().unwrap();
                            *s = (offset as u32 + s.start) .. (offset+ccx) as _;
                        }
                        // consume the candidate token and create a new capture.
                        captures.push(Range { start: cx as _, end: 0 });
                        cp.token_raw(c);
                        cx += 1;
                        if c <= TK_DATA {
                            cx += TK_DATALEN;
                        }
                        px += 1;
                        cap = Some((px, cx, pp, cp));
                        continue;
                    }
                } else {
                    if p == c {
                        // consume both tokens.
                        // since pp = cp, we can just update one and then copy.
                        pp.token_raw(p);
                        cp = pp;
                        px += 1;
                        cx += 1;
                        if p > TK_DATA {
                            continue;
                        }
                        // data must match, too.
                        if pattern[px..px+TK_DATALEN] == candidate[cx..cx+TK_DATALEN] {
                            px += TK_DATALEN;
                            cx += TK_DATALEN;
                            continue;
                        }
                    }
                }
            }
        }
        // no match and there is still tokens in at least one of the sequences.
        match cap {
            Some((cpx, ccx, cpp, ccp)) => {
                // return to starting point and consume a candidate token.
                px = cpx;
                pp = cpp;
                cx = ccx;
                cp = ccp;
                if let Some(c) = candidate.get(cx).cloned() {
                    cp.token_raw(c);
                    cx += 1;
                    if c <= TK_DATA {
                        cx += TK_DATALEN;
                    }
                } else {
                    // no more starting points to try.
                    return false;
                }
                cap = Some((px, cx, pp, cp));
            },
            None => {
                // special case: a lonely trailing capture (`'{$cap}`) matches the empty sequence.
                if c.is_none() && &pattern[px..] ==
                    &[Token::Apostrophe as _, Token::LCurly as _, TK_CAPTURE, Token::RCurly as _]
                {
                    captures.push((cx as u32)..(cx as u32));
                    return true;
                }
                // failed and no pending starting point => no match.
                return false;
            }
        }
    }
}


pub fn pushmacro<'a, 'input>(
    parser: &'a mut Parser<logos::Lexer<'input, Token>>,
    intern: &InternPtr,
    ns: Namespace,
    table: Interned<[u8]>,
    name: Interned<[u8]>
) -> Option<&'a mut Frame> {
    let stem = splitstem(&intern[name]);
    let mut id = parser.chain.get(&(stem, ns))?.0;
    let base = parser.captures.len() as _;
    loop {
        let macro_ = &parser.macros[id];
        if try_match(
            &mut parser.captures,
            &intern[table],
            &intern[macro_.table_pattern],
            table.ptr()
        ) && try_match(
            &mut parser.captures,
            &intern[name],
            &intern[macro_.name_pattern],
            name.ptr()
        ) {
            let body = intern.get_range(macro_.body);
            parser.stack.push(Frame {
                base,
                cursor: body.start as _,
                end: body.end as _,
                lookahead: None,
                lookahead_data: 0,
                ns,
                this: zerocopy::transmute!(id)
            });
            return parser.stack.last_mut();
        }
        parser.captures.truncate(base as _);
        id = match macro_.next.unpack() {
            Some(id) => id,
            None     => return None
        };
    }
}

pub fn pushtemplate(pcx: &mut Pcx, template: Interned<[u8]>, cap: &[Interned<[u8]>]) -> compile::Result {
    let parser = &mut *pcx.data;
    let body = pcx.intern.get_range(template);
    parser.stack.push(Frame {
        base: parser.captures.len() as _,
        cursor: body.start as _,
        end: body.end as _,
        lookahead: Some(parser.token),
        lookahead_data: parser.tdata,
        this: zerocopy::transmute!(template),
        ns: Namespace::Template
    });
    parser.captures.extend(cap.iter().map(|&c| {
        let Range { start, end } = pcx.intern.get_range(c);
        start as u32 .. end as u32
    }));
    next(pcx)
}

/* ---- Parsing ------------------------------------------------------------- */

fn parse_name_seq(pcx: &mut Pcx, sty: SequenceType) -> compile::Result<Interned<[u8]>> {
    let base = pcx.tmp.end();
    save(pcx);
    if check(pcx, Token::Scope)? { save(pcx); }
    consume(pcx, Token::Ident)?;
    if pcx.data.token == Token::Apostrophe {
        let subscript = pcx.tmp.end();
        save(pcx);
        next(pcx)?;
        // canonicalize subscripted names to curly brackets, no matter whether brackets are used
        // or what kind.
        pcx.tmp.push(Token::LCurly as u8);
        if (Token::LParen | Token::LBracket | Token::LCurly).contains(pcx.data.token) {
            let mut parens = ParenCounter::default();
            parens.token(pcx.data.token);
            loop {
                next(pcx)?;
                parens.token(pcx.data.token);
                if parens.balanced() { break; }
                savemaybecap(pcx, sty)?;
            }
        } else {
            savemaybecap(pcx, sty)?;
        }
        next(pcx)?; // skip subscript token or closing parenthesis
        if pcx.tmp.end() == subscript.add(2) {
            // canonicalize empty subscript '{} -> no subscript
            pcx.tmp.truncate(subscript);
        } else {
            pcx.tmp.push(Token::RCurly as u8);
        }
    }
    let name = pcx.intern.intern(&pcx.tmp[base..]);
    pcx.tmp.truncate(base);
    Ok(name)
}

pub fn parse_name(pcx: &mut Pcx) -> compile::Result<Interned<[u8]>> {
    parse_name_seq(pcx, SequenceType::Body)
}

pub fn parse_name_pattern(pcx: &mut Pcx) -> compile::Result<Interned<[u8]>> {
    parse_name_seq(pcx, SequenceType::Pattern)
}

fn expandnext(pcx: &mut Pcx) -> Option<Token> {
    let parser = &mut *pcx.data;
    let top = parser.stack.last_mut()?;
    if top.cursor == top.end {
        let lookahead = top.lookahead;
        let data = top.lookahead_data;
        parser.captures.truncate(top.base as _);
        parser.stack.pop();
        return match lookahead {
            Some(token) => {
                parser.tdata = data;
                Some(token)
            },
            None => expandnext(pcx)
        }
    }
    let data = &pcx.intern.as_slice()[top.cursor as usize ..];
    if data[0] < Token::OpInsert as u8 {
        let token: Token = unsafe { transmute(data[0]) };
        parser.token = token;
        top.cursor += 1;
        if token.has_data() {
            parser.tdata = u32::from_ne_bytes(data[1..5].try_into().unwrap());
            top.cursor += TK_DATALEN as u32;
        }
        return Some(token);
    } else {
        debug_assert!(data[0] == Token::OpInsert as u8);
        top.cursor += 2;
        let capno = top.base + data[1] as u32;
        let Range { start, end } = parser.captures[capno as usize];
        parser.stack.push(Frame {
            base: parser.captures.len() as _,
            cursor: start,
            end,
            lookahead: None,
            lookahead_data: 0,
            this: capno,
            ns: Namespace::Capture
        });
        expandnext(pcx)
    }
}

// TODO 1: this should share code with stringify
fn expandstring(pcx: &mut Pcx) {
    let base = pcx.tmp.end();
    let mut space = false;
    loop {
        // this should never return none, because the recorder should never record
        // incomplete strings
        let token = expandnext(pcx).unwrap();
        let tsp = SPACE_BETWEEN & (1 << token as u64) != 0;
        if space && tsp {
            pcx.tmp.push(b' ');
        }
        space = tsp;
        match token {
            Token::OpLiteralBoundary => break,
            Token::Ident | Token::Literal => {
                let ident: Interned<[u8]> = zerocopy::transmute!(pcx.data.tdata);
                pcx.tmp.write(&pcx.intern[ident]);
            },
            Token::Scope => write!(&mut pcx.tmp, "%{}", pcx.data.tdata).unwrap(),
            Token::Int => write!(&mut pcx.tmp, "{}", pcx.data.tdata as i32).unwrap(),
            Token::Int64 => {
                let v = i64::from_ne_bytes(pcx.intern[zerocopy::transmute!(pcx.data.tdata)]);
                write!(&mut pcx.tmp, "{}", v).unwrap();
            },
            Token::Fp64 => {
                let v = f64::from_ne_bytes(pcx.intern[zerocopy::transmute!(pcx.data.tdata)]);
                write!(&mut pcx.tmp, "{}", v).unwrap();
            },
            Token::OpThis => todo!(),
            // Token::OpThis => pushcap(&mut parser.macros,
            //     parser.builder.graph.vars[parser.this].name),
            tok => { pcx.tmp.write(tok.str()); }
        }
    }
    let data: &[u8] = &pcx.tmp[base..];
    pcx.data.tdata = zerocopy::transmute!(pcx.intern.intern(data));
    pcx.tmp.truncate(base);
}

fn nexttoken(pcx: &mut Pcx) -> compile::Result<Token> {
    match expandnext(pcx) {
        Some(Token::OpLiteralBoundary) => {
            expandstring(pcx);
            Ok(Token::Literal)
        },
        Some(token) => Ok(token),
        None => lex::next(pcx)
    }
}

pub fn next(pcx: &mut Pcx) -> compile::Result {
    match nexttoken(pcx)? {
        Token::Tilde if !pcx.data.rec => {
            next(pcx)?;
            let name = parse_name(pcx)?;
            let Parser { token, tdata: data, .. } = *pcx.data;
            match pushmacro(&mut pcx.data, &pcx.intern, Namespace::Snippet, Interned::EMPTY, name) {
                Some(frame) => {
                    frame.lookahead = Some(token);
                    frame.lookahead_data = data;
                    next(pcx)
                },
                None => pcx.error(DefinitionError {
                    ns: Namespace::Snippet,
                    body: name,
                    what: DefinitionErrorType::Undefined
                })
            }
        },
        token => {
            pcx.data.token = token;
            Ok(())
        }
    }
}

pub fn check(pcx: &mut Pcx, token: Token) -> compile::Result<bool> {
    Ok(if pcx.data.token == token {
        next(pcx)?;
        true
    } else {
        false
    })
}

pub fn require(pcx: &mut Pcx, token: Token) -> compile::Result<u32> {
    if pcx.data.token == token {
        Ok(pcx.data.tdata)
    } else {
        pcx.error(TokenError { want: token.into() })
    }
}

pub fn consume(pcx: &mut Pcx, token: Token) -> compile::Result<u32> {
    let data = require(pcx, token)?;
    next(pcx)?;
    Ok(data)
}

pub fn save(pcx: &mut Pcx) {
    pcx.tmp.push(pcx.data.token as u8);
    if pcx.data.token.has_data() {
        // don't push `tdata` directly here, this write must be unaligned
        pcx.tmp.push(pcx.data.tdata.to_ne_bytes());
    }
}

fn savemaybecap(pcx: &mut Pcx, sty: SequenceType) -> compile::Result {
    match (pcx.data.token, sty) {
        (Token::CapName, SequenceType::Pattern) => {
            pcx.tmp.push(Token::OpInsert as u8);
            let parser = &mut *pcx.data;
            parser.marg.push(zerocopy::transmute!(parser.tdata));
        },
        (Token::CapPos|Token::Dollar, SequenceType::Pattern) => {
            // TODO: report error (only named captures are allowed here)
            todo!()
        },
        _ => save(pcx)
    }
    Ok(())
}

pub fn parse<'a,F,R>(ccx: &'a mut Ccx<Parser>, input: &'a [u8], func: F) -> compile::Result<R>
    where F: FnOnce(&mut Pcx<'a>) -> compile::Result<R>
{
    // safety: parser contains LexData<Absent>, ie. no lexer
    let pcx: &mut Pcx = unsafe {
        core::ptr::write(
            &mut ccx.data.lex as *mut _ as *mut logos::Lexer<'a, Token>,
            Token::lexer(input)
        );
        transmute(ccx)
    };
    #[cfg(feature="trace")] let start = pcx.objs.end();
    let result = next(pcx).and_then(|_| func(&mut *pcx));
    #[cfg(feature="trace")]
    if start != pcx.objs.end() && crate::trace::trace!(PARSE) {
        crate::trace::trace!(
            PARSE "{:04}...{:04}:",
            {let o: u32 = zerocopy::transmute!(start); o},
            {let o: u32 = zerocopy::transmute!(pcx.objs.end()); o}
        );
        crate::dump::trace_objs(&pcx.intern, &pcx.objs, start);
    }
    // safety: pcx contains a valid lexer
    unsafe { core::ptr::drop_in_place(&mut pcx.data.lex) }
    result
}

/* -------------------------------------------------------------------------- */

impl Stage for Parser {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Self {
            token: Token::Eof,
            tdata: Default::default(),
            lex: Default::default(),
            scope: ScopeId(0),
            bindings: Default::default(),
            tab: ObjRef::NIL.cast(),
            marg: Default::default(),
            macros: Default::default(),
            chain: Default::default(),
            undef: Default::default(),
            undef_base: Default::default(),
            this: ObjRef::NIL,
            stack: Default::default(),
            captures: Default::default(),
            snippet: Default::default(),
            rec: false,
            bindparams: 0
        })
    }

}
