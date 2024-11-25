//! Parser and macro engine.

use core::fmt::Write;
use core::mem::{transmute, ManuallyDrop};
use core::ops::Range;

use alloc::vec::Vec;
use enumset::EnumSet;
use logos::Logos;

use crate::bytestring::ByteString;
use crate::compile::{self, Ccx, Phase};
use crate::hash::HashMap;
use crate::index::{index, IndexOption, IndexVec};
use crate::intern::{Intern, IRef};
use crate::lex::{self, Token};
use crate::obj::{ObjRef, EXPR, TAB};
use crate::typestate::{typestate_union, Absent};

index!(pub struct ScopeId(u32) invalid(!0));
index!(struct MacroId(u32) invalid(!0));

pub struct Binding {
    pub name: IRef<[u8]>,
    pub value: ObjRef<EXPR>
}

struct Macro {
    table_pattern: IRef<[u8]>, // only for model/var
    name_pattern: IRef<[u8]>,
    body: IRef<[u8]>,
    next: IndexOption<MacroId> // next with same namespace and stem
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Namespace {
    Model,
    Var,
    Func,
    Table,
    Snippet,
    // the following are only used for debug messages:
    Capture,
    Template
}

pub type TokenData = u32;

struct Frame {
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
    pub bindings: Vec<Binding>,
    pub tab: ObjRef<TAB>,
    pub marg: Vec<IRef<[u8]>>,
    pub rec: bool,
    macros: IndexVec<MacroId, Macro>,
    chain: HashMap<(IRef<[u8]>, Namespace), (MacroId, MacroId)>, // stem -> (head, tail)
    stack: Vec<Frame>,
    captures: Vec<Range<u32>>,
    snippet: Vec<u8>,
}

pub type Pcx<'a> = Ccx<Parser<logos::Lexer<'a, Token>>>;

#[derive(Clone, Copy)]
pub enum SyntaxError {
    InvalidToken,
    ExpectedValue,
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
            CapNameInTemplate  => "named capture not allowed in templates",
            CapPosInBody       => "positional capture not allowed in macro body",
            UndefCap           => "undefined capture",
            BadImplicitTab     => "implicit table not allowed here"
        }
    }

}

#[derive(Clone, Copy)]
pub enum SequenceType {
    Pattern,  // OpInsert is *not* followed by an index
    Body      // OpInsert is followed by an index
}

const SPACE_BETWEEN: u64 = (1 << Token::Ident as u64)
    | (1 << Token::Dollar as u64)
    | (1 << Token::CapName as u64)
    | (1 << Token::CapPos as u64)
    | (1 << Token::Literal as u64)
    | (1 << Token::Scope as u64)
    | (1 << Token::Int as u64)
    | (1 << Token::Int64 as u64)
    | (1 << Token::Fp64 as u64);

const TK_DATA: u8 = Token::Literal as _;
const TK_DATALEN: usize = 4;
const TK_CAPTURE: u8 = Token::OpInsert as _;

pub fn stringify(buf: &mut ByteString, intern: &Intern, body: &[u8], sty: SequenceType) {
    let mut i = 0;
    let mut space = false;
    let mut data = 0;
    while let Some(t) = body.get(i).cloned() {
        let tsp = SPACE_BETWEEN & (1 << t as u64) != 0;
        if space && tsp {
            buf.push(' ');
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
                    if tk == Token::CapName { buf.push('$'); }
                    // TODO: this doesn't properly quote idents or escape quotes in strings.
                    if tk == Token::Literal { buf.push('"'); }
                    buf.push_bytes(intern.get_slice(zerocopy::transmute!(data)));
                    if tk == Token::Literal { buf.push('"'); }
                },
                Token::CapPos => {
                    write!(buf, "${}", data).unwrap();
                },
                Token::Scope => {
                    write!(buf, "%{}", data).unwrap();
                },
                Token::Int => write!(buf, "{}", data as i32).unwrap(),
                Token::Int64 => {
                    let v = i64::from_ne_bytes(intern[zerocopy::transmute!(data)]);
                    write!(buf, "{}", v).unwrap();
                },
                Token::Fp64 => {
                    let v = f64::from_ne_bytes(intern[zerocopy::transmute!(data)]);
                    write!(buf, "{}", v).unwrap();
                },
                tk => {
                    buf.push_str(tk.str());
                }
            }
        } else {
            debug_assert!(t == Token::OpInsert as _);
            match sty {
                SequenceType::Pattern => buf.push('$'),
                SequenceType::Body => {
                    write!(buf, "${}", body[i]).unwrap();
                    i += 1;
                },
            }
        }
    }
}

fn nsname(ns: Namespace) -> &'static str {
    use Namespace::*;
    match ns {
        Model    => "model",
        Var      => "var",
        Func     => "func",
        Table    => "table",
        Snippet  => "snippet",
        Capture  => "capture",
        Template => "template"
    }
}

fn traceback(pcx: &mut Pcx) {
    use Namespace::*;
    for frame in pcx.data.stack.iter().rev() {
        pcx.host.buf.push_str(nsname(frame.ns));
        pcx.host.buf.push(' ');
        match frame.ns {
            Model | Var | Func | Table | Snippet => {
                let macro_ = &pcx.data.macros[zerocopy::transmute!(frame.this)];
                if macro_.table_pattern != IRef::EMPTY {
                    stringify(
                        &mut pcx.host.buf,
                        &pcx.intern,
                        pcx.intern.get_slice(macro_.table_pattern.cast()),
                        SequenceType::Pattern
                    );
                    pcx.host.buf.push('.');
                }
                stringify(
                    &mut pcx.host.buf,
                    &pcx.intern,
                    pcx.intern.get_slice(macro_.name_pattern.cast()),
                    SequenceType::Pattern
                );
            },
            Capture => {
                let Range { start, end } = pcx.data.captures[frame.this as usize];
                stringify(
                    &mut pcx.host.buf,
                    &pcx.intern,
                    &pcx.intern.bump().as_slice()[start as usize .. end as usize],
                    SequenceType::Body
                );
            },
            Template => {
                let template: IRef<[u8]> = zerocopy::transmute!(frame.this);
                stringify(
                    &mut pcx.host.buf,
                    &pcx.intern,
                    &pcx.intern.get_slice(template),
                    SequenceType::Body
                );
            }
        }
        pcx.host.buf.push('\n');
    }
    let loc = lex::loc(&pcx.data.lex);
    write!(pcx.host.buf, "on line {} col {}", loc.line, loc.col).unwrap();
}

#[cold]
fn syntaxerr_(pcx: &mut Pcx, error: SyntaxError) {
    pcx.host.buf.clear();
    write!(pcx.host.buf, "syntax error: {}\n", error.str()).unwrap();
    traceback(pcx);
}

pub fn syntaxerr<T>(pcx: &mut Pcx, error: SyntaxError) -> compile::Result<T> {
    syntaxerr_(pcx, error);
    Err(())
}

#[cold]
fn tokenerr_(pcx: &mut Pcx, want: EnumSet<Token>) {
    pcx.host.buf.clear();
    write!(pcx.host.buf, "unexpected token: `{}` (expected ", pcx.data.token.str()).unwrap();
    let mut comma = "";
    for tok in want {
        write!(pcx.host.buf, "{}`{}`", comma, tok.str()).unwrap();
        comma = ", ";
    }
    pcx.host.buf.push_str(")\n");
    traceback(pcx)
}

pub fn tokenerr<T>(pcx: &mut Pcx, want: impl Into<EnumSet<Token>>) -> compile::Result<T> {
    tokenerr_(pcx, want.into());
    Err(())
}

#[cold]
fn xdeferr_(pcx: &mut Pcx, ns: Namespace, body: IRef<[u8]>, what: &str) {
    pcx.host.buf.clear();
    pcx.host.buf.push_str(what);
    pcx.host.buf.push_str(nsname(ns));
    stringify(
        &mut pcx.host.buf,
        &pcx.intern,
        pcx.intern.get_slice(body.cast()),
        SequenceType::Body
    );
    pcx.host.buf.push('\n');
    traceback(pcx)
}

pub fn undeferr<T>(pcx: &mut Pcx, ns: Namespace, body: IRef<[u8]>) -> compile::Result<T> {
    xdeferr_(pcx, ns, body, "undefined ");
    Err(())
}

pub fn redeferr<T>(pcx: &mut Pcx, ns: Namespace, body: IRef<[u8]>) -> compile::Result<T> {
    xdeferr_(pcx, ns, body, "redefinition of ");
    Err(())
}

#[cold]
fn langerr_(pcx: &mut Pcx) {
    pcx.host.buf.clear();
    pcx.host.buf.push_str("unsupported language: ");
    pcx.host.buf.push_bytes(pcx.intern.get_slice(zerocopy::transmute!(pcx.data.tdata)));
}

pub fn langerr<T>(pcx: &mut Pcx) -> compile::Result<T> {
    langerr_(pcx);
    Err(())
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
pub fn try_match(
    captures: &mut Vec<Range<u32>>,
    intern: &Intern,
    candidate: IRef<[u8]>,
    pattern: &[u8]
) -> bool {
    let candidate = intern.get_range(candidate.cast());
    let cand = &intern.bump().as_slice()[candidate.clone()];
    let mut cap: Option<(usize, usize, ParenCounter, ParenCounter)> = None;
    let mut px = 0; // NEXT in pattern
    let mut cx = 0; // NEXT in candidate
    let mut pp = ParenCounter::default(); // CURRENT pattern balance
    let mut cp = ParenCounter::default(); // CURRENT candidate balance
    loop {
        let p = pattern.get(px).cloned();
        let c = cand.get(cx).cloned();
        if p.is_none() && c.is_none() {
            // we are done.
            // finish up pending capture, if any.
            if let Some((_, ccx, _, _)) = cap {
                let s = captures.last_mut().unwrap();
                *s = (candidate.start as u32 + s.start) .. (candidate.start+ccx) as _;
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
                            *s = (candidate.start as u32 + s.start) .. (candidate.start+ccx) as _;
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
                        if pattern[px..px+TK_DATALEN] == cand[cx..cx+TK_DATALEN] {
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
                if let Some(c) = cand.get(cx).cloned() {
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
                // failed and no pending starting point => no match.
                return false;
            }
        }
    }
}

fn splitstem(name: &[u8]) -> IRef<[u8]> {
    debug_assert!(name[0] == Token::Ident as _);
    let stem: [u8; TK_DATALEN] = name[1..5].try_into().unwrap();
    zerocopy::transmute!(stem)
}

fn pushmacro<'a, 'input>(
    pcx: &'a mut Pcx<'input>,
    ns: Namespace,
    table: IRef<[u8]>,
    name: IRef<[u8]>
) -> Option<&'a mut Frame> {
    let stem = splitstem(pcx.intern.get_slice(name.cast()));
    let parser = &mut *pcx.data;
    let mut id = parser.chain.get(&(stem, ns))?.0;
    let base = parser.captures.len() as _;
    loop {
        let macro_ = &parser.macros[id];
        if try_match(
            &mut parser.captures,
            &pcx.intern,
            table,
            pcx.intern.get_slice(macro_.table_pattern.cast()),
        ) && try_match(
            &mut parser.captures,
            &pcx.intern,
            name,
            pcx.intern.get_slice(macro_.name_pattern.cast())
        ) {
            let body = pcx.intern.get_range(macro_.body.cast());
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

pub fn pushtemplate(pcx: &mut Pcx, template: IRef<[u8]>, cap: &[IRef<[u8]>]) -> compile::Result {
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

fn snipname(pcx: &mut Pcx) -> compile::Result<IRef<[u8]>> {
    let parser = &mut *pcx.data;
    let base = parser.snippet.len();
    if parser.token == Token::Scope {
        parser.snippet.push(Token::Scope as _);
        parser.snippet.extend_from_slice(&parser.tdata.to_ne_bytes());
        next(pcx)?;
    }
    require(pcx, Token::Ident)?;
    let parser = &mut *pcx.data;
    parser.snippet.push(Token::Ident as _);
    parser.snippet.extend_from_slice(&parser.tdata.to_ne_bytes());
    next(pcx)?;
    let mut token = pcx.data.token;
    if token == Token::LCurly {
        let mut parens = ParenCounter::default();
        loop {
            parens.token(token);
            pcx.data.snippet.push(token as _);
            if token.has_data() {
                let parser = &mut *pcx.data;
                parser.snippet.extend_from_slice(&parser.tdata.to_ne_bytes());
            }
            next(pcx)?;
            if token == Token::RCurly && parens.balanced() { break; }
            token = pcx.data.token;
        }
    }
    let id = pcx.intern.intern(&pcx.data.snippet[base..]).cast();
    pcx.data.snippet.truncate(base);
    Ok(id)
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
    let data = &pcx.intern.bump().as_slice()[top.cursor as usize ..];
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

fn expandstring(pcx: &mut Pcx) {
    let start = pcx.intern.bump().end();
    loop {
        // this should never return none, because the recorder should never record
        // incomplete strings
        match expandnext(pcx).unwrap() {
            Token::OpLiteralBoundary => break,
            Token::Ident | Token::Literal => pcx.intern.write_ref(
                zerocopy::transmute!(pcx.data.tdata)),
            Token::Scope => write!(&mut pcx.intern, "%{}", pcx.data.tdata).unwrap(),
            Token::Int => write!(&mut pcx.intern, "{}", pcx.data.tdata as i32).unwrap(),
            Token::Int64 => {
                let v = i64::from_ne_bytes(pcx.intern[zerocopy::transmute!(pcx.data.tdata)]);
                write!(&mut pcx.intern, "{}", v).unwrap();
            },
            Token::Fp64 => {
                let v = f64::from_ne_bytes(pcx.intern[zerocopy::transmute!(pcx.data.tdata)]);
                write!(&mut pcx.intern, "{}", v).unwrap();
            },
            Token::OpThis => todo!(),
            // Token::OpThis => pushcap(&mut parser.macros,
            //     parser.builder.graph.vars[parser.this].name),
            tok => pcx.intern.write(tok.str())
        }
    }
    pcx.data.tdata = zerocopy::transmute!(pcx.intern.intern_consume_from(start));
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
            let name = snipname(pcx)?;
            let Parser { token, tdata: data, .. } = *pcx.data;
            match pushmacro(pcx, Namespace::Snippet, IRef::EMPTY, name) {
                Some(frame) => {
                    frame.lookahead = Some(token);
                    frame.lookahead_data = data;
                    next(pcx)
                },
                None => undeferr(pcx, Namespace::Snippet, name)
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

pub fn require(pcx: &mut Pcx, token: Token) -> compile::Result {
    if pcx.data.token == token {
        Ok(())
    } else {
        tokenerr(pcx, token)
    }
}

pub fn consume(pcx: &mut Pcx, token: Token) -> compile::Result {
    require(pcx, token)?;
    next(pcx)
}

pub fn save(pcx: &mut Pcx) {
    pcx.tmp.push(pcx.data.token as u8);
    if pcx.data.token.has_data() {
        // don't push `tdata` directly here, this write must be unaligned
        pcx.tmp.push(pcx.data.tdata.to_ne_bytes());
    }
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

impl Phase for Parser {

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
            stack: Default::default(),
            captures: Default::default(),
            snippet: Default::default(),
            rec: false
        })
    }

}
