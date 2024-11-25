//! Lexical analysis

use core::str;

use enumset::EnumSetType;
use logos::{Logos, Skip};

use crate::compile;
use crate::parser::{syntaxerr, Pcx, SyntaxError};

#[derive(Debug)]
pub struct SourceLocation {
    pub line: u32,
    pub col: u32
}

impl Default for SourceLocation {

    fn default() -> Self {
        Self { line: 1, col: 0 }
    }

}

fn lex_newline(lex: &mut logos::Lexer<'_, Token>) -> Skip {
    lex.extras.line += 1;
    lex.extras.col = lex.span().start as _;
    Skip
}

#[derive(Logos, EnumSetType, Debug)]
#[logos(extras=SourceLocation)]
#[logos(source=[u8])]
#[logos(skip r"[\t\v\f\r ]")]
#[logos(skip "#[^\n]*")]
#[repr(u8)]
pub enum Token {

    // NOTE: ensure Token has at most 64 variants, so that EnumSet<Token> is 64 bits.

    /* ---- data-carrying tokens ------------------------------------------------ */

    Int,     // data = signed int literal
    Int64,   // data = intern kref8
    Fp64,    // data = intern kref8

    #[regex(r"[[:alpha:]_][[:word:]]*")]
    #[regex(r"`([^`]*)`")]
    Ident,   // data = intern ref

    #[regex(r"\$[[:alpha:]_][[:word:]]*")]
    #[regex(r"\$`([^`]*)`")]
    CapName, // data = intern ref

    #[regex(r"\$[[:digit:]]+")]
    CapPos,   // data = int literal

    #[regex(r"%[[:digit:]]*")]
    Scope,   // data = int literal

    #[regex(r#""([^"]*)""#)]
    Literal, // data = intern ref

    /* ---- symbols and keywords ------------------------------------------------ */

    // binary operators. ORDER BINOP.
    #[token("or")]        Or,
    #[token("and")]       And,
    #[token("+")]         Plus,
    #[token("-")]         Minus,
    #[token("*")]         Asterisk,
    #[token("/")]         Slash,
    #[token("^")]         Caret,
    #[token("=")]         Eq,
    #[token("!=")]        Ne,
    #[token("<")]         Lt,
    #[token("<=")]        Le,
    #[token(">")]         Gt,
    #[token(">=")]        Ge,

    // punctuation
    #[token(",")]         Comma,
    #[token("(")]         LParen,
    #[token(")")]         RParen,
    #[token("[")]         LBracket,
    #[token("]")]         RBracket,
    #[token("{")]         LCurly,
    #[token("}")]         RCurly,
    #[token(":")]         Colon,
    #[token("~")]         Tilde,
    #[token(".")]         Dot,
    #[token("'")]         Apostrophe,
    #[token("$")]         Dollar,
    #[token("..")]        DotDot,
    #[token("##")]        HashHash,
    #[token("$$")]        DollarDollar,

    // keywords
    #[token("not")]       Not,
    #[token("call")]      Call,
    #[token("macro")]     Macro,
    #[token("model")]     Model,
    #[token("table")]     Table,
    #[token("func")]      Func,
    #[token("where")]     Where,
    #[token("intrinsic")] Intrinsic,
    #[token("let")]       Let,
    #[token("in")]        In,
    #[token("true")]      True,
    #[token("false")]     False,

    /* ---- pseudo tokens ------------------------------------------------------- */

    #[regex(r"0x[[:digit:]a-fA-F]+")]
    NumHex,

    #[token("inf")]
    #[regex(r"(?:(?:[[:digit:]]+(?:\.[[:digit:]]*)?)|(?:\.[[:digit:]]+))(?:[eE]-?[[:digit:]+])?")]
    Num,

    #[token("\n", lex_newline)]
    Newline,

    Eof,
    OpThis,
    OpLiteralBoundary,

    // must be last
    OpInsert,

}

impl Token {

    pub fn has_data(self) -> bool {
        (self as u8) <= (Self::Literal as u8)
    }

    pub fn is_binop(self) -> bool {
        (self as u8).wrapping_sub(Token::Or as _) <= (Token::Ge as u8 - Token::Or as u8)
    }

    pub fn str(self) -> &'static str {
        use Token::*;
        match self {
            Plus       => "+",
            Minus      => "-",
            Asterisk   => "*",
            Slash      => "/",
            Caret      => "^",
            Eq         => "=",
            Lt         => "<",
            Gt         => ">",
            Comma      => ",",
            LParen     => "(",
            RParen     => ")",
            LBracket   => "[",
            RBracket   => "]",
            LCurly     => "{",
            RCurly     => "}",
            Colon      => ":",
            Tilde      => "~",
            Le         => "<=",
            Ge         => ">=",
            Ne         => "!=",
            DotDot     => "..",
            HashHash   => "##",
            DollarDollar => "$$",
            Dot        => ".",
            Apostrophe => "'",
            Dollar     => "$",
            Call       => "call",
            Macro      => "macro",
            Model      => "model",
            Table      => "table",
            Func       => "func",
            Where      => "where",
            Intrinsic  => "intrinsic",
            Let        => "let",
            In         => "in",
            And        => "and",
            Or         => "or",
            Not        => "not",
            True       => "true",
            False      => "false",
            Newline    => "\n",
            Num | NumHex | Int | Int64 | Fp64 => "<num>",
            Ident      => "<ident>",
            CapName | CapPos => "<capture>",
            Scope      => "<scope>",
            Literal    => "<literal>",
            Eof        => "<eof>",
            OpThis     => "$$",
            OpLiteralBoundary => "\"",
            OpInsert   => "$",
        }
    }

}

fn internid(pcx: &mut Pcx, ofs: usize) {
    let mut id = &pcx.data.lex.slice()[ofs..];
    if id.get(0).cloned() == Some('`' as _) {
        id = &id[1..id.len()-1];
    }
    pcx.data.tdata = zerocopy::transmute!(pcx.constants.intern(id));
}

fn internint(pcx: &mut Pcx, v: i64) -> Token {
    let (token, data) = if (v as i32) as i64 == v {
        (Token::Int, v as _)
    } else {
        (Token::Int64, zerocopy::transmute!(pcx.constants.intern(&v.to_ne_bytes())))
    };
    pcx.data.tdata = data;
    token
}

fn internfloat(pcx: &mut Pcx, v: f64) -> Token {
    if (v as i64) as f64 == v {
        internint(pcx, v as i64)
    } else {
        pcx.data.tdata = zerocopy::transmute!(pcx.constants.intern(&v.to_ne_bytes()));
        Token::Fp64
    }
}

pub fn next(pcx: &mut Pcx) -> compile::Result<Token> {
    let parser = &mut *pcx.data;
    let mut token = match parser.lex.next() {
        Some(Ok(token)) => token,
        Some(_)         => return syntaxerr(pcx, SyntaxError::InvalidToken),
        None            => return Ok(Token::Eof)
    };
    match token {
        Token::NumHex => {
            let v = i64::from_str_radix(
                // safety: pattern accepts only valid utf8
                unsafe { str::from_utf8_unchecked(&parser.lex.slice()[2..]) },
                16
            ).unwrap();
            token = internint(pcx, v);
        },
        Token::Num => {
            // safety: pattern accepts only valid utf8
            let slice = unsafe { str::from_utf8_unchecked(parser.lex.slice()) };
            token = match slice.parse() {
                Ok(v) => internfloat(pcx, v),
                _     => internint(pcx, slice.parse().unwrap())
            };
        },
        Token::Ident => {
            internid(pcx, 0);
        },
        Token::CapName => {
            internid(pcx, 1);
        },
        Token::CapPos => {
            // safety: pattern accepts only valid utf8
            parser.tdata = unsafe { str::from_utf8_unchecked(&parser.lex.slice()[1..]) }
                .parse().unwrap();
        },
        Token::Scope => {
            let s = parser.lex.slice();
            parser.tdata = if s.len() > 1 {
                // safety: pattern accepts only valid utf8
                unsafe { str::from_utf8_unchecked(&s[1..]) }.parse().unwrap()
            } else {
                zerocopy::transmute!(parser.scope)
            };
        },
        Token::Literal => {
            let s = parser.lex.slice();
            parser.tdata = zerocopy::transmute!(pcx.constants.intern(&s[1..s.len()-1]));
        },
        _ => {}
    }
    Ok(token)
}

pub fn loc(lex: &logos::Lexer<'_,  Token>) -> SourceLocation {
    let linestart = &lex.extras;
    SourceLocation {
        line: linestart.line,
        col: lex.span().start as u32 - linestart.col
    }
}
