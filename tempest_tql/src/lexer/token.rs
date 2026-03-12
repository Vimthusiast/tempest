use std::borrow::Cow;

use derive_more::Display;
use logos::Logos;

#[derive(Debug, Display, Clone, PartialEq, Eq, Logos)]
#[logos(skip(r"[ \t\n\f]+"))]
pub(crate) enum Token<'a> {
    // -- keywords --

    // type definitions
    #[token("type")]
    Type,

    // create statement
    #[token("create")]
    Create,
    #[token("database")]
    Database,
    #[token("table")]
    Table,
    #[token("primary")]
    Primary,
    #[token("key")]
    Key,

    // insert statement
    #[token("insert")]
    Insert,
    #[token("into")]
    Into,
    #[token("values")]
    Values,

    // select statement
    #[token("select")]
    Select,
    #[token("from")]
    From,
    #[token("where")]
    Where,
    #[token("and")]
    And,
    #[token("or")]
    Or,

    // other keywords
    #[token("true")]
    True,
    #[token("false")]
    False,

    // -- punctuation --
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(".")]
    Dot,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,

    // -- operators --
    #[token("*")]
    Asterisk, // operator for multiply and used to select all rows
    #[token("=")]
    Eq,
    #[token(">")]
    Gt,
    #[token("<")]
    Lt,
    #[token(">=")]
    Gte,
    #[token("<=")]
    Lte,

    // literals
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| Cow::Borrowed(lex.slice()))]
    Identifier(Cow<'a, str>),
    #[regex(r"-?[0-9]+", |lex| Cow::Borrowed(lex.slice()))]
    IntegerLiteral(Cow<'a, str>),
    #[regex(r#""[^"]*""#, |lex| {
        let slice = lex.slice();
        // trim the leading and trailing quotes
        Cow::Borrowed(&slice[1..slice.len()-1])
    })]
    StringLiteral(Cow<'a, str>),
}

impl<'a> Token<'a> {
    pub(crate) fn into_static(self) -> Token<'static> {
        match self {
            Self::Identifier(ident) => Token::Identifier(Cow::Owned(ident.into_owned())),
            Self::IntegerLiteral(lit) => Token::IntegerLiteral(Cow::Owned(lit.into_owned())),
            Self::StringLiteral(lit) => Token::StringLiteral(Cow::Owned(lit.into_owned())),
            // SAFETY: all the other variants are not bound to 'a, so it's safe to transmute the
            // lifetime here, to avoid having to spell out all the other variants
            other => unsafe { std::mem::transmute(other) },
        }
    }
}
