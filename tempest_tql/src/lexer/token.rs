use std::borrow::Cow;

use derive_more::Display;
use logos::Logos;
use strum::IntoStaticStr;
use tempest_core::tempest_str::TempestStr;

#[derive(Debug, Display, Clone, PartialEq, Eq, Logos, IntoStaticStr)]
#[logos(skip(r"[ \t\n\f]+"))]
pub enum Token<'a> {
    // -- keywords --

    // type definitions
    #[strum(serialize = "`type`")]
    #[token("type")]
    Type,

    // create statement
    #[strum(serialize = "`create`")]
    #[token("create")]
    Create,
    #[strum(serialize = "`database`")]
    #[token("database")]
    Database,
    #[strum(serialize = "`table`")]
    #[token("table")]
    Table,
    #[strum(serialize = "`primary`")]
    #[token("primary")]
    Primary,
    #[strum(serialize = "`key`")]
    #[token("key")]
    Key,

    // insert statement
    #[strum(serialize = "`insert`")]
    #[token("insert")]
    Insert,
    #[strum(serialize = "`into`")]
    #[token("into")]
    Into,
    #[strum(serialize = "`values`")]
    #[token("values")]
    Values,

    // select statement
    #[strum(serialize = "`select`")]
    #[token("select")]
    Select,
    #[strum(serialize = "`from`")]
    #[token("from")]
    From,
    #[strum(serialize = "`where`")]
    #[token("where")]
    Where,
    #[strum(serialize = "`and`")]
    #[token("and")]
    And,
    #[strum(serialize = "`or`")]
    #[token("or")]
    Or,

    // other keywords
    #[strum(serialize = "`true`")]
    #[token("true")]
    True,
    #[strum(serialize = "`false`")]
    #[token("false")]
    False,

    // -- punctuation --
    #[strum(serialize = "`(`")]
    #[token("(")]
    LParen,
    #[strum(serialize = "`)`")]
    #[token(")")]
    RParen,
    #[strum(serialize = "`{`")]
    #[token("{")]
    LBrace,
    #[strum(serialize = "`}`")]
    #[token("}")]
    RBrace,
    #[strum(serialize = "`.`")]
    #[token(".")]
    Dot,
    #[strum(serialize = "`,`")]
    #[token(",")]
    Comma,
    #[strum(serialize = "`:`")]
    #[token(":")]
    Colon,
    #[strum(serialize = "`::`")]
    #[token("::")]
    DoubleColon,
    #[strum(serialize = "`;`")]
    #[token(";")]
    Semicolon,

    // -- operators --
    #[strum(serialize = "`*`")]
    #[token("*")]
    Asterisk, // operator for multiply and used to select all rows
    #[strum(serialize = "`=`")]
    #[token("=")]
    Eq,
    #[strum(serialize = "`>`")]
    #[token(">")]
    Gt,
    #[strum(serialize = "`<`")]
    #[token("<")]
    Lt,
    #[strum(serialize = "`>=`")]
    #[token(">=")]
    Gte,
    #[strum(serialize = "`<=`")]
    #[token("<=")]
    Lte,

    // -- literals --
    #[strum(serialize = "identifier")]
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| {
        TempestStr::from_borrowed(lex.slice())
            .expect("identifier tokens are guranteed null-free by the lexer")
    })]
    Identifier(TempestStr<'a>),
    #[strum(serialize = "integer literal")]
    #[regex(r"-?[0-9]+", |lex| Cow::Borrowed(lex.slice()))]
    IntegerLiteral(Cow<'a, str>),
    #[strum(serialize = "string literal")]
    #[regex(r#""[^"]*""#, |lex| {
        let slice = lex.slice();
        // trim the leading and trailing quotes
        Cow::Borrowed(&slice[1..slice.len()-1])
    })]
    StringLiteral(Cow<'a, str>),

    // -- end of file token --
    Eof,
}

impl<'a> Token<'a> {
    pub(crate) fn into_static(self) -> Token<'static> {
        match self {
            Self::Create => Token::Create,
            Self::Database => Token::Database,
            Self::Table => Token::Table,
            Self::Type => Token::Type,
            Self::Primary => Token::Primary,
            Self::Key => Token::Key,
            Self::Insert => Token::Insert,
            Self::Into => Token::Into,
            Self::Values => Token::Values,

            Self::Select => Token::Select,
            Self::From => Token::From,
            Self::Where => Token::Where,
            Self::And => Token::And,
            Self::Or => Token::Or,

            Self::True => Token::True,
            Self::False => Token::False,

            Self::LParen => Token::LParen,
            Self::RParen => Token::RParen,
            Self::LBrace => Token::LBrace,
            Self::RBrace => Token::RBrace,
            Self::Dot => Token::Dot,
            Self::Comma => Token::Comma,
            Self::Colon => Token::Colon,
            Self::DoubleColon => Token::DoubleColon,
            Self::Semicolon => Token::Semicolon,

            Self::Asterisk => Token::Asterisk,
            Self::Eq => Token::Eq,
            Self::Gt => Token::Gt,
            Self::Lt => Token::Lt,
            Self::Gte => Token::Gte,
            Self::Lte => Token::Lte,

            Self::Identifier(ident) => Token::Identifier(ident.into_owned()),
            Self::IntegerLiteral(lit) => Token::IntegerLiteral(Cow::Owned(lit.into_owned())),
            Self::StringLiteral(lit) => Token::StringLiteral(Cow::Owned(lit.into_owned())),

            Self::Eof => Token::Eof,
        }
    }

    pub(crate) fn name(&self) -> &'static str {
        self.into()
    }

    pub(crate) const fn empty_ident() -> Token<'static> {
        Token::Identifier(unsafe { TempestStr::from_borrowed_unchecked("") })
    }

    pub(crate) const fn empty_string() -> Token<'static> {
        Token::StringLiteral(Cow::Borrowed(""))
    }
}
