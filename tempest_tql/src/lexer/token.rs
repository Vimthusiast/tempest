use std::borrow::Cow;

use derive_more::Display;
use logos::Logos;
use strum::IntoStaticStr;

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
    #[strum(serialize = "IDENTIFIER")]
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| Cow::Borrowed(lex.slice()))]
    Identifier(Cow<'a, str>),
    #[strum(serialize = "INTEGER_LITERAL")]
    #[regex(r"-?[0-9]+", |lex| Cow::Borrowed(lex.slice()))]
    IntegerLiteral(Cow<'a, str>),
    #[strum(serialize = "STRING_LITERAL")]
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
            Self::Identifier(ident) => Token::Identifier(Cow::Owned(ident.into_owned())),
            Self::IntegerLiteral(lit) => Token::IntegerLiteral(Cow::Owned(lit.into_owned())),
            Self::StringLiteral(lit) => Token::StringLiteral(Cow::Owned(lit.into_owned())),
            // SAFETY: all the other variants are not bound to 'a, so it's safe to transmute the
            // lifetime here, to avoid having to spell out all the other variants
            other => unsafe { std::mem::transmute(other) },
        }
    }

    pub(crate) fn name(&self) -> &'static str {
        self.into()
    }
}
