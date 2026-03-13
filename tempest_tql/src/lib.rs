use std::ops::Range;

use derive_more::{Display, Error};
use itertools::Itertools;

use crate::{
    ast::Stmt,
    lexer::{Lexer, LexerError, LexerErrorKind, SpannedToken, Token},
};

#[macro_use]
extern crate tracing;

pub mod ast;
pub mod lexer;

#[derive(Debug, Display)]
pub enum ParserErrorKind {
    #[display("lexer error: {}", _0)]
    LexerError(LexerErrorKind),
    #[display(
        "unexpected token: expected one of {} but got {}",
        expected_list.iter().map(|t| t.name()).join(", "),
        got.name()
    )]
    UnexpectedToken {
        expected_list: &'static [Token<'static>],
        got: Token<'static>,
    },
    #[display("duplicate primary key")]
    DuplicatePrimaryKey,
    #[display("missing primary key")]
    MissingPrimaryKey,
}

#[derive(Debug, Display, Error)]
#[display("parser error at {:?}: {}", span, kind)]
pub struct ParserError {
    span: Range<usize>,
    kind: ParserErrorKind,
}

// flatten the lexer error's span into the parser error
impl From<LexerError> for ParserError {
    fn from(value: LexerError) -> Self {
        Self {
            span: value.span,
            kind: ParserErrorKind::LexerError(value.kind),
        }
    }
}

pub(crate) struct Parser<'a> {
    lexer: Lexer<'a>,
    statements: Vec<Stmt<'a>>,
    errors: Vec<ParserError>,
    current_span: Range<usize>,
}

impl<'a> Parser<'a> {
    /// Tries to consume one of the token types provided in `expected_list` and extends the current
    /// span window to contain that token. If the next token is not withing `expected_list`,
    /// returns a [`ParserError`] of kind [`ParserErrorKind::UnexpectedToken`].
    pub(crate) fn consume(
        &mut self,
        expected_list: &'static [Token<'static>],
    ) -> Result<&SpannedToken<'a>, ParserError> {
        let next = self.lexer.next();
        if expected_list.contains(&next.token) {
            self.current_span.end = next.span.end;
            Ok(next)
        } else {
            let next = next.clone();
            Err(ParserError {
                span: next.span,
                kind: ParserErrorKind::UnexpectedToken {
                    expected_list,
                    got: next.token.into_static(),
                },
            })
        }
    }

    /// Sync up to the next parsing restart point on errors.
    fn sync(&mut self) {
        loop {
            match self.lexer.peek().token {
                // consume, nobody upstream wants this
                Token::Semicolon => {
                    self.lexer.advance();
                    break;
                }

                // break but do not consume, parent context owns these
                Token::RBrace
                | Token::RParen
                | Token::Comma
                | Token::Create
                | Token::Select
                | Token::Insert
                | Token::Eof => break,

                // skip everything else
                _ => self.lexer.advance(),
            }
        }
    }

    fn parse_all(mut self) -> (Vec<Stmt<'a>>, Vec<ParserError>) {
        while !self.lexer.reached_eof() {
            match self.parse_stmt() {
                Ok(stmt) => self.statements.push(stmt),
                Err(err) => {
                    self.errors.push(err);
                    self.sync();
                }
            }
        }

        (self.statements, self.errors)
    }

    fn new(source: &'a str) -> Self {
        let (lexer, lexer_errors) = Lexer::lex(source);
        Parser {
            lexer,
            current_span: 0..0,
            statements: Vec::new(),
            errors: lexer_errors.into_iter().map(Into::into).collect(),
        }
    }
}

#[instrument(skip_all, level = "debug")]
pub fn parse<'a>(source: &'a str) -> (Vec<Stmt<'a>>, Vec<ParserError>) {
    Parser::new(source).parse_all()
}

#[cfg(test)]
mod tests {
    use crate::ast::*;

    use super::*;

    /// If `errors` is not empty, prints them using the `Display` implementation, and `panic!`s.
    fn assert_no_errors(errors: &[ParserError]) {
        if !errors.is_empty() {
            for err in errors {
                eprintln!("{}", err);
            }
            panic!("there should not be any errors, but got {}", errors.len());
        }
    }

    #[test]
    fn consume_wrong_token_returns_unexpected_token() {
        let mut parser = Parser::new("table");
        let err = parser.consume(&[Token::Create]).unwrap_err();
        assert!(matches!(err.kind, ParserErrorKind::UnexpectedToken { .. }));
    }

    #[test]
    fn test_create_database() {
        let source = "create database mydb;";
        let (statements, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::CreateDatabase(CreateDatabaseStmt { name, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };
        assert_eq!(name.name, "mydb");
        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn test_create_table() {
        let source = "create table users : User {
            primary key (id),
        };";

        let (statements, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::CreateTable(CreateTableStmt { name, ty, body, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };
        assert_eq!(name.name, "users");
        assert_eq!(ty.name, "User");
        assert_eq!(body.primary_key.columns[0].name, "id");
        assert_eq!(body.primary_key.columns.len(), 1);
        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn test_create_type() {
        let source = "create type User {
            id       : Int64,
            username : String,
        };";

        let (statements, errors) = parse(source);
        assert_no_errors(&errors);

        let Stmt::CreateTy(CreateTyStmt { name, body, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };

        assert_eq!(name.name, "User");
        assert_eq!(body.fields[0].name.name, "id");
        assert_eq!(body.fields[0].ty.name.name, "Int64");
        assert_eq!(body.fields[1].name.name, "username");
        assert_eq!(body.fields[1].ty.name.name, "String");
        assert_eq!(body.fields.len(), 2);
        assert_eq!(statements.len(), 1);
    }
}
