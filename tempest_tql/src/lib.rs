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
        "unexpected token: expected one of {} but got {:?}",
        expected_list.iter().map(|t| t.name()).join(", "),
        got
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
                kind: ParserErrorKind::UnexpectedToken {
                    expected_list,
                    got: next.token.into_static(),
                },
                span: next.span,
            })
        }
    }

    fn sync(&mut self) {
        match self.lexer.tokens()[self.lexer.pos().saturating_sub(1)].token {
            Token::Semicolon | Token::RBrace | Token::RParen | Token::Comma | Token::Eof => return,
            _ => {}
        }

        loop {
            match self.lexer.peek().token {
                Token::Semicolon | Token::RBrace | Token::RParen | Token::Comma => {
                    self.lexer.advance();
                    break;
                }
                Token::Eof => break,
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
    use super::*;

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
        assert!(
            errors.is_empty(),
            "there should not be errors, but got: {:?}",
            errors
        );
        assert!(matches!(&statements[0], Stmt::CreateDatabase { name, .. }
            if name.name == "mydb"));
        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn test_create_table() {
        let source = "create table users : User {
            primary key (id)
        };";

        let (statements, errors) = parse(source);
        assert!(
            errors.is_empty(),
            "there should not be errors, but got: {:?}",
            errors
        );
        assert!(
            matches!(&statements[0], Stmt::CreateTable { name, ty, body, .. }
                if name.name == "users" && ty.name == "User"
                // validate table body has correct primary key definition
                && body.primary_key.columns[0].name == "id" && body.primary_key.columns.len() == 1)
        );
        assert_eq!(statements.len(), 1);
    }
}
