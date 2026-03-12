use std::ops::Range;

use derive_more::{Display, Error};
use itertools::Itertools;
use logos::Logos;

use crate::lexer::token::Token;

mod token;

#[derive(Debug, Clone)]
pub(crate) struct SpannedToken<'a> {
    pub token: Token<'a>,
    pub span: Range<usize>,
}

#[derive(Debug, Display)]
pub(crate) enum LexerErrorKind {
    #[display("unknown token")]
    UnknownToken,
    #[display("unexpected end of file")]
    UnexpectedEof,
    #[display(
        "unexpected token: expected one of {:?} but got {:?}",
        expected_list.iter().join(", "),
        got
    )]
    UnexpectedToken {
        expected_list: &'static [Token<'static>],
        got: Token<'static>,
    },
}

#[derive(Debug, Display, Error)]
#[display("lexer error at {:?}: {}", span, kind)]
pub struct LexerError {
    kind: LexerErrorKind,
    span: Range<usize>,
}

pub(crate) struct Lexer<'a> {
    /// The current token position the lexer is at.
    pos: usize,
    /// The span that corresponds to the end of the file.
    eof_span: Range<usize>,
    /// The list of all correctly lexed tokens.
    tokens: Vec<SpannedToken<'a>>,
}

impl<'a> Lexer<'a> {
    pub(crate) fn lex(source: &'a str) -> (Self, Vec<LexerError>) {
        let mut lex = Token::lexer(source);
        let mut errors = Vec::new();
        let mut tokens = Vec::new();
        while let Some(result) = lex.next() {
            let span = lex.span();
            if let Ok(token) = result {
                trace!(?token, ?span, "lexed token");
                tokens.push(SpannedToken { token, span })
            } else {
                trace!(?span, "lexer encountered error");
                errors.push(LexerError {
                    span,
                    kind: LexerErrorKind::UnknownToken,
                })
            }
        }
        (
            Self {
                pos: 0,
                eof_span: source.len()..source.len(),
                tokens,
            },
            errors,
        )
    }

    pub(crate) fn next(&mut self) -> Result<&SpannedToken<'a>, LexerError> {
        if let Some(token) = self.tokens.get(self.pos) {
            self.pos += 1;
            Ok(token)
        } else {
            Err(LexerError {
                kind: LexerErrorKind::UnexpectedEof,
                span: self.eof_span.clone(),
            })
        }
    }

    pub(crate) fn peek(&mut self) -> Option<&SpannedToken<'a>> {
        self.tokens.get(self.pos)
    }

    pub(crate) fn consume(
        &'a mut self,
        expected_list: &'static [Token<'static>],
    ) -> Result<&'a SpannedToken<'a>, LexerError> {
        let next = self.next()?;
        if expected_list.contains(&next.token) {
            Ok(next)
        } else {
            let next = next.clone();
            Err(LexerError {
                kind: LexerErrorKind::UnexpectedToken {
                    expected_list,
                    got: next.token.into_static(),
                },
                span: next.span,
            })
        }
    }

    /// Advances the lexer.
    pub(crate) fn advance(&mut self) {
        self.pos += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(source: &str) -> (Lexer<'_>, Vec<LexerError>) {
        Lexer::lex(source)
    }

    #[test]
    fn lex_keywords() {
        let mut lexer = lex("create table database").0;
        assert!(matches!(lexer.next().unwrap().token, Token::Create));
        assert!(matches!(lexer.next().unwrap().token, Token::Table));
        assert!(matches!(lexer.next().unwrap().token, Token::Database));
    }

    #[test]
    fn lex_identifier() {
        let mut lexer = lex("users").0;
        let tok = lexer.next().unwrap();
        assert!(matches!(&tok.token, Token::Identifier(s) if s == "users"));
    }

    #[test]
    fn lex_integer_literal() {
        let mut lexer = lex("42").0;
        assert!(matches!(&lexer.next().unwrap().token, Token::IntegerLiteral(s) if s == "42"));
    }

    #[test]
    fn lex_string_literal_strips_quotes() {
        let mut lexer = lex(r#""hello""#).0;
        assert!(matches!(&lexer.next().unwrap().token, Token::StringLiteral(s) if s == "hello"));
    }

    #[test]
    fn lex_unknown_token_produces_error() {
        let errors = lex("@@@").1;
        assert!(!errors.is_empty());
    }

    #[test]
    fn lex_span_is_correct() {
        let mut lexer = lex("create table").0;
        let tok = lexer.next().unwrap();
        assert_eq!(tok.span, 0..6);
        let tok = lexer.next().unwrap();
        assert_eq!(tok.span, 7..12);
    }

    #[test]
    fn next_at_eof_returns_unexpected_eof() {
        let mut lexer = lex("").0;
        assert!(matches!(
            lexer.next().unwrap_err().kind,
            LexerErrorKind::UnexpectedEof
        ));
    }

    #[test]
    fn consume_wrong_token_returns_unexpected_token() {
        let mut lexer = lex("table").0;
        let err = lexer.consume(&[Token::Create]).unwrap_err();
        assert!(matches!(err.kind, LexerErrorKind::UnexpectedToken { .. }));
    }

    #[test]
    fn peek_does_not_advance() {
        let mut lexer = lex("create table").0;
        lexer.peek();
        lexer.peek();
        assert!(matches!(lexer.next().unwrap().token, Token::Create));
    }
}
