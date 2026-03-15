use std::ops::Range;

use derive_more::{Display, Error};
use logos::Logos;

pub(crate) use crate::lexer::token::Token;

mod token;

#[derive(Debug, Clone)]
pub(crate) struct SpannedToken<'a> {
    pub token: Token<'a>,
    pub span: Range<usize>,
}

#[derive(Debug, Display, Error)]
pub enum LexerErrorKind {
    #[display("unknown token")]
    UnknownToken,
}

#[derive(Debug, Display, Error)]
#[display("lexer error at {:?}: {}", span, kind)]
pub struct LexerError {
    pub kind: LexerErrorKind,
    pub span: Range<usize>,
}

pub(crate) struct Lexer<'a> {
    /// The current token position the lexer is at.
    pos: usize,
    /// The list of all correctly lexed tokens.
    tokens: Vec<SpannedToken<'a>>,
}

impl<'a> Lexer<'a> {
    pub(crate) fn lex(source: &'a str) -> (Self, Vec<LexerError>) {
        // create lexer
        let mut lex = Token::lexer(source);

        // lex all tokens
        let mut errors = Vec::new();
        let mut tokens = Vec::new();
        while let Some(result) = lex.next() {
            let span = lex.span();
            if let Ok(token) = result {
                tokens.push(SpannedToken { token, span })
            } else {
                errors.push(LexerError {
                    span,
                    kind: LexerErrorKind::UnknownToken,
                })
            }
        }

        // terminate with eof token
        tokens.push(SpannedToken {
            token: Token::Eof,
            span: source.len()..source.len(),
        });

        (Self { pos: 0, tokens }, errors)
    }

    pub(crate) fn next(&mut self) -> &SpannedToken<'a> {
        let token = &self.tokens[self.pos];
        if token.token != Token::Eof {
            self.pos += 1;
        }
        token
    }

    pub(crate) fn peek(&mut self) -> &SpannedToken<'a> {
        self.tokens.get(self.pos).unwrap()
    }

    /// Advances the lexer.
    pub(crate) fn advance(&mut self) {
        self.pos += 1;
    }

    /// Checks if we arrived at the `Eof` token, or if we've surpassed it.
    pub(crate) fn reached_eof(&self) -> bool {
        self.pos >= self.tokens.len() || self.tokens[self.pos].token == Token::Eof
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
        assert!(matches!(lexer.next().token, Token::Create));
        assert!(matches!(lexer.next().token, Token::Table));
        assert!(matches!(lexer.next().token, Token::Database));
    }

    #[test]
    fn lex_identifier() {
        let mut lexer = lex("users").0;
        let tok = lexer.next();
        assert!(matches!(&tok.token, Token::Identifier(s) if *s == "users".into()));
    }

    #[test]
    fn lex_integer_literal() {
        let mut lexer = lex("42").0;
        assert!(matches!(&lexer.next().token, Token::IntegerLiteral(s) if s == "42"));
    }

    #[test]
    fn lex_string_literal_strips_quotes() {
        let mut lexer = lex(r#""hello""#).0;
        assert!(matches!(&lexer.next().token, Token::StringLiteral(s) if s == "hello"));
    }

    #[test]
    fn lex_unknown_token_produces_error() {
        let errors = lex("@@@").1;
        assert!(!errors.is_empty());
    }

    #[test]
    fn lex_span_is_correct() {
        let mut lexer = lex("create table").0;
        let tok = lexer.next();
        assert_eq!(tok.span, 0..6);
        let tok = lexer.next();
        assert_eq!(tok.span, 7..12);
    }

    #[test]
    fn next_at_eof_returns_eof() {
        let mut lexer = lex("").0;
        assert!(matches!(lexer.next().token, Token::Eof));
    }

    #[test]
    fn peek_does_not_advance() {
        let mut lexer = lex("create table").0;
        lexer.peek();
        lexer.peek();
        assert!(matches!(lexer.next().token, Token::Create));
    }
}
