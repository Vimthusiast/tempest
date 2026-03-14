use std::ops::Range;

use tempest_core::tempest_str::TempestStr;

use crate::{Parser, ParseError, ParserErrorKind, lexer::Token};

#[derive(Debug)]
pub struct Ident<'a> {
    pub span: Range<usize>,
    pub name: TempestStr<'a>,
}

impl<'a> Ident<'a> {
    #[cfg(any(test, feature = "testing"))]
    pub fn for_testing(name: TempestStr<'a>) -> Self {
        Self { span: 0..0, name }
    }
}

impl<'a> Parser<'a> {
    #[instrument(skip_all, level = "debug")]
    pub(crate) fn parse_ident(&mut self) -> Result<Ident<'a>, ParseError> {
        let tok = self.lexer.next();
        match &tok.token {
            Token::Identifier(name) => {
                self.current_span.end = tok.span.end;
                Ok(Ident {
                    name: name.clone(),
                    span: tok.span.clone(),
                })
            }
            _ => {
                let err = Err(ParseError {
                    span: tok.span.clone(),
                    kind: ParserErrorKind::unexpected_token(&[Token::empty_ident()], &tok.token),
                });
                self.lexer.advance();
                err
            }
        }
    }
}
