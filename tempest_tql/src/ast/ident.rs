use std::{borrow::Cow, ops::Range};

use crate::{Parser, ParserError, ParserErrorKind, lexer::Token};

#[derive(Debug)]
pub struct Ident<'a> {
    pub name: Cow<'a, str>,
    pub span: Range<usize>,
}

impl<'a> Parser<'a> {
    #[instrument(skip_all, level = "debug")]
    pub(crate) fn parse_ident(&mut self) -> Result<Ident<'a>, ParserError> {
        let tok = self.lexer.next();
        match &tok.token {
            Token::Identifier(name) => {
                self.current_span.end = tok.span.end;
                Ok(Ident {
                    name: name.clone(),
                    span: tok.span.clone(),
                })
            }
            _ => Err(ParserError {
                span: tok.span.clone(),
                kind: ParserErrorKind::UnexpectedToken {
                    expected_list: &[Token::Identifier(Cow::Borrowed(""))],
                    got: tok.token.clone().into_static(),
                },
            }),
        }
    }
}
