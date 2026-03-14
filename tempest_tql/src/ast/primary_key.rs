use std::ops::Range;

use crate::{Parser, ParserError, ParserErrorKind, ast::Ident, lexer::Token};

#[derive(Debug)]
pub struct PrimaryKey<'a> {
    pub span: Range<usize>,
    pub columns: Vec<Ident<'a>>,
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_primary_key(&mut self) -> Result<PrimaryKey<'a>, ParserError> {
        let span_start = self.consume(&[Token::Primary])?.span.start;
        self.consume(&[Token::Key])?;
        self.consume(&[Token::LParen])?;

        let mut columns = Vec::new();
        loop {
            let tok = self.lexer.peek();
            match tok.token {
                Token::Identifier(_) => {
                    let ident = self.parse_ident()?;
                    columns.push(ident);
                }
                Token::Comma => self.lexer.advance(),
                Token::RParen => break,
                _ => {
                    let err = ParserError {
                        span: tok.span.clone(),
                        kind: ParserErrorKind::unexpected_token(
                            &[Token::Primary, Token::RBrace],
                            &tok.token,
                        ),
                    };
                    if tok.token == Token::Eof {
                        return Err(err);
                    }
                    self.errors.push(err);
                    self.sync();
                }
            }
        }

        let span_end = self.consume(&[Token::RParen])?.span.end;

        Ok(PrimaryKey {
            span: span_start..span_end,
            columns,
        })
    }
}
