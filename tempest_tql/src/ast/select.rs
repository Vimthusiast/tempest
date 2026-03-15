use std::ops::Range;

use crate::{
    Parser, ParseError, ParserErrorKind,
    ast::{Ident, Path},
    lexer::Token,
};

#[derive(Debug)]
pub enum ProjectionKind<'a> {
    All,
    Columns(Vec<Ident<'a>>),
}

#[derive(Debug)]
pub struct Projection<'a> {
    pub span: Range<usize>,
    pub kind: ProjectionKind<'a>,
}

#[derive(Debug)]
pub struct SelectFromStmt<'a> {
    pub span: Range<usize>,
    pub projection: Projection<'a>,
    pub table: Path<'a>,
    // TODO: selection - filter out columns, based on a predicate expression
    // selection: Selection<'a>
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_projection(&mut self) -> Result<Projection<'a>, ParseError> {
        let tok = self.lexer.peek();
        match tok.token {
            Token::Asterisk => {
                let span = tok.span.clone();
                self.lexer.advance();
                Ok(Projection {
                    span,
                    kind: ProjectionKind::All,
                })
            }
            Token::Identifier(_) => {
                let span_start = tok.span.start;
                let mut columns = Vec::new();
                loop {
                    let tok = self.lexer.peek();
                    match tok.token {
                        Token::Identifier(_) => {
                            let col = self.parse_ident()?;
                            columns.push(col);
                        }
                        Token::Comma => self.lexer.advance(),
                        Token::From => break,
                        _ => {
                            let err = ParseError {
                                span: tok.span.clone(),
                                kind: ParserErrorKind::unexpected_token(
                                    &[Token::empty_ident(), Token::Comma, Token::From],
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
                Ok(Projection {
                    span: span_start..self.current_span.end,
                    kind: ProjectionKind::Columns(columns),
                })
            }
            _ => Err(ParseError {
                span: tok.span.clone(),
                kind: ParserErrorKind::unexpected_token(
                    &[Token::Asterisk, Token::empty_ident()],
                    &tok.token,
                ),
            }),
        }
    }

    pub(crate) fn parse_select_stmt(&mut self) -> Result<SelectFromStmt<'a>, ParseError> {
        self.current_span.start = self.consume(&[Token::Select])?.span.start;
        let projection = self.parse_projection()?;
        self.consume(&[Token::From])?;
        let table = self.parse_path()?;
        // ...selection/filtering goes here...
        self.consume(&[Token::Semicolon])?;
        Ok(SelectFromStmt {
            span: self.current_span.clone(),
            projection,
            table,
        })
    }
}
