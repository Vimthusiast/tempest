use std::{borrow::Cow, ops::Range};

use crate::{
    Parser, ParserError, ParserErrorKind,
    ast::{Ident, TablePath},
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
    pub table: TablePath<'a>,
    // TODO: selection - filter out columns, based on a predicate expression
    // selection: Selection<'a>
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_projection(&mut self) -> Result<Projection<'a>, ParserError> {
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
                            let err = ParserError {
                                span: tok.span.clone(),
                                kind: ParserErrorKind::UnexpectedToken {
                                    expected_list: &[
                                        Token::Identifier(Cow::Borrowed("")),
                                        Token::Comma,
                                        Token::From,
                                    ],
                                    got: tok.token.clone().into_static(),
                                },
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
            _ => Err(ParserError {
                span: tok.span.clone(),
                kind: ParserErrorKind::UnexpectedToken {
                    expected_list: &[Token::Asterisk, Token::Identifier(Cow::Borrowed(""))],
                    got: tok.token.clone().into_static(),
                },
            }),
        }
    }

    pub(crate) fn parse_select_stmt(&mut self) -> Result<SelectFromStmt<'a>, ParserError> {
        self.current_span.start = self.consume(&[Token::Select])?.span.start;
        let projection = self.parse_projection()?;
        self.consume(&[Token::From])?;
        let table = self.parse_table_path()?;
        // ...selection/filtering goes here...
        self.consume(&[Token::Semicolon])?;
        Ok(SelectFromStmt {
            span: self.current_span.clone(),
            projection,
            table,
        })
    }
}
