use std::{borrow::Cow, ops::Range};

use crate::{
    Parser, ParserError, ParserErrorKind,
    ast::{Expr, Ident, Path},
    lexer::Token,
};

#[derive(Debug)]
pub struct InsertValue<'a> {
    pub span: Range<usize>,
    pub column: Ident<'a>,
    pub value: Expr<'a>,
}

#[derive(Debug)]
pub struct InsertValueList<'a> {
    pub span: Range<usize>,
    pub values: Vec<InsertValue<'a>>,
}

#[derive(Debug)]
pub struct InsertIntoStmt<'a> {
    pub span: Range<usize>,
    pub table: Path<'a>,
    pub values: InsertValueList<'a>,
}

impl<'a> Parser<'a> {
    fn parse_insert_value(&mut self) -> Result<InsertValue<'a>, ParserError> {
        let column = self.parse_ident()?;
        self.consume(&[Token::Colon])?;
        let value = self.parse_expr()?;
        Ok(InsertValue {
            span: column.span.start..value.span.end,
            column,
            value,
        })
    }

    pub(crate) fn parse_insert_value_list(&mut self) -> Result<InsertValueList<'a>, ParserError> {
        let span_start = self.consume(&[Token::LBrace])?.span.start;
        let mut values = Vec::new();
        loop {
            let tok = self.lexer.peek();
            match tok.token {
                Token::Identifier(_) => {
                    let value = self.parse_insert_value()?;
                    values.push(value);
                }
                Token::Comma => self.lexer.advance(),
                Token::RBrace => break,
                _ => {
                    let err = ParserError {
                        span: tok.span.clone(),
                        kind: ParserErrorKind::UnexpectedToken {
                            expected_list: &[
                                Token::Identifier(Cow::Borrowed("")),
                                Token::Comma,
                                Token::RBrace,
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

        let span_end = self.consume(&[Token::RBrace])?.span.end;

        Ok(InsertValueList {
            span: span_start..span_end,
            values,
        })
    }

    pub(crate) fn parse_insert_stmt(&mut self) -> Result<InsertIntoStmt<'a>, ParserError> {
        self.current_span.start = self.consume(&[Token::Insert])?.span.start;
        self.consume(&[Token::Into])?;
        let table = self.parse_path()?;
        let values = self.parse_insert_value_list()?;
        self.consume(&[Token::Semicolon])?;
        Ok(InsertIntoStmt {
            span: self.current_span.clone(),
            table,
            values,
        })
    }
}
