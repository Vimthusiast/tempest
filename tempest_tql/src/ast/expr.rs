use std::{borrow::Cow, ops::Range};

use crate::{Parser, ParserError, ParserErrorKind, lexer::Token};

//pub enum BinaryOpKind {
//    Eq, Gt, Lt, Gte, Lte,
//    And, Or
//}

#[derive(Debug)]
pub enum ExprKind<'a> {
    IntegerLiteral(Cow<'a, str>),
    StringLiteral(Cow<'a, str>),
    Bool(bool),
    //ColumnRef(Ident<'a>),
    //BinaryOp {
    //    left:  Box<Expr<'a>>,
    //    op:    BinaryOpKind,
    //    right: Box<Expr<'a>>,
    //},
}

#[derive(Debug)]
pub struct Expr<'a> {
    pub span: Range<usize>,
    pub kind: ExprKind<'a>,
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_primary_expr(&mut self) -> Result<Expr<'a>, ParserError> {
        let tok = self.lexer.next();
        match &tok.token {
            Token::IntegerLiteral(s) => Ok(Expr {
                span: tok.span.clone(),
                kind: ExprKind::IntegerLiteral(s.clone()),
            }),
            Token::StringLiteral(s) => Ok(Expr {
                span: tok.span.clone(),
                kind: ExprKind::StringLiteral(s.clone()),
            }),
            Token::True => Ok(Expr {
                span: tok.span.clone(),
                kind: ExprKind::Bool(true),
            }),
            Token::False => Ok(Expr {
                span: tok.span.clone(),
                kind: ExprKind::Bool(false),
            }),
            _ => Err(ParserError {
                span: tok.span.clone(),
                kind: ParserErrorKind::unexpected_token(
                    &[
                        Token::empty_ident(),
                        Token::empty_string(),
                        Token::True,
                        Token::False,
                    ],
                    &tok.token,
                ),
            }),
        }
    }

    pub(crate) fn parse_expr(&mut self) -> Result<Expr<'a>, ParserError> {
        // for now, this just supports primary expressions, but computations and column references
        // will come later, when implementing complex selections in the 'where'-clause
        self.parse_primary_expr()
    }
}
