use std::{borrow::Cow, ops::Range};

use crate::{
    Parser, ParseError, ParserErrorKind,
    ast::{Ident, Path},
    lexer::Token,
};

#[derive(Debug)]
pub struct TyDeclField<'a> {
    pub span: Range<usize>,
    pub name: Ident<'a>,
    pub ty: Path<'a>,
}

#[derive(Debug)]
pub struct TyDeclBody<'a> {
    pub span: Range<usize>,
    pub fields: Vec<TyDeclField<'a>>,
}

#[derive(Debug)]
pub struct CreateTyStmt<'a> {
    pub span: Range<usize>,
    pub path: Path<'a>,
    pub body: TyDeclBody<'a>,
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_ty_decl_field(&mut self) -> Result<TyDeclField<'a>, ParseError> {
        let name = self.parse_ident()?;
        self.consume(&[Token::Colon])?;
        let ty = self.parse_path()?;

        Ok(TyDeclField {
            span: name.span.start..ty.span.end,
            name,
            ty,
        })
    }

    fn parse_ty_decl_body(&mut self) -> Result<TyDeclBody<'a>, ParseError> {
        let span_start = self.consume(&[Token::LBrace])?.span.start;
        let mut fields = Vec::new();
        loop {
            let tok = self.lexer.peek();
            match tok.token {
                Token::Identifier(_) => {
                    let field = match self.parse_ty_decl_field() {
                        Ok(f) => f,
                        Err(e) => {
                            self.errors.push(e);
                            self.sync();
                            continue;
                        }
                    };
                    fields.push(field);
                }
                Token::Comma => self.lexer.advance(),
                Token::RBrace => break,
                _ => {
                    let err = ParseError {
                        span: tok.span.clone(),
                        kind: ParserErrorKind::unexpected_token(
                            &[Token::empty_ident(), Token::Comma, Token::RBrace],
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
        let span_end = self.consume(&[Token::RBrace])?.span.end;
        Ok(TyDeclBody {
            span: span_start..span_end,
            fields,
        })
    }

    /// Assumes that `create` has already been parsed and the span is set.
    pub(crate) fn parse_create_ty_stmt(&mut self) -> Result<CreateTyStmt<'a>, ParseError> {
        self.consume(&[Token::Type])?;
        let path = self.parse_path()?;
        let body = self.parse_ty_decl_body()?;
        self.consume(&[Token::Semicolon])?;
        Ok(CreateTyStmt {
            span: self.current_span.clone(),
            path,
            body,
        })
    }
}
