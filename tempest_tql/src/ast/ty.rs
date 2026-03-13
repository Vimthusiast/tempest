use std::{borrow::Cow, ops::Range};

use crate::{Parser, ParserError, ParserErrorKind, ast::Ident, lexer::Token};

#[derive(Debug)]
pub struct TyPath<'a> {
    pub span: Range<usize>,
    /// The full identifier of a type - syntax-wise.
    ///
    /// # Note
    ///
    /// In the future, this will be a `Vec<Ident>`, and allow for qualified paths, but we don't
    /// have modules or anything right now, and won't during the MVP phase.
    pub name: Ident<'a>,
}

#[derive(Debug)]
pub struct TyDeclField<'a> {
    pub span: Range<usize>,
    pub name: Ident<'a>,
    pub ty: TyPath<'a>,
}

#[derive(Debug)]
pub struct TyDeclBody<'a> {
    pub span: Range<usize>,
    pub fields: Vec<TyDeclField<'a>>,
}

#[derive(Debug)]
pub struct CreateTyStmt<'a> {
    pub span: Range<usize>,
    pub name: Ident<'a>,
    pub body: TyDeclBody<'a>,
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_ty_path(&mut self) -> Result<TyPath<'a>, ParserError> {
        let name = self.parse_ident()?;
        Ok(TyPath {
            // same span as the inner ident, until qualified paths exist.
            // currently, this is basically a new-type with a duplicated span.
            span: name.span.clone(),
            name,
        })
    }

    pub(crate) fn parse_ty_decl_field(&mut self) -> Result<TyDeclField<'a>, ParserError> {
        let name = self.parse_ident()?;
        self.consume(&[Token::Colon])?;
        let ty = self.parse_ty_path()?;

        Ok(TyDeclField {
            span: name.span.start..ty.span.end,
            name,
            ty,
        })
    }

    fn parse_ty_decl_body(&mut self) -> Result<TyDeclBody<'a>, ParserError> {
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
        Ok(TyDeclBody {
            span: span_start..span_end,
            fields,
        })
    }

    /// Assumes that `create` has already been parsed and the span is set.
    pub(crate) fn parse_create_ty_stmt(&mut self) -> Result<CreateTyStmt<'a>, ParserError> {
        self.consume(&[Token::Type])?;
        let name = self.parse_ident()?;
        let body = self.parse_ty_decl_body()?;
        self.consume(&[Token::Semicolon])?;
        Ok(CreateTyStmt {
            span: self.current_span.clone(),
            name,
            body,
        })
    }
}
