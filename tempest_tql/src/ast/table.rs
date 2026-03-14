use std::ops::Range;

use crate::{
    Parser, ParserError, ParserErrorKind,
    ast::{Path, PrimaryKey},
    lexer::Token,
};

#[derive(Debug)]
pub struct TableDeclBody<'a> {
    pub span: Range<usize>,
    pub primary_key: PrimaryKey<'a>,
}

#[derive(Debug)]
pub struct CreateTableStmt<'a> {
    pub span: Range<usize>,
    pub path: Path<'a>,
    pub ty: Path<'a>,
    pub body: TableDeclBody<'a>,
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_table_decl_body(&mut self) -> Result<TableDeclBody<'a>, ParserError> {
        let body_span_start = self.consume(&[Token::LBrace])?.span.start;
        let mut primary_key = None;
        loop {
            let tok = self.lexer.peek();
            match tok.token {
                Token::Primary => {
                    if primary_key.is_some() {
                        self.errors.push(ParserError {
                            span: tok.span.clone(),
                            kind: ParserErrorKind::DuplicatePrimaryKey,
                        });
                        self.sync();
                        continue;
                    }
                    let pk = match self.parse_primary_key() {
                        Ok(pk) => pk,
                        Err(err) => {
                            self.errors.push(err);
                            self.sync();
                            continue;
                        }
                    };
                    primary_key = Some(pk);
                }
                Token::Comma => self.lexer.advance(),
                Token::RBrace => break,
                _ => {
                    let err = ParserError {
                        span: tok.span.clone(),
                        kind: ParserErrorKind::unexpected_token(
                            &[Token::Primary, Token::Comma, Token::RBrace],
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
        let body_span_end = self.consume(&[Token::RBrace])?.span.end;

        Ok(TableDeclBody {
            span: body_span_start..body_span_end,
            primary_key: primary_key.ok_or_else(|| ParserError {
                // TODO: use the whole span, or just the end of the body?
                span: self.current_span.clone(),
                kind: ParserErrorKind::MissingPrimaryKey,
            })?,
        })
    }

    /// Assumes that `create` has already been parsed and the span is set.
    pub(crate) fn parse_create_table_stmt(&mut self) -> Result<CreateTableStmt<'a>, ParserError> {
        self.consume(&[Token::Table])?;
        let path = self.parse_path()?;
        let _colon = self.consume(&[Token::Colon])?;
        let ty = self.parse_path()?;

        // -- parse table body --
        let body = self.parse_table_decl_body()?;

        self.consume(&[Token::Semicolon])?;

        Ok(CreateTableStmt {
            span: self.current_span.clone(),
            path,
            body,
            ty,
        })
    }
}
