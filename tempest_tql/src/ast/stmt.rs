use std::ops::Range;

use crate::{Parser, ParserError, ParserErrorKind, ast::Ident, lexer::Token};

#[derive(Debug)]
pub struct PrimaryKey<'a> {
    pub span: Range<usize>,
    pub columns: Vec<Ident<'a>>,
}

#[derive(Debug)]
pub struct TableBody<'a> {
    pub span: Range<usize>,
    pub primary_key: PrimaryKey<'a>,
}

#[derive(Debug)]
pub enum Stmt<'a> {
    CreateDatabase {
        span: Range<usize>,
        name: Ident<'a>,
    },
    CreateTable {
        span: Range<usize>,
        name: Ident<'a>,
        ty: Ident<'a>,
        body: TableBody<'a>,
    },
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
                        kind: ParserErrorKind::UnexpectedToken {
                            expected_list: &[Token::Primary, Token::RBrace],
                            got: tok.token.clone().into_static(),
                        },
                    };
                    if tok.token == Token::Eof {
                        // exit on eof
                        return Err(err);
                    } else {
                        // try to go further
                        self.errors.push(err);
                        self.sync();
                    }
                }
            }
        }

        let span_end = self.consume(&[Token::RParen])?.span.end;

        Ok(PrimaryKey {
            span: span_start..span_end,
            columns,
        })
    }

    pub(crate) fn parse_create_stmt(&mut self) -> Result<Stmt<'a>, ParserError> {
        self.current_span.start = self.consume(&[Token::Create])?.span.start;
        let create = self.consume(&[Token::Table, Token::Database])?;

        match create.token {
            Token::Table => {
                let name = self.parse_ident()?;
                let _colon = self.consume(&[Token::Colon])?;
                let ty = self.parse_ident()?;

                // -- parse table body --
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
                                kind: ParserErrorKind::UnexpectedToken {
                                    expected_list: &[Token::Primary, Token::RBrace],
                                    got: tok.token.clone().into_static(),
                                },
                            };
                            if tok.token == Token::Eof {
                                // exit on eof
                                return Err(err);
                            } else {
                                // try to go further
                                self.errors.push(err);
                                self.sync();
                            }
                        }
                    }
                }
                let body_span_end = self.consume(&[Token::RBrace])?.span.end;

                self.consume(&[Token::Semicolon])?;

                Ok(Stmt::CreateTable {
                    span: self.current_span.clone(),
                    name,
                    body: TableBody {
                        span: body_span_start..body_span_end,
                        primary_key: primary_key.ok_or_else(|| ParserError {
                            // TODO: use the whole span, or just the end of the body?
                            span: self.current_span.clone(),
                            kind: ParserErrorKind::MissingPrimaryKey,
                        })?,
                    },
                    ty,
                })
            }
            Token::Database => {
                let name = self.parse_ident()?;
                self.consume(&[Token::Semicolon])?;
                Ok(Stmt::CreateDatabase {
                    span: self.current_span.clone(),
                    name,
                })
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn parse_stmt(&mut self) -> Result<Stmt<'a>, ParserError> {
        // start a new span
        self.current_span = 0..0;

        // peek at next token
        let stmt_start = self.lexer.peek();

        match stmt_start.token {
            Token::Create => self.parse_create_stmt(),
            Token::Insert => todo!("parse insert statement"),
            Token::Select => todo!("parse select statement"),
            _ => {
                let err = Err(ParserError {
                    span: stmt_start.span.clone(),
                    kind: ParserErrorKind::UnexpectedToken {
                        expected_list: &[Token::Create, Token::Insert, Token::Select],
                        got: stmt_start.token.clone().into_static(),
                    },
                });
                self.lexer.advance();
                err
            }
        }
    }
}
