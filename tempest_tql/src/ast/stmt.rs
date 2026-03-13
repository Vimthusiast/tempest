use crate::{
    Parser, ParserError, ParserErrorKind,
    ast::{CreateDatabaseStmt, CreateTableStmt, CreateTyStmt, InsertIntoStmt},
    lexer::Token,
};

#[derive(Debug)]
pub enum Stmt<'a> {
    CreateDatabase(CreateDatabaseStmt<'a>),
    CreateTable(CreateTableStmt<'a>),
    CreateTy(CreateTyStmt<'a>),
    InsertInto(InsertIntoStmt<'a>),
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_create_stmt(&mut self) -> Result<Stmt<'a>, ParserError> {
        self.current_span.start = self.consume(&[Token::Create])?.span.start;
        let tok = self.lexer.peek();

        match tok.token {
            Token::Database => self.parse_create_database_stmt().map(Stmt::CreateDatabase),
            Token::Table => self.parse_create_table_stmt().map(Stmt::CreateTable),
            Token::Type => self.parse_create_ty_stmt().map(Stmt::CreateTy),
            _ => Err(ParserError {
                span: tok.span.clone(),
                kind: ParserErrorKind::UnexpectedToken {
                    expected_list: &[Token::Database, Token::Table, Token::Type],
                    got: tok.token.clone().into_static(),
                },
            }),
        }
    }

    pub(crate) fn parse_stmt(&mut self) -> Result<Stmt<'a>, ParserError> {
        // start a new span
        self.current_span = 0..0;

        // peek at next token
        let stmt_start = self.lexer.peek();

        match stmt_start.token {
            Token::Create => self.parse_create_stmt(),
            Token::Insert => self.parse_insert_stmt().map(Stmt::InsertInto),
            Token::Select => todo!("parse select statement"),
            _ => {
                let err = Err(ParserError {
                    span: stmt_start.span.clone(),
                    kind: ParserErrorKind::UnexpectedToken {
                        expected_list: &[Token::Create, Token::Insert, Token::Select],
                        got: stmt_start.token.clone().into_static(),
                    },
                });
                self.sync();
                err
            }
        }
    }
}
