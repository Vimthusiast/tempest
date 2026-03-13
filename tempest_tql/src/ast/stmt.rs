use crate::{
    Parser, ParserError, ParserErrorKind,
    ast::{CreateDatabaseStmt, CreateTableStmt, CreateTyStmt},
    lexer::Token,
};

#[derive(Debug)]
pub enum Stmt<'a> {
    CreateDatabase(CreateDatabaseStmt<'a>),
    CreateTable(CreateTableStmt<'a>),
    CreateTy(CreateTyStmt<'a>),
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_create_stmt(&mut self) -> Result<Stmt<'a>, ParserError> {
        self.current_span.start = self.consume(&[Token::Create])?.span.start;
        let next = self.lexer.peek();

        match next.token {
            Token::Database => self.parse_create_database_stmt().map(Stmt::CreateDatabase),
            Token::Table => self.parse_create_table_stmt().map(Stmt::CreateTable),
            Token::Type => self.parse_create_ty_stmt().map(Stmt::CreateTy),
            _ => Err(ParserError {
                span: next.span.clone(),
                kind: ParserErrorKind::UnexpectedToken {
                    expected_list: &[Token::Database, Token::Table, Token::Type],
                    got: next.token.clone().into_static(),
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
                self.sync();
                err
            }
        }
    }
}
