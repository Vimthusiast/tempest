use crate::{
    ParseError, Parser, ParserErrorKind,
    ast::{CreateDatabaseStmt, CreateTableStmt, CreateTyStmt, InsertIntoStmt, SelectFromStmt},
    lexer::Token,
};

#[derive(Debug)]
pub enum Stmt<'a> {
    CreateDatabase(CreateDatabaseStmt<'a>),
    CreateTable(CreateTableStmt<'a>),
    CreateTy(CreateTyStmt<'a>),
    InsertInto(InsertIntoStmt<'a>),
    SelectFrom(SelectFromStmt<'a>),
}

impl<'a> Parser<'a> {
    #[instrument(skip_all, level = "trace")]
    pub(crate) fn parse_create_stmt(&mut self) -> Result<Stmt<'a>, ParseError> {
        self.current_span.start = self.consume(&[Token::Create])?.span.start;
        let tok = self.lexer.peek();

        match tok.token {
            Token::Database => self.parse_create_database_stmt().map(Stmt::CreateDatabase),
            Token::Table => self.parse_create_table_stmt().map(Stmt::CreateTable),
            Token::Type => self.parse_create_ty_stmt().map(Stmt::CreateTy),
            _ => Err(ParseError {
                span: tok.span.clone(),
                kind: ParserErrorKind::unexpected_token(
                    &[Token::Database, Token::Table, Token::Type],
                    &tok.token,
                ),
            }),
        }
    }

    #[instrument(skip_all, level = "trace")]
    pub(crate) fn parse_stmt(&mut self) -> Result<Stmt<'a>, ParseError> {
        // start a new span
        self.current_span = 0..0;

        // peek at next token
        let stmt_start = self.lexer.peek();

        match stmt_start.token {
            Token::Create => self.parse_create_stmt(),
            Token::Insert => self.parse_insert_stmt().map(Stmt::InsertInto),
            Token::Select => self.parse_select_stmt().map(Stmt::SelectFrom),
            _ => {
                let err = Err(ParseError {
                    span: stmt_start.span.clone(),
                    kind: ParserErrorKind::unexpected_token(
                        &[Token::Create, Token::Insert, Token::Select],
                        &stmt_start.token,
                    ),
                });
                self.lexer.advance();
                self.sync();
                err
            }
        }
    }
}
