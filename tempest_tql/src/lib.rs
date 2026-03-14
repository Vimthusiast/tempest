use std::ops::Range;

use derive_more::{Display, Error};
use itertools::Itertools;

use crate::{
    ast::Stmt,
    lexer::{Lexer, LexerError, LexerErrorKind, SpannedToken, Token},
};

#[macro_use]
extern crate tracing;

pub mod ast;
pub mod lexer;

#[derive(Debug, Display, Error)]
pub enum ParserErrorKind {
    #[display("lexer error: {}", _0)]
    LexerError(LexerErrorKind),
    #[display("unexpected token: {}", _0)]
    UnexpectedToken(#[error(not(source))] String),
    #[display("duplicate primary key")]
    DuplicatePrimaryKey,
    #[display("missing primary key")]
    MissingPrimaryKey,
}

impl ParserErrorKind {
    pub(crate) fn unexpected_token(expected_list: &[Token], got: &Token) -> Self {
        debug_assert_ne!(expected_list.len(), 0, "supply a list of expected tokens");
        if expected_list.len() == 1 {
            Self::UnexpectedToken(format!(
                "expected {}, but got {}",
                expected_list[0].name(),
                got.name()
            ))
        } else {
            Self::UnexpectedToken(format!(
                "expected one of: {}, but got {}",
                expected_list.iter().map(|t| t.name()).join(", "),
                got.name()
            ))
        }
    }
}

#[derive(Debug, Display, Error)]
#[display("parser error at {:?}: {}", span, kind)]
pub struct ParseError {
    span: Range<usize>,
    kind: ParserErrorKind,
}

// flatten the lexer error's span into the parser error
impl From<LexerError> for ParseError {
    fn from(value: LexerError) -> Self {
        Self {
            span: value.span,
            kind: ParserErrorKind::LexerError(value.kind),
        }
    }
}

pub(crate) struct Parser<'a> {
    lexer: Lexer<'a>,
    statements: Vec<Stmt<'a>>,
    errors: Vec<ParseError>,
    current_span: Range<usize>,
}

impl<'a> Parser<'a> {
    /// Tries to consume one of the token types provided in `expected_list` and extends the current
    /// span window to contain that token. If the next token is not withing `expected_list`,
    /// returns a [`ParserError`] of kind [`ParserErrorKind::UnexpectedToken`].
    pub(crate) fn consume(
        &mut self,
        expected_list: &[Token],
    ) -> Result<&SpannedToken<'a>, ParseError> {
        let tok = self.lexer.next();
        if expected_list.contains(&tok.token) {
            self.current_span.end = tok.span.end;
            Ok(tok)
        } else {
            Err(ParseError {
                span: tok.span.clone(),
                kind: ParserErrorKind::unexpected_token(expected_list, &tok.token),
            })
        }
    }

    /// Sync up to the next parsing restart point on errors.
    fn sync(&mut self) {
        loop {
            match self.lexer.peek().token {
                // consume, nobody upstream wants this
                Token::Semicolon => {
                    self.lexer.advance();
                    break;
                }

                // break but do not consume, parent context owns these
                Token::RBrace
                | Token::RParen
                | Token::Comma
                | Token::Create
                | Token::Select
                | Token::Insert
                | Token::Eof => break,

                // skip everything else
                _ => self.lexer.advance(),
            }
        }
    }

    fn parse_all(mut self) -> (Vec<Stmt<'a>>, Vec<ParseError>) {
        while !self.lexer.reached_eof() {
            match self.parse_stmt() {
                Ok(stmt) => self.statements.push(stmt),
                Err(err) => {
                    self.errors.push(err);
                    self.sync();
                }
            }
        }

        (self.statements, self.errors)
    }

    fn new(source: &'a str) -> Self {
        let (lexer, lexer_errors) = Lexer::lex(source);
        Parser {
            lexer,
            current_span: 0..0,
            statements: Vec::new(),
            errors: lexer_errors.into_iter().map(Into::into).collect(),
        }
    }
}

#[instrument(skip_all, level = "debug")]
pub fn parse<'a>(source: &'a str) -> (Vec<Stmt<'a>>, Vec<ParseError>) {
    Parser::new(source).parse_all()
}

#[cfg(test)]
mod tests {
    use crate::ast::*;

    use super::*;

    /// If `errors` is not empty, prints them using the `Display` implementation, and `panic!`s.
    fn assert_no_errors(errors: &[ParseError]) {
        if !errors.is_empty() {
            for err in errors {
                eprintln!("{}", err);
            }
            panic!("there should not be any errors, but got {}", errors.len());
        }
    }

    #[test]
    fn consume_wrong_token_returns_unexpected_token() {
        let mut parser = Parser::new("table");
        let err = parser.consume(&[Token::Create]).unwrap_err();
        assert!(matches!(err.kind, ParserErrorKind::UnexpectedToken(_)));
    }

    #[test]
    fn test_create_database() {
        let source = "create database mydb;";
        let (statements, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::CreateDatabase(CreateDatabaseStmt { name, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };
        assert_eq!(name.name, "mydb");
        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn test_create_table() {
        let source = "create table mydb.users : User {
            primary key (id),
        };";

        let (statements, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::CreateTable(CreateTableStmt { path, ty, body, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };
        assert_eq!(path.database.as_ref().unwrap().name, "mydb");
        assert_eq!(path.name.name, "users");
        assert_eq!(ty.name.name, "User");
        assert_eq!(body.primary_key.columns[0].name, "id");
        assert_eq!(body.primary_key.columns.len(), 1);
        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn test_create_type() {
        let source = "create type User {
            id       : Int64,
            username : String,
        };";

        let (statements, errors) = parse(source);
        assert_no_errors(&errors);

        let Stmt::CreateTy(CreateTyStmt { path, body, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };

        assert_eq!(path.name.name, "User");
        assert_eq!(body.fields[0].name.name, "id");
        assert_eq!(body.fields[0].ty.name.name, "Int64");
        assert_eq!(body.fields[1].name.name, "username");
        assert_eq!(body.fields[1].ty.name.name, "String");
        assert_eq!(body.fields.len(), 2);
        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn test_create_type_qualified_path() {
        let source = "create type main.User { id: Int64 };";

        let (statements, errors) = parse(source);
        assert_no_errors(&errors);

        let Stmt::CreateTy(CreateTyStmt { path, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };

        assert_eq!(path.database.as_ref().unwrap().name, "main");
        assert_eq!(path.name.name, "User");
    }

    #[test]
    fn test_create_database_works_after_error_sync() {
        // finds IDENTIFIER ("garbage"), then syncs up to `;`
        let source = "garbage code; create database main;";

        let (statements, errors) = parse(source);
        assert!(matches!(
            errors[0].kind,
            ParserErrorKind::UnexpectedToken(_),
        ));
        assert_eq!(errors.len(), 1);

        let Stmt::CreateDatabase(CreateDatabaseStmt { name, .. }) = &statements[0] else {
            panic!("invalid statement type: {:?}", &statements[0]);
        };
        assert_eq!(name.name, "main".into());
    }

    #[test]
    fn test_parse_insert_value() {
        let source = "insert into mydb.users { id: 42 };";
        let (stmts, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::InsertInto(stmt) = &stmts[0] else {
            panic!("expected insert")
        };
        assert_eq!(stmt.values.values[0].column.name, "id".into());
        assert!(
            matches!(stmt.values.values[0].value.kind, ExprKind::IntegerLiteral(ref s) if s == "42")
        );
    }

    #[test]
    fn test_parse_insert_value_list_multiple() {
        let source = r#"insert into mydb.users { id: 1, username: "john" };"#;
        let (stmts, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::InsertInto(stmt) = &stmts[0] else {
            panic!("expected insert")
        };
        assert_eq!(stmt.values.values.len(), 2);
        assert_eq!(stmt.values.values[1].column.name, "username".into());
        assert!(
            matches!(stmt.values.values[1].value.kind, ExprKind::StringLiteral(ref s) if s == "john")
        );
    }

    #[test]
    fn test_parse_insert_stmt_table_path() {
        let source = "insert into mydb.users { id: 1 };";
        let (stmts, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::InsertInto(stmt) = &stmts[0] else {
            panic!("expected insert")
        };
        assert_eq!(stmt.table.database.as_ref().unwrap().name, "mydb".into());
        assert_eq!(stmt.table.name.name, "users".into());
    }

    #[test]
    fn test_select_all() {
        let source = "select * from mydb.users;";
        let (stmts, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::SelectFrom(stmt) = &stmts[0] else {
            panic!("expected select")
        };
        assert!(matches!(stmt.projection.kind, ProjectionKind::All));
        assert_eq!(stmt.table.name.name, "users".into());
    }

    #[test]
    fn test_select_columns() {
        let source = "select id, username from mydb.users;";
        let (stmts, errors) = parse(source);
        assert_no_errors(&errors);
        let Stmt::SelectFrom(stmt) = &stmts[0] else {
            panic!("expected select")
        };
        let ProjectionKind::Columns(cols) = &stmt.projection.kind else {
            panic!("expected columns")
        };
        assert_eq!(cols.len(), 2);
        assert_eq!(cols[0].name, "id".into());
        assert_eq!(cols[1].name, "username".into());
    }
}
