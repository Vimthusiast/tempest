use std::ops::Range;

use crate::{Parser, ParserError, ast::Ident, lexer::Token};

#[derive(Debug)]
pub struct CreateDatabaseStmt<'a> {
    pub span: Range<usize>,
    pub name: Ident<'a>,
}

impl<'a> Parser<'a> {
    /// Assumes that `create` has already been parsed and the span is set.
    pub(crate) fn parse_create_database_stmt(
        &mut self,
    ) -> Result<CreateDatabaseStmt<'a>, ParserError> {
        self.consume(&[Token::Database])?;
        let name = self.parse_ident()?;
        self.consume(&[Token::Semicolon])?;
        Ok(CreateDatabaseStmt {
            span: self.current_span.clone(),
            name,
        })
    }
}
