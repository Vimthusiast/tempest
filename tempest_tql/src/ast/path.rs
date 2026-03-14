use std::ops::Range;

use tempest_core::tempest_str::TempestStr;

use crate::{Parser, ParseError, ast::Ident, lexer::Token};

/// A `Path` may either resolve to a fully qualified path of database + name, or just the name.
#[derive(Debug)]
pub struct Path<'a> {
    pub span: Range<usize>,
    pub database: Option<Ident<'a>>,
    pub name: Ident<'a>,
}

impl<'a> Path<'a> {
    #[cfg(any(test, feature = "testing"))]
    pub fn for_testing(database: Option<TempestStr<'a>>, name: TempestStr<'a>) -> Self {
        Self {
            span: 0..0,
            database: database.map(Ident::for_testing),
            name: Ident::for_testing(name),
        }
    }
}

impl<'a> Parser<'a> {
    pub(crate) fn parse_path(&mut self) -> Result<Path<'a>, ParseError> {
        let first = self.parse_ident()?;
        if self.lexer.peek().token == Token::Dot {
            self.consume(&[Token::Dot])?;
            let name = self.parse_ident()?;
            Ok(Path {
                span: first.span.start..name.span.end,
                database: Some(first),
                name,
            })
        } else {
            Ok(Path {
                span: first.span.clone(),
                database: None,
                name: first,
            })
        }
    }
}
