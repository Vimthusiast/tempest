use derive_more::{Display, Error, From};

use crate::lexer::{Lexer, LexerError};

pub mod lexer;

#[derive(Debug, Display, Error, From)]
pub enum ParserError {
    LexerError(LexerError),
}

pub struct Parser<'a> {
    source: &'a str,
}

impl<'a> Parser<'a> {
    pub fn parse(source: &'a str) -> () {
        let (lexer, lexer_errors) = Lexer::new(source);
    }
}
