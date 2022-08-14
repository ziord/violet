// a simple lexer with three token types

use crate::errors::ViError;
use std::fmt::Formatter;
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum TokenType {
  NUM,
  PLUS,
  MINUS,
  EOF,
  ERROR,
}

#[derive(Debug)]
pub struct Token<'a> {
  t_type: TokenType,
  line: i32,
  column: i32,
  error_code: Option<ViError>,
  value: &'a str,
}

#[derive(Debug)]
pub struct Lexer<'a, 'b> {
  src: &'a str,
  at_error: bool,
  line: i32,
  column: i32,
  start: usize,
  current: usize,
  keywords: HashMap<&'b str, TokenType>,
}

impl Display for TokenType {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      TokenType::NUM => write!(f, "TOKEN_NUM"),
      TokenType::PLUS => write!(f, "TOKEN_PLUS"),
      TokenType::MINUS => write!(f, "TOKEN_MINUS"),
      TokenType::EOF => write!(f, "TOKEN_EOF"),
      TokenType::ERROR => write!(f, "TOKEN_ERROR"),
    }
  }
}

impl<'a> Token<'a> {
  fn new(
    value: &'a str,
    t_type: TokenType,
    line: i32,
    column: i32,
    error: Option<ViError>,
  ) -> Self {
    Self {
      t_type,
      line,
      column,
      error_code: error,
      value,
    }
  }

  pub fn to_int(&self) -> i32 {
    match self.value.parse::<i32>() {
      Ok(x) => x,
      _ => 0,
    }
  }
  pub fn get_type(&self) -> TokenType {
    self.t_type
  }

  pub fn value(&self) -> &'a str {
    self.value
  }
}

impl<'a> Display for Token<'a> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "Token(value={}, type={}, column={}, line={})",
      self.value, self.t_type, self.column, self.line
    )
  }
}

impl<'a, 'b> Lexer<'a, 'b> {
  pub fn new(src: &'a str) -> Self {
    Self {
      src,
      at_error: false,
      line: 1,
      column: 1,
      start: 0,
      current: 0,
      keywords: HashMap::new(),
    }
  }

  fn is_digit(&self, ch: char) -> bool {
    ch.is_digit(10)
  }

  fn is_alpha(&self, ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
  }

  fn at_end(&self) -> bool {
    self.current >= self.src.len()
  }

  fn create_token(&self, t_type: TokenType) -> Token<'a> {
    let val = &self.src[self.start..self.current];
    Token::new(val, t_type, self.line, self.column, None)
  }

  fn eof_token(&self) -> Token<'a> {
    Token::new("", TokenType::EOF, self.line, self.column, None)
  }

  fn error_token(&self, code: ViError) -> Token<'a> {
    let mut token = self.create_token(TokenType::ERROR);
    token.error_code = Some(code);
    return token;
  }

  fn current(&self) -> char {
    if self.at_end() {
      return '\0';
    }
    self.src.as_bytes()[self.current] as char
  }

  fn peek(&self, i: Option<usize>) -> char {
    if self.at_end() {
      return '\0';
    }
    match i {
      // todo: improve
      Some(idx) => self.src.as_bytes()[idx] as char,
      None => self.src.as_bytes()[self.current] as char,
    }
  }

  fn skip_whitespace(&mut self) {
    loop {
      match self.peek(None) {
        ' ' | '\n' | '\t' | '\r' => {
          self.advance();
        }
        // todo: comment
        _ => return,
      }
    }
  }

  fn advance(&mut self) -> char {
    if self.current() == '\n' {
      self.line += 1;
      self.column = 1;
    } else {
      self.column += 1;
    }
    self.current += 1;
    self.src.as_bytes()[self.current - 1] as char
  }

  fn lex_number(&mut self) -> Token<'a> {
    // todo: improve
    let bytes = self.src.as_bytes();
    while !self.at_end() && self.is_digit(bytes[self.current] as char) {
      self.advance();
    }
    self.create_token(TokenType::NUM)
  }

  pub fn get_token(&mut self) -> Token<'a> {
    self.skip_whitespace();
    if self.at_end() {
      return self.eof_token();
    } else if self.at_error {
      return self.error_token(ViError::EL001); // todo
    }
    self.start = self.current;
    let ch = self.advance();
    if self.is_digit(ch) {
      return self.lex_number();
    }
    match ch {
      '+' => self.create_token(TokenType::PLUS),
      '-' => self.create_token(TokenType::MINUS),
      _ => self.error_token(ViError::EL001),
    }
  }
}
