// a simple lexer with three token types

use crate::errors::ViError;
use std::fmt::Formatter;
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[allow(non_camel_case_types)]
pub enum TokenType {
  NUM,
  PLUS,          // +
  MINUS,         // -
  STAR,          // *
  FWD_SLASH,     // /
  LEFT_BRACKET,  // (
  RIGHT_BRACKET, // )
  LESS_THAN,     // <
  GRT_THAN,      // >
  EQUAL_EQUAL,   // ==
  NOT_EQUAL,     // !=
  LESS_EQUAL,    // <=
  GRT_EQUAL,     // >=
  EQUAL,         // =
  SEMI_COLON,    // ;
  IDENT,         // id
  BOF,           // |-
  EOF,           // -|
  ERROR,
}

#[derive(Debug)]
pub enum OpType {
  PLUS,  // +
  MINUS, // -
  DIV,   // /
  MUL,   // *
  LEQ,   // <=
  GEQ,   // >=
  LT,    // <
  GT,    // >
  EQQ,   // ==
  NEQ,   // !=
  EQ,    // =
}

#[derive(Debug, Copy, Clone)]
pub struct Token<'a> {
  t_type: TokenType,
  line: i32,
  column: i32,
  value: &'a str,
  pub error_code: Option<ViError>,
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
      TokenType::NUM => write!(f, "TOK<NUM>"),
      TokenType::PLUS => write!(f, "TOK<PLUS>"),
      TokenType::MINUS => write!(f, "TOK<MINUS>"),
      TokenType::BOF => write!(f, "TOK<BOF>"),
      TokenType::EOF => write!(f, "TOK<EOF>"),
      TokenType::ERROR => write!(f, "TOK<ERROR>"),
      TokenType::STAR => write!(f, "TOK<STAR>"),
      TokenType::FWD_SLASH => write!(f, "TOK<FWD-SLASH>"),
      TokenType::LEFT_BRACKET => write!(f, "TOK<LEFT-BRACKET>"),
      TokenType::RIGHT_BRACKET => write!(f, "TOK<RIGHT-BRACKET>"),
      TokenType::LESS_THAN => write!(f, "TOK<LESS-THAN>"),
      TokenType::GRT_THAN => write!(f, "TOK<GREATER-THAN>"),
      TokenType::EQUAL_EQUAL => write!(f, "TOK<EQUAL-EQUAL>"),
      TokenType::LESS_EQUAL => write!(f, "TOK<LESS-EQUAL>"),
      TokenType::GRT_EQUAL => write!(f, "TOK<GREATER-EQUAL>"),
      TokenType::EQUAL => write!(f, "TOK<EQUAL>"),
      TokenType::NOT_EQUAL => write!(f, "TOK<NOT-EQUAL>"),
      TokenType::SEMI_COLON => write!(f, "TOK<SEMI-COLON>"),
      TokenType::IDENT => write!(f, "TOK<IDENTIFIER>"),
    }
  }
}

impl Display for OpType {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      OpType::PLUS => write!(f, "+"),
      OpType::MINUS => write!(f, "-"),
      OpType::DIV => write!(f, "/"),
      OpType::MUL => write!(f, "*"),
      OpType::LEQ => write!(f, "<="),
      OpType::GEQ => write!(f, ">="),
      OpType::LT => write!(f, "<"),
      OpType::GT => write!(f, ">="),
      OpType::EQQ => write!(f, "=="),
      OpType::NEQ => write!(f, "!="),
      OpType::EQ => write!(f, "="),
    }
  }
}

impl TokenType {
  pub(crate) fn to_optype(&self) -> OpType {
    match self {
      TokenType::MINUS => OpType::MINUS,
      TokenType::PLUS => OpType::PLUS,
      TokenType::STAR => OpType::MUL,
      TokenType::FWD_SLASH => OpType::DIV,
      TokenType::EQUAL_EQUAL => OpType::EQQ,
      TokenType::LESS_EQUAL => OpType::LEQ,
      TokenType::GRT_EQUAL => OpType::GEQ,
      TokenType::NOT_EQUAL => OpType::NEQ,
      TokenType::GRT_THAN => OpType::GT,
      TokenType::LESS_THAN => OpType::LT,
      TokenType::EQUAL => OpType::EQ,
      _ => panic!("{} is not an operator", self.to_string()),
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
  pub fn t_type(&self) -> TokenType {
    self.t_type
  }

  pub fn value(&self) -> &'a str {
    self.value
  }

  pub fn equal(&self, t_type: TokenType) -> bool {
    self.t_type == t_type
  }

  pub fn is_error_token(&self) -> bool {
    self.error_code.is_some()
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

impl<'a> Default for Token<'a> {
  fn default() -> Self {
    Token::new("", TokenType::BOF, 1, 0, None)
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
    let ch_u8 = ch as u8;
    ch_u8 >= 'A' as u8 && ch_u8 <= 'Z' as u8
      || ch_u8 >= 'a' as u8 && ch_u8 <= 'z' as u8
      || ch == '_'
  }

  fn ident_type(&self, ident: &str) -> TokenType {
    match ident {
      // "break" | "true" | "false" => (true, TokenType::EOF), // todo
      _ => TokenType::IDENT,
    }
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

  fn lex_ident(&mut self) -> Token<'a> {
    while self.is_alpha(self.peek(None)) || self.is_digit(self.peek(None)) {
      self.advance();
    }
    let mut tok = self.create_token(TokenType::IDENT);
    tok.t_type = self.ident_type(tok.value);
    return tok;
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
    } else if self.is_alpha(ch) {
      return self.lex_ident();
    }
    match ch {
      '+' => self.create_token(TokenType::PLUS),
      '-' => self.create_token(TokenType::MINUS),
      '*' => self.create_token(TokenType::STAR),
      '/' => self.create_token(TokenType::FWD_SLASH),
      '(' => self.create_token(TokenType::LEFT_BRACKET),
      ')' => self.create_token(TokenType::RIGHT_BRACKET),
      ';' => self.create_token(TokenType::SEMI_COLON),
      '<' => {
        if self.peek(None) == '=' {
          self.advance();
          self.create_token(TokenType::LESS_EQUAL)
        } else {
          self.create_token(TokenType::LESS_THAN)
        }
      }
      '>' => {
        if self.peek(None) == '=' {
          self.advance();
          self.create_token(TokenType::GRT_EQUAL)
        } else {
          self.create_token(TokenType::GRT_THAN)
        }
      }
      '=' => {
        if self.peek(None) == '=' {
          self.advance();
          self.create_token(TokenType::EQUAL_EQUAL)
        } else {
          self.create_token(TokenType::EQUAL)
        }
      }
      '!' => {
        if self.peek(None) == '=' {
          self.advance();
          self.create_token(TokenType::NOT_EQUAL)
        } else {
          self.error_token(ViError::EL001)
        }
      }
      _ => self.error_token(ViError::EL001),
    }
  }
}
