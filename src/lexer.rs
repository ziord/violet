use crate::errors::ViError;
use std::fmt::Formatter;
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[allow(non_camel_case_types)]
pub enum TokenType {
  NUM,
  PLUS,              // +
  MINUS,             // -
  STAR,              // *
  FWD_SLASH,         // /
  LEFT_BRACKET,      // (
  RIGHT_BRACKET,     // )
  LEFT_SQR_BRACKET,  // [
  RIGHT_SQR_BRACKET, // ]
  LESS_THAN,         // <
  GRT_THAN,          // >
  EQUAL_EQUAL,       // ==
  NOT_EQUAL,         // !=
  LESS_EQUAL,        // <=
  GRT_EQUAL,         // >=
  EQUAL,             // =
  SEMI_COLON,        // ;
  COMMA,             // ,
  IDENT,             // id
  LEFT_CURLY,        // {
  RIGHT_CURLY,       // }
  AMP,               // &
  RETURN,            // return
  SIZEOF,            //sizeof
  IF,                // if
  ELSE,              // else
  FOR,               // for
  WHILE,             // while
  INT,               // int
  CHAR,              // char
  STRING,            // "..."
  BOF,               // |-
  EOF,               // -|
  ERROR,
}

#[derive(Debug, PartialOrd, PartialEq)]
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
  ADDR,  // &
  DEREF, // *
}

#[derive(Debug, Copy, Clone)]
pub struct Token<'a> {
  t_type: TokenType,
  value: &'a str,
  pub(crate) line: i32,
  pub(crate) column: i32,
  pub(crate) has_esc: bool,
  pub(crate) error_code: Option<ViError>,
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
      TokenType::COMMA => write!(f, "TOK<COMMA>"),
      TokenType::FWD_SLASH => write!(f, "TOK<FWD-SLASH>"),
      TokenType::LEFT_BRACKET => write!(f, "TOK<LEFT-BRACKET>"),
      TokenType::RIGHT_BRACKET => write!(f, "TOK<RIGHT-BRACKET>"),
      TokenType::LEFT_SQR_BRACKET => write!(f, "TOK<LEFT-SQUARE-BRACKET>"),
      TokenType::RIGHT_SQR_BRACKET => {
        write!(f, "TOK<RIGHT-SQUARE-BRACKET>")
      }
      TokenType::LESS_THAN => write!(f, "TOK<LESS-THAN>"),
      TokenType::GRT_THAN => write!(f, "TOK<GREATER-THAN>"),
      TokenType::EQUAL_EQUAL => write!(f, "TOK<EQUAL-EQUAL>"),
      TokenType::LESS_EQUAL => write!(f, "TOK<LESS-EQUAL>"),
      TokenType::GRT_EQUAL => write!(f, "TOK<GREATER-EQUAL>"),
      TokenType::EQUAL => write!(f, "TOK<EQUAL>"),
      TokenType::NOT_EQUAL => write!(f, "TOK<NOT-EQUAL>"),
      TokenType::SEMI_COLON => write!(f, "TOK<SEMI-COLON>"),
      TokenType::AMP => write!(f, "TOK<AMP>"),
      TokenType::IDENT => write!(f, "TOK<IDENTIFIER>"),
      TokenType::RETURN => write!(f, "TOK<RETURN>"),
      TokenType::SIZEOF => write!(f, "TOK<SIZEOF>"),
      TokenType::IF => write!(f, "TOK<IF>"),
      TokenType::ELSE => write!(f, "TOK<ELSE>"),
      TokenType::FOR => write!(f, "TOK<FOR>"),
      TokenType::WHILE => write!(f, "TOK<WHILE>"),
      TokenType::INT => write!(f, "TOK<INT>"),
      TokenType::CHAR => write!(f, "TOK<CHAR>"),
      TokenType::STRING => write!(f, "TOK<STRING>"),
      TokenType::LEFT_CURLY => write!(f, "TOK<LEFT-CURLY>"),
      TokenType::RIGHT_CURLY => write!(f, "TOK<RIGHT-CURLY>"),
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
      OpType::ADDR => write!(f, "&"),
      OpType::DEREF => write!(f, "*"),
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
      TokenType::AMP => OpType::ADDR,
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
    esc: bool,
    error: Option<ViError>,
  ) -> Self {
    Self {
      t_type,
      line,
      column,
      has_esc: esc,
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
      "Token(value='{}', type={}, column={}, line={})",
      self.value, self.t_type, self.column, self.line
    )
  }
}

impl<'a> Default for Token<'a> {
  fn default() -> Self {
    Token::new("", TokenType::BOF, 1, 0, false, None)
  }
}

impl<'a, 'b> Lexer<'a, 'b> {
  pub fn new(src: &'a str) -> Self {
    let kwds = [
      ("return", TokenType::RETURN),
      ("sizeof", TokenType::SIZEOF),
      ("if", TokenType::IF),
      ("else", TokenType::ELSE),
      ("for", TokenType::FOR),
      ("while", TokenType::WHILE),
      ("int", TokenType::INT),
      ("char", TokenType::CHAR),
    ];
    Self {
      src,
      at_error: false,
      line: 1,
      column: 1,
      start: 0,
      current: 0,
      keywords: HashMap::from(kwds),
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
    if let Some(t_type) = self.keywords.get(ident) {
      *t_type
    } else {
      TokenType::IDENT
    }
  }

  fn at_end(&self) -> bool {
    self.current >= self.src.len()
  }

  fn create_token(&self, t_type: TokenType) -> Token<'a> {
    let val = &self.src[self.start..self.current];
    Token::new(val, t_type, self.line, self.column, false, None)
  }

  fn eof_token(&self) -> Token<'a> {
    Token::new("", TokenType::EOF, self.line, self.column, false, None)
  }

  fn error_token(&mut self, code: ViError) -> Token<'a> {
    self.at_error = true;
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
      Some(idx) => self.src.as_bytes()[self.current + idx] as char,
      None => self.src.as_bytes()[self.current] as char,
    }
  }

  fn skip_whitespace(&mut self) -> Result<(), Token<'a>> {
    loop {
      match self.peek(None) {
        ' ' | '\n' | '\t' | '\r' => {
          self.advance();
        }
        '/' => {
          let next = self.peek(Some(1));
          if next == '/' {
            let res = self.skip_comment(true);
            if res.is_err() {
              return res;
            }
          } else if next == '*' {
            let res = self.skip_comment(false);
            if res.is_err() {
              return res;
            }
          } else {
            break;
          }
        }
        _ => break,
      }
    }
    Ok(())
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

  fn skip_comment(&mut self, is_line: bool) -> Result<(), Token<'a>> {
    // skip '/' or '*'
    self.advance();
    if is_line {
      while self.peek(None) != '\n' {
        if self.at_end() {
          return Ok(());
        }
        self.advance();
      }
      // skip '\n'
      self.advance();
      return Ok(());
    }
    let mut closed = false;
    while !self.at_end() {
      if self.peek(None) == '*' && self.peek(Some(1)) == '/' {
        closed = true;
        self.current += 2;
        break;
      }
      self.advance();
    }
    if !closed {
      return Err(self.error_token(ViError::EL003));
    }
    Ok(())
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

  fn lex_string(&mut self) -> Token<'a> {
    // exclude starting '"'
    let start = self.current;
    let bytes = self.src.as_bytes();
    let mut has_esc = false;
    while bytes[self.current] as char != '"' {
      let ch = bytes[self.current] as char;
      if ch == '\n' || self.at_end() {
        return self.error_token(ViError::EL002);
      } else if ch == '\\' {
        has_esc = true;
        // escape the next char; handles any char to be escaped.
        self.current += 1;
      }
      self.advance();
    }
    self.start = start;
    let mut token = self.create_token(TokenType::STRING);
    token.has_esc = has_esc;
    self.advance(); // skip the closing '"'
    token
  }

  pub fn get_token(&mut self) -> Token<'a> {
    if let Err(tok) = self.skip_whitespace() {
      return tok;
    }
    if self.at_end() {
      return self.eof_token();
    } else if self.at_error {
      return self.error_token(ViError::EL000);
    }
    self.start = self.current;
    let ch = self.advance();
    if self.is_digit(ch) {
      return self.lex_number();
    } else if self.is_alpha(ch) {
      return self.lex_ident();
    }
    match ch {
      ',' => self.create_token(TokenType::COMMA),
      '+' => self.create_token(TokenType::PLUS),
      '-' => self.create_token(TokenType::MINUS),
      '*' => self.create_token(TokenType::STAR),
      '&' => self.create_token(TokenType::AMP),
      '/' => self.create_token(TokenType::FWD_SLASH),
      '(' => self.create_token(TokenType::LEFT_BRACKET),
      ')' => self.create_token(TokenType::RIGHT_BRACKET),
      '[' => self.create_token(TokenType::LEFT_SQR_BRACKET),
      ']' => self.create_token(TokenType::RIGHT_SQR_BRACKET),
      ';' => self.create_token(TokenType::SEMI_COLON),
      '{' => self.create_token(TokenType::LEFT_CURLY),
      '}' => self.create_token(TokenType::RIGHT_CURLY),
      '"' => self.lex_string(),
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
