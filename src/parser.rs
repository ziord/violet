use crate::ast::{AstNode, BinaryNode, NumberNode};
use crate::lexer::{Lexer, Token, TokenType};

#[derive(Debug)]
pub(crate) struct Parser<'a, 'b> {
  lexer: Lexer<'a, 'b>,
  current_token: Token<'a>,
  previous_token: Token<'a>,
}

impl<'a, 'b> Parser<'a, 'b> {
  pub fn new(src: &'a str) -> Self {
    Self {
      lexer: Lexer::new(src),
      current_token: Token::default(),
      previous_token: Token::default(),
    }
  }

  fn error(&self) {
    // todo
    eprintln!(
      "Error at {} - {}",
      self.current_token,
      self.current_token.error_code.unwrap().to_info().error_msg
    );
  }

  fn advance(&mut self) {
    self.previous_token = self.current_token;
    self.current_token = self.lexer.get_token();
    if self.current_token.is_error_token() {
      self.error();
    }
  }

  fn consume(&mut self, t_type: TokenType) {
    if self.current_token.equal(t_type) {
      self.advance();
    } else {
      self.error();
    }
  }

  fn num(&mut self) -> AstNode {
    self.consume(TokenType::NUM);
    AstNode::NumberNode(NumberNode {
      value: self.previous_token.to_int(),
    })
  }

  fn primary(&mut self) -> AstNode {
    // primary = "(" expr ")" | num
    if self.current_token.equal(TokenType::L_BRACKET) {
      self.consume(TokenType::L_BRACKET);
      let node = self.expr();
      self.consume(TokenType::R_BRACKET);
      return node;
    } else {
      self.num()
    }
  }

  fn term(&mut self) -> AstNode {
    // term = primary ("*" primary | "/" primary)*
    let mut left = self.primary();
    while self.current_token.equal(TokenType::STAR)
      || self.current_token.equal(TokenType::F_SLASH)
    {
      let op = self.current_token.get_type().to_optype();
      self.advance();
      let right = self.primary();
      left = AstNode::BinaryNode(BinaryNode {
        left: Box::new(left),
        right: Box::new(right),
        op,
      });
    }
    left
  }

  fn expr(&mut self) -> AstNode {
    // expr = term ("+" term | "-" term)*
    let mut left = self.term();
    while self.current_token.equal(TokenType::PLUS)
      || self.current_token.equal(TokenType::MINUS)
    {
      let op = self.current_token.get_type().to_optype();
      self.advance();
      let right = self.term();
      left = AstNode::BinaryNode(BinaryNode {
        left: Box::new(left),
        right: Box::new(right),
        op,
      });
    }
    left
  }

  pub fn parse(&mut self) -> AstNode {
    self.advance();
    self.expr()
  }
}