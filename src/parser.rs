use crate::ast::{AstNode, BinaryNode, NumberNode, UnaryNode};
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

  fn unary(&mut self) -> AstNode {
    // unary = ("+" | "-") unary | primary
    if self.current_token.equal(TokenType::PLUS)
      || self.current_token.equal(TokenType::MINUS)
    {
      self.advance();
      let op = self.previous_token.t_type().to_optype();
      let node = self.unary();
      return AstNode::UnaryNode(UnaryNode {
        node: Box::new(node),
        op,
      });
    }
    self.primary()
  }

  fn term(&mut self) -> AstNode {
    // term = unary ("*" primary | "/" unary)*
    let mut left = self.unary();
    while self.current_token.equal(TokenType::STAR)
      || self.current_token.equal(TokenType::F_SLASH)
    {
      let op = self.current_token.t_type().to_optype();
      self.advance();
      let right = self.unary();
      left = AstNode::BinaryNode(BinaryNode {
        left_node: Box::new(left),
        right_node: Box::new(right),
        op,
      });
    }
    left
  }

  fn additive(&mut self) -> AstNode {
    // additive = term ("+" term | "-" term)*
    let mut left = self.term();
    while self.current_token.equal(TokenType::PLUS)
      || self.current_token.equal(TokenType::MINUS)
    {
      let op = self.current_token.t_type().to_optype();
      self.advance();
      let right = self.term();
      left = AstNode::BinaryNode(BinaryNode {
        left_node: Box::new(left),
        right_node: Box::new(right),
        op,
      });
    }
    left
  }

  fn relational(&mut self) -> AstNode {
    // relational = additive ("<" additive | "<=" additive | ">" additive | ">=" additive)*
    let mut left = self.additive();
    loop {
      match self.current_token.t_type() {
        TokenType::L_THAN
        | TokenType::L_EQ
        | TokenType::G_THAN
        | TokenType::G_EQ => {
          self.advance();
          let op = self.previous_token.t_type().to_optype();
          let right = self.relational();
          left = AstNode::BinaryNode(BinaryNode {
            left_node: Box::new(left),
            right_node: Box::new(right),
            op,
          });
        }
        _ => break,
      }
    }
    left
  }

  fn equality(&mut self) -> AstNode {
    // equality = relational ("==" relational | "!=" relational)*
    let mut left = self.relational();
    while self.current_token.equal(TokenType::EQ_EQ)
      || self.current_token.equal(TokenType::N_EQ)
    {
      self.advance();
      let op = self.previous_token.t_type().to_optype();
      let right = self.relational();
      left = AstNode::BinaryNode(BinaryNode {
        left_node: Box::new(left),
        right_node: Box::new(right),
        op,
      });
    }
    left
  }

  fn expr(&mut self) -> AstNode {
    // expr = equality
    self.equality()
  }

  pub fn parse(&mut self) -> AstNode {
    self.advance();
    let node: AstNode = self.expr();
    self.consume(TokenType::EOF);
    return node;
  }
}
