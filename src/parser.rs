use crate::ast::{AstNode, BinaryNode, ExprStmtNode, NumberNode, StmtList, UnaryNode};
use crate::errors::{ErrorInfo, ViError};
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

  fn error(&self, code: Option<ErrorInfo>) {
    // todo
    eprintln!(
      "Error at {} - {}",
      self.current_token,
      code
        .unwrap_or(self.current_token.error_code.unwrap().to_info())
        .error_msg
    );
  }

  fn advance(&mut self) {
    self.previous_token = self.current_token;
    self.current_token = self.lexer.get_token();
    if self.current_token.is_error_token() {
      self.error(None);
    }
  }

  fn consume(&mut self, t_type: TokenType) {
    if self.current_token.equal(t_type) {
      self.advance();
    } else {
      let help_msg = format!(
        "Expected {}, found {}",
        t_type,
        self.current_token.t_type()
      );
      let mut info = ViError::EP001.to_info();
      info.help_msg = help_msg.as_str();
      self.error(Some(info));
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
    if self.current_token.equal(TokenType::LEFT_BRACKET) {
      self.consume(TokenType::LEFT_BRACKET);
      let node = self.expr();
      self.consume(TokenType::RIGHT_BRACKET);
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
      || self.current_token.equal(TokenType::FWD_SLASH)
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
        TokenType::LESS_THAN
        | TokenType::LESS_EQUAL
        | TokenType::GRT_THAN
        | TokenType::GRT_EQUAL => {
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
    while self.current_token.equal(TokenType::EQUAL_EQUAL)
      || self.current_token.equal(TokenType::NOT_EQUAL)
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

  fn expr_stmt(&mut self) -> AstNode {
    // expr-stmt = expr ";"
    let node = self.expr();
    self.consume(TokenType::SEMI_COLON);
    AstNode::ExprStmtNode(ExprStmtNode {
      node: Box::new(node),
    })
  }

  fn stmt(&mut self) -> AstNode {
    // stmt = expr-stmt
    self.expr_stmt()
  }

  pub fn parse(&mut self) -> AstNode {
    self.advance();
    let mut list = StmtList { stmts: vec![]};
    while !self.current_token.equal(TokenType::EOF) {
      list.stmts.push(self.stmt());
    }
    self.consume(TokenType::EOF);
    return AstNode::StmtList(list);
  }
}
