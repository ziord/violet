use crate::ast::{
  AssignNode, AstNode, BinaryNode, BlockStmtNode, ExprStmtNode,
  ForLoopNode, FunctionNode, IfElseNode, NumberNode, ReturnNode, UnaryNode,
  VarNode,
};
use crate::errors::{ErrorInfo, ViError};
use crate::lexer::{Lexer, Token, TokenType};
use std::cell::Cell;
use std::collections::BTreeMap;

#[derive(Debug)]
struct FnState {
  // fn_name: String, // todo
  locals: BTreeMap<String, i32>,
}

#[derive(Debug)]
pub(crate) struct Parser<'a, 'b> {
  lexer: Lexer<'a, 'b>,
  current_token: Token<'a>,
  previous_token: Token<'a>,
  current_state: FnState,
}

impl<'a, 'b> Parser<'a, 'b> {
  pub fn new(src: &'a str) -> Self {
    Self {
      lexer: Lexer::new(src),
      current_token: Token::default(),
      previous_token: Token::default(),
      current_state: FnState {
        locals: BTreeMap::new(),
      },
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

  fn match_tok(&mut self, t_type: TokenType) -> bool {
    if self.current_token.equal(t_type) {
      self.advance();
      true
    } else {
      false
    }
  }

  fn num(&mut self) -> AstNode {
    self.consume(TokenType::NUM);
    AstNode::NumberNode(NumberNode {
      value: self.previous_token.to_int(),
    })
  }

  fn variable(&mut self) -> AstNode {
    self.advance();
    let ident = AstNode::VarNode(VarNode {
      name: self.previous_token.value().into(),
    });
    // todo: multiple vars with same name
    if let None = self.current_state.locals.get(self.previous_token.value())
    {
      self
        .current_state
        .locals
        .insert(self.previous_token.value().into(), 1);
    }
    ident
  }

  fn primary(&mut self) -> AstNode {
    // primary = "(" expr ")" | ident | num
    if self.match_tok(TokenType::LEFT_BRACKET) {
      let node = self.expr();
      self.consume(TokenType::RIGHT_BRACKET);
      return node;
    } else if self.current_token.equal(TokenType::IDENT) {
      self.variable()
    } else {
      self.num()
    }
  }

  fn unary(&mut self) -> AstNode {
    // unary = ("+" | "-") unary | primary
    if self.match_tok(TokenType::PLUS) || self.match_tok(TokenType::MINUS) {
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
    while self.match_tok(TokenType::STAR)
      || self.match_tok(TokenType::FWD_SLASH)
    {
      let op = self.previous_token.t_type().to_optype();
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
    while self.match_tok(TokenType::PLUS)
      || self.match_tok(TokenType::MINUS)
    {
      let op = self.previous_token.t_type().to_optype();
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
    while self.match_tok(TokenType::EQUAL_EQUAL)
      || self.match_tok(TokenType::NOT_EQUAL)
    {
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

  fn assign(&mut self) -> AstNode {
    // assign = equality ("=" assign)?
    let left = self.equality();
    if self.match_tok(TokenType::EQUAL) {
      let op = self.previous_token.t_type().to_optype();
      let right = self.assign();
      return AstNode::AssignNode(AssignNode {
        left_node: Box::new(left),
        right_node: Box::new(right),
        op,
      });
    }
    left
  }

  fn expr(&mut self) -> AstNode {
    // expr = assign
    self.assign()
  }

  fn expr_stmt(&mut self) -> AstNode {
    // expr-stmt = expr? ";"
    if self.match_tok(TokenType::SEMI_COLON) {
      return self.empty_stmt();
    }
    let node = self.expr();
    self.consume(TokenType::SEMI_COLON);
    AstNode::ExprStmtNode(ExprStmtNode {
      node: Box::new(node),
    })
  }

  fn compound_stmt(&mut self) -> AstNode {
    let mut block = BlockStmtNode { stmts: vec![] };
    while !self.match_tok(TokenType::RIGHT_CURLY) {
      block.stmts.push(self.stmt());
    }
    AstNode::BlockStmtNode(block)
  }

  fn empty_stmt(&self) -> AstNode {
    AstNode::BlockStmtNode(BlockStmtNode { stmts: vec![] })
  }

  fn stmt(&mut self) -> AstNode {
    // stmt = "for" "(" expr-stmt expr? ";" expr? ")" stmt
    //          | if "(" expr ")" stmt ("else" stmt)?
    //          | "return" expr ";"
    //          | "{" compound-stmt
    //          | expr-stmt
    match self.current_token.t_type() {
      TokenType::FOR => {
        self.advance();
        let init;
        let condition;
        let incr;
        self.consume(TokenType::LEFT_BRACKET);
        if !self.match_tok(TokenType::SEMI_COLON) {
          init = self.stmt();
        } else {
          init = self.empty_stmt();
        }
        if !self.match_tok(TokenType::SEMI_COLON) {
          condition = self.expr_stmt();
        } else {
          condition = self.empty_stmt();
        }
        if !self.match_tok(TokenType::RIGHT_BRACKET) {
          incr = self.expr();
          self.consume(TokenType::RIGHT_BRACKET);
        } else {
          incr = self.empty_stmt();
        }
        let block = self.stmt();
        AstNode::ForLoopNode(ForLoopNode {
          init: Box::new(init),
          condition: Box::new(condition),
          incr: Box::new(incr),
          block: Box::new(block),
        })
      }
      TokenType::IF => {
        self.advance();
        self.consume(TokenType::LEFT_BRACKET);
        let condition = Box::new(self.expr());
        self.consume(TokenType::RIGHT_BRACKET);
        let if_block = Box::new(self.stmt());
        let else_block;
        if self.match_tok(TokenType::ELSE) {
          else_block = Box::new(self.stmt());
        } else {
          else_block = Box::new(self.empty_stmt())
        }
        return AstNode::IfElseNode(IfElseNode {
          condition,
          if_block,
          else_block,
        });
      }
      TokenType::RETURN => {
        self.advance();
        let node: AstNode = self.expr();
        self.consume(TokenType::SEMI_COLON);
        return AstNode::ReturnNode(ReturnNode {
          expr: Box::new(node),
        });
      }
      TokenType::LEFT_CURLY => {
        self.advance();
        self.compound_stmt()
      }
      _ => self.expr_stmt(),
    }
  }

  pub fn parse(&mut self) -> AstNode {
    self.advance();
    self.consume(TokenType::LEFT_CURLY);
    let list = self.compound_stmt();
    let mut locals = vec![];
    self.current_state.locals.iter().for_each(|(var, _)| {
      locals.push(var.clone()); // todo: should not clone
    });
    if let AstNode::BlockStmtNode(block) = list {
      AstNode::FunctionNode(FunctionNode {
        stack_size: Cell::new(0),
        body: block,
        locals,
      })
    } else {
      panic!("expected BlockStmtNode node")
    }
  }
}
