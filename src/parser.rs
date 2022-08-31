use crate::ast::{
  AssignNode, AstNode, BinaryNode, BlockStmtNode, ExprStmtNode,
  ForLoopNode, FunctionNode, IfElseNode, NumberNode, ReturnNode, UnaryNode,
  VarDeclListNode, VarDeclNode, VarNode, WhileLoopNode,
};
use crate::errors::{ErrorInfo, ViError};
use crate::lexer::{Lexer, OpType, Token, TokenType};
use crate::types::{Type, TypeLiteral, TypeStack};
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::process::exit;
use std::rc::Rc;

#[derive(Debug)]
struct FnState {
  // fn_name: String, // todo
  locals: BTreeMap<String, i32>,
  types: Rc<RefCell<TypeStack>>,
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
        types: Rc::new(RefCell::new(TypeStack::new())),
      },
    }
  }

  fn error(&self, code: Option<ErrorInfo<'a>>) {
    // todo
    eprintln!(
      "Error at {} - {}",
      self.current_token,
      code
        .unwrap_or(
          self
            .current_token
            .error_code
            .unwrap_or(ViError::E0000)
            .to_info()
        )
        .error_msg
    );
    exit(-1);
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
      ty: RefCell::new(Rc::new(Type::new(TypeLiteral::TYPE_INT))),
    })
  }

  fn variable(&mut self) -> AstNode {
    let ty = self
      .current_state
      .types
      .borrow_mut()
      .lookup(&self.current_token.value());
    if ty.is_none() {
      self.error(Some(ViError::EP002.to_info()));
    }
    self.advance();
    AstNode::VarNode(VarNode {
      name: self.previous_token.value().into(),
      ty: RefCell::new(Rc::new(ty.unwrap())),
    })
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
    // unary = ("+" | "-" | "*" | "&") unary | primary
    match self.current_token.t_type() {
      TokenType::PLUS
      | TokenType::MINUS
      | TokenType::STAR
      | TokenType::AMP => {
        self.advance();
        let mut op = self.previous_token.t_type().to_optype();
        if op == OpType::MUL {
          op = OpType::DEREF;
        }
        let node = self.unary();
        AstNode::UnaryNode(UnaryNode {
          node: Box::new(node),
          op,
          ty: RefCell::new(Rc::new(Type::new(TypeLiteral::TYPE_NIL))),
        })
      }
      _ => self.primary(),
    }
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

  fn pointer_to(&self, sub: Type) -> Type {
    let ty = Type::new(TypeLiteral::TYPE_PTR);
    ty.subtype.borrow_mut().replace(RefCell::new(Rc::new(sub)));
    ty
  }

  fn declspec(&mut self) -> Type {
    // declspec = "int"
    self.consume(TokenType::INT);
    Type::new(TypeLiteral::TYPE_INT)
  }

  fn declarator(&mut self, ty: &Type) -> Type {
    // declarator = "*"* ident
    let mut ty = ty.clone();
    while self.match_tok(TokenType::STAR) {
      ty = self.pointer_to(ty);
    }
    self.consume(TokenType::IDENT);
    ty
  }

  fn declaration(&mut self) -> AstNode {
    // declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    let base_ty = self.declspec();
    let mut decls = vec![];
    let mut i = 0;
    while !self.match_tok(TokenType::SEMI_COLON) {
      if i > 0 {
        self.consume(TokenType::COMMA);
      }
      let ty = self.declarator(&base_ty);
      let name: String = self.previous_token.value().into();
      // insert type
      self
        .current_state
        .types
        .borrow_mut()
        .insert_type(name.clone(), ty.clone());
      // todo: multiple vars with same name
      // insert local
      if let None = self.current_state.locals.get(self.previous_token.value())
      {
        self
          .current_state
          .locals
          .insert(name.clone(), 1);
      }
      let var = VarNode {
        name,
        ty: RefCell::new(Rc::new(ty)),
      };
      if !self.match_tok(TokenType::EQUAL) {
        decls.push(VarDeclNode { var, value: None });
        continue;
      }
      let value = self.assign();
      decls.push(VarDeclNode {
        var,
        value: Some(Box::new(value)),
      });
      i += 1;
    }
    if decls.len() == 1 {
      return AstNode::VarDeclNode(decls.pop().unwrap());
    }
    AstNode::VarDeclListNode(VarDeclListNode { decls })
  }

  fn compound_stmt(&mut self) -> AstNode {
    // compound-stmt = (declaration | stmt)* "}"
    let mut block = BlockStmtNode { stmts: vec![] };
    while !self.match_tok(TokenType::RIGHT_CURLY) {
      if self.current_token.equal(TokenType::INT) {
        block.stmts.push(self.declaration());
      } else {
        block.stmts.push(self.stmt());
      }
    }
    AstNode::BlockStmtNode(block)
  }

  fn empty_stmt(&self) -> AstNode {
    AstNode::BlockStmtNode(BlockStmtNode { stmts: vec![] })
  }

  fn stmt(&mut self) -> AstNode {
    // stmt = "for" "(" expr-stmt expr? ";" expr? ")" stmt
    //          | "while" "(" expr ")" stmt
    //          | if "(" expr ")" stmt ("else" stmt)?
    //          | "return" expr ";"
    //          | "{" compound-stmt
    //          | expr-stmt
    match self.current_token.t_type() {
      TokenType::WHILE => {
        self.advance();
        self.consume(TokenType::LEFT_BRACKET);
        let condition = self.expr();
        self.consume(TokenType::RIGHT_BRACKET);
        let block = self.stmt();
        AstNode::WhileLoopNode(WhileLoopNode {
          condition: Box::new(condition),
          body: Box::new(block),
        })
      }
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
          body: Box::new(block),
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
        types: self.current_state.types.clone(),
        ty: RefCell::new(Rc::new(Type::new(TypeLiteral::TYPE_INT))), // todo: use func signature
      })
    } else {
      panic!("expected BlockStmtNode node")
    }
  }
}
