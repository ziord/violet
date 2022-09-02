use crate::ast::{
  AssignNode, AstNode, BinaryNode, BlockStmtNode, ExprStmtNode, FnCallNode,
  ForLoopNode, FunctionNode, IfElseNode, NumberNode, ProgramNode,
  ReturnNode, UnaryNode, VarDeclListNode, VarDeclNode, VarNode,
  WhileLoopNode,
};
use crate::errors::{ErrorInfo, ViError};
use crate::lexer::{Lexer, OpType, Token, TokenType};
use crate::types::{Type, TypeLiteral};
use std::cell::{Cell, RefCell};
use std::process::exit;
use std::rc::Rc;

#[derive(Debug)]
pub(crate) struct Parser<'a, 'b> {
  lexer: Lexer<'a, 'b>,
  current_token: Token<'a>,
  previous_token: Token<'a>,
  locals: Vec<String>,
}

impl<'a, 'b> Parser<'a, 'b> {
  pub fn new(src: &'a str) -> Self {
    Self {
      lexer: Lexer::new(src),
      current_token: Token::default(),
      previous_token: Token::default(),
      locals: vec![],
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

  fn enter(&mut self) {
    self.locals.clear();
  }

  fn leave(&mut self, _fn_name: &String) {
    // todo
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
    let name = self.previous_token.value().into();
    AstNode::VarNode(VarNode { name })
  }

  fn call(&mut self, name: &str) -> AstNode {
    let name: String = name.into();
    // args
    let mut args: Vec<AstNode> = vec![];
    if !self.match_tok(TokenType::RIGHT_BRACKET) {
      let mut i = 0;
      while !self.match_tok(TokenType::RIGHT_BRACKET) {
        if i > 0 {
          self.consume(TokenType::COMMA);
        }
        args.push(self.assign());
        i += 1;
      }
    }
    AstNode::FnCallNode(FnCallNode { name, args })
  }

  fn primary(&mut self) -> AstNode {
    // primary = "(" expr ")" | ident args? | num
    // args = "(" ")"
    if self.match_tok(TokenType::LEFT_BRACKET) {
      let node = self.expr();
      self.consume(TokenType::RIGHT_BRACKET);
      return node;
    } else if self.current_token.equal(TokenType::IDENT) {
      let name = self.current_token.value();
      self.advance();
      if self.match_tok(TokenType::LEFT_BRACKET) {
        self.call(name)
      } else {
        self.variable()
      }
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

  fn func_type(&mut self, ty: &Type) -> Type {
    let func_ty = Type::new(TypeLiteral::TYPE_FUNC);
    // return type
    func_ty
      .subtype
      .borrow_mut()
      .replace(RefCell::new(Rc::new(ty.clone())));
    func_ty
  }

  fn type_suffix(&mut self, ty: &Type) -> Type {
    // type-suffix = ("(" func-params)?
    if self.match_tok(TokenType::LEFT_BRACKET) {
      // todo: func param types should be sorted out here
      self.consume(TokenType::RIGHT_BRACKET);
      self.func_type(ty)
    } else {
      ty.clone()
    }
  }

  fn declarator(&mut self, ty: &Type) -> (Type, String) {
    // declarator = "*"* ident type-suffix
    let mut ty = ty.clone();
    while self.match_tok(TokenType::STAR) {
      ty = self.pointer_to(ty);
    }
    self.consume(TokenType::IDENT);
    let name = self.previous_token.value().into();
    // = | ; -> var decl or ( -> func
    ty = self.type_suffix(&ty);
    (ty, name)
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
      let (ty, name) = self.declarator(&base_ty);
      let ty = RefCell::new(Rc::new(ty));
      // insert local
      self.locals.push(name.clone());
      if !self.match_tok(TokenType::EQUAL) {
        decls.push(VarDeclNode {
          name,
          ty,
          value: None,
        });
        continue;
      }
      let value = self.assign();
      decls.push(VarDeclNode {
        name,
        ty,
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

  fn function(&mut self) -> AstNode {
    let ty = self.declspec();
    let (ty, name) = self.declarator(&ty);
    // create new fn state
    self.enter();
    self.consume(TokenType::LEFT_CURLY);
    let list = self.compound_stmt();
    // leave fn state
    self.leave(&name);
    if let AstNode::BlockStmtNode(block) = list {
      AstNode::FunctionNode(FunctionNode {
        name,
        stack_size: Cell::new(0),
        body: block,
        locals: std::mem::take(&mut self.locals),
        ty: RefCell::new(Rc::new(ty)),
      })
    } else {
      panic!("expected BlockStmtNode node")
    }
  }

  pub fn parse(&mut self) -> AstNode {
    self.advance();
    let mut decls = vec![];
    while !self.match_tok(TokenType::EOF) {
      decls.push(self.function());
    }
    AstNode::ProgramNode(ProgramNode { decls })
  }
}
