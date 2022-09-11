use crate::ast::{
  AssignNode, AstNode, BinaryNode, BlockStmtNode, ExprStmtNode, FnCallNode,
  ForLoopNode, FunctionNode, IfElseNode, NumberNode, ProgramNode,
  ReturnNode, SizeofNode, UnaryNode, VarDeclListNode, VarDeclNode, VarNode,
  WhileLoopNode,
};
use crate::errors::{ErrorInfo, ViError};
use crate::lexer::{Lexer, OpType, Token, TokenType};
use crate::types::{TParam, Type, TypeLiteral};
use std::cell::{Cell, RefCell};
use std::process::exit;
use std::rc::Rc;

#[derive(Debug)]
pub(crate) struct Parser<'a, 'b> {
  lexer: Lexer<'a, 'b>,
  current_token: Token<'a>,
  previous_token: Token<'a>,
  locals: Vec<(Rc<Type>, String)>,
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

  fn find_var_type(&self, name: &str) -> Rc<Type> {
    for (var_ty, var_name) in &self.locals {
      if var_name == name {
        return var_ty.clone();
      }
    }
    // todo: need to handle this
    panic!("variable '{}' is not defined in the current scope", name)
  }

  fn num(&mut self) -> AstNode {
    self.consume(TokenType::NUM);
    AstNode::NumberNode(NumberNode {
      value: self.previous_token.to_int(),
      ty: RefCell::new(Rc::new(Type::new(TypeLiteral::TYPE_INT))),
    })
  }

  fn variable(&mut self) -> AstNode {
    let name: String = self.previous_token.value().into();
    let ty = RefCell::new(self.find_var_type(&name));
    AstNode::VarNode(VarNode { name, ty })
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
    // primary = "(" expr ")" | "sizeof" unary | ident args? | num
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
    } else if self.match_tok(TokenType::SIZEOF) {
      AstNode::SizeofNode(SizeofNode {
        size: Cell::new(0),
        node: Box::new(self.unary()),
      })
    } else {
      self.num()
    }
  }

  fn postfix(&mut self) -> AstNode {
    // postfix = primary ("[" expr "]")*
    let mut node = self.primary();
    while self.match_tok(TokenType::LEFT_SQR_BRACKET) {
      // x[y] is a sugar for *(x+y)
      let index = self.expr();
      self.consume(TokenType::RIGHT_SQR_BRACKET);
      let tmp = UnaryNode {
        op: OpType::DEREF,
        node: Box::new(AstNode::BinaryNode(BinaryNode {
          left_node: Box::new(node),
          right_node: Box::new(index),
          op: OpType::PLUS,
        })),
        ty: RefCell::new(Rc::new(Type::default())),
      };
      node = AstNode::UnaryNode(tmp);
    }
    node
  }

  fn unary(&mut self) -> AstNode {
    // unary = ("+" | "-" | "*" | "&") unary
    //       | postfix
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
          ty: RefCell::new(Rc::new(Type::default())),
        })
      }
      _ => self.postfix(),
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

  fn declspec(&mut self) -> Type {
    // declspec = "int"
    self.consume(TokenType::INT);
    Type::new(TypeLiteral::TYPE_INT)
  }

  fn func_type(
    &mut self,
    ty: &Type,
    params: Vec<VarDeclNode>,
  ) -> (Type, Option<Vec<VarDeclNode>>) {
    let mut func_ty = Type::new(TypeLiteral::TYPE_FUNC);
    // return type
    func_ty
      .subtype
      .borrow_mut()
      .replace(RefCell::new(Rc::new(ty.clone())));
    if params.len() > 0 {
      // associate params type with func type
      let mut params_ty = vec![];
      for param in &params {
        params_ty.push(TParam {
          name: param.name.clone(),
          ty: param.ty.borrow().clone(),
        });
      }
      func_ty.params.replace(RefCell::new(params_ty));
    }
    (func_ty, Some(params))
  }

  fn func_params(&mut self, ty: &Type) -> (Type, Option<Vec<VarDeclNode>>) {
    // func-params = (param ("," param)*)? ")"
    // param       = declspec declarator
    let mut i = 0;
    let mut params = vec![];
    while !self.match_tok(TokenType::RIGHT_BRACKET) {
      // func-params
      if i > 0 {
        self.consume(TokenType::COMMA);
      }
      let base_ty = self.declspec();
      let ((ty, _), name) = self.declarator(&base_ty);
      let ty = Rc::new(ty);
      // make parameters locally scoped to the function
      self.locals.push((ty.clone(), name.clone()));
      params.push(VarDeclNode {
        ty: RefCell::new(ty),
        name,
        value: None,
      });
      i += 1;
    }
    self.func_type(ty, params)
  }

  fn type_suffix(&mut self, ty: &Type) -> (Type, Option<Vec<VarDeclNode>>) {
    // type-suffix = "(" func-params
    //             | "[" num "]"
    //             | ε
    if self.match_tok(TokenType::LEFT_BRACKET) {
      self.func_params(ty)
    } else if self.match_tok(TokenType::LEFT_SQR_BRACKET) {
      self.consume(TokenType::NUM);
      let len: u32 = self
        .previous_token
        .value()
        .parse()
        .expect("array size should be an unsigned integer");
      self.consume(TokenType::RIGHT_SQR_BRACKET);
      let (ty, _) = self.type_suffix(ty);
      (Type::array_of(ty, len), None)
    } else {
      (ty.clone(), None)
    }
  }

  fn declarator(
    &mut self,
    ty: &Type,
  ) -> ((Type, Option<Vec<VarDeclNode>>), String) {
    // declarator = "*"* ident type-suffix
    let mut ty = ty.clone();
    while self.match_tok(TokenType::STAR) {
      ty = Type::pointer_to(ty);
    }
    self.consume(TokenType::IDENT);
    let name = self.previous_token.value().into();
    // = | ; -> var decl or ( -> func
    let suffixes = self.type_suffix(&ty);
    (suffixes, name)
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
      let ((ty, _params), name) = self.declarator(&base_ty);
      let ty = RefCell::new(Rc::new(ty));
      // insert local
      self.locals.push((ty.borrow().clone(), name.clone()));
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
    // create new fn state
    self.enter();
    let ty = self.declspec();
    let ((ty, params), name) = self.declarator(&ty);
    self.consume(TokenType::LEFT_CURLY);
    let list = self.compound_stmt();
    // leave fn state
    self.leave(&name);
    if let AstNode::BlockStmtNode(block) = list {
      AstNode::FunctionNode(FunctionNode {
        name,
        params: params.unwrap_or(vec![]),
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
