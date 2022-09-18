use crate::ast::*;
use crate::errors::{ErrorInfo, ViError};
use crate::lexer::{Lexer, OpType, Token, TokenType};
use crate::types::{TParam, Type, TypeLiteral};
use crate::unbox;
use std::borrow::BorrowMut;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, VecDeque};
use std::process::exit;
use std::rc::Rc;

#[derive(Debug)]
struct Scope<K, V> {
  level: Cell<i32>,
  items: RefCell<BTreeMap<K, V>>,
  enclosing: Option<RefCell<Rc<Scope<K, V>>>>,
}

#[derive(Debug)]
pub(crate) struct Parser<'a, 'b> {
  lexer: Lexer<'a, 'b>,
  current_token: Token<'a>,
  previous_token: Token<'a>,
  // name, type, scope
  locals: Vec<(String, Rc<Type>, i32)>,
  // type, name, init_data (string literal)
  globals: Vec<(Rc<Type>, String, Option<String>)>,
  current_scope: Rc<Scope<String, Rc<Type>>>,
}

impl<K, V> Scope<K, V> {
  fn new() -> Self {
    Self {
      level: Cell::new(0),
      items: RefCell::new(BTreeMap::new()),
      enclosing: (None),
    }
  }
}

impl<'a, 'b> Parser<'a, 'b> {
  pub fn new(src: &'a str) -> Self {
    Self {
      lexer: Lexer::new(src),
      current_token: Token::default(),
      previous_token: Token::default(),
      locals: Vec::new(),
      current_scope: Rc::new(Scope::new()),
      globals: vec![],
    }
  }

  fn error(&self, code: Option<ErrorInfo<'a>>) {
    // todo
    let info = self.current_token.error_code.unwrap_or(ViError::E0000);
    let info = code.unwrap_or(info.to_info());
    eprintln!("Error at {} - {}", self.current_token, info.error_msg);
    if !info.help_msg.is_empty() {
      eprintln!("Help: {}", info.help_msg);
    }
    exit(-1);
  }

  fn enter_scope(&mut self) {
    let mut other = Scope::new();
    other
      .enclosing
      .borrow_mut()
      .replace(RefCell::new(self.current_scope.clone()));
    let level = self.current_scope.level.get();
    self.current_scope = Rc::new(other);
    self.current_scope.level.set(level + 1);
  }

  fn leave_scope(&mut self) {
    let p = self
      .current_scope
      .enclosing
      .as_ref()
      .unwrap()
      .borrow()
      .clone();
    self.current_scope = p;
  }

  fn push_scope(&mut self, name: &str, ty: &Rc<Type>) {
    self
      .current_scope
      .items
      .borrow_mut()
      .insert(name.into(), ty.clone());
  }

  fn gen_id(&self) -> String {
    format!(".L.glob.{}", self.globals.len())
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

  fn store(&mut self, name: &String, ty: &Rc<Type>) -> i32 {
    let scope = self.current_scope.level.get();
    self.locals.push((name.clone(), ty.clone(), scope));
    self.push_scope(name, ty);
    scope
  }

  fn store_global(
    &mut self,
    name: &String,
    ty: &Rc<Type>,
    data: Option<String>,
  ) {
    self.globals.push((ty.clone(), name.clone(), data));
    // don't push into current scope; reserve current scope for locals
  }

  fn find_var_type(&self, name: &String) -> (Rc<Type>, i32) {
    let mut scope = self.current_scope.clone();
    loop {
      if let Some(v) = scope.items.borrow().get(name) {
        return (v.clone(), scope.level.get());
      }
      if scope.enclosing.is_none() {
        break;
      }
      let tmp = scope.enclosing.as_ref().unwrap().borrow().clone();
      scope = tmp;
    }
    for (var_ty, var_name, _data) in &self.globals {
      if var_name == name {
        return (var_ty.clone(), -1); // global -> -1
      }
    }
    // todo: need to handle this
    panic!("variable '{}' is not defined in the current scope", name)
  }

  fn convert_hex(&self, c: char) -> u32 {
    if '0' <= c && c <= '9' {
      return c as u32 - '0' as u32;
    }
    if 'a' <= c && c <= 'f' {
      return c as u32 - 'a' as u32 + 10;
    }
    c as u32 - 'A' as u32 + 10
  }

  fn process_str_literal(&self) -> String {
    if !self.previous_token.has_esc {
      let mut s: String = self.previous_token.value().into();
      s.push('\0');
      return s;
    }
    let bytes = self.previous_token.value().as_bytes();
    let mut string = String::new();
    let mut i = 0;
    while i < bytes.len() && bytes[i] as char != '"' {
      let ch = bytes[i] as char;
      if ch == '\\' {
        // check for octal sequence \ooo
        let mut oc = bytes[i + 1] as char;
        if '0' <= oc && oc <= '7' {
          let mut c = oc as u32 - '0' as u32;
          let mut j = 0;
          i += 2;
          while j < 2 && i < bytes.len() {
            oc = bytes[i] as char;
            if '0' <= oc && oc <= '7' {
              c = (c << 3) + (oc as u32 - '0' as u32);
              i += 1;
            }
            j += 1;
          }
          unsafe {
            string.as_mut_vec().extend_from_slice(&[c as u8]);
          }
          continue;
        } else if oc == 'x' {
          // check for hex sequence \x[a-fA-F0-9]*
          if i + 2 >= bytes.len()
            || !char::is_ascii_hexdigit(&(bytes[i + 2] as char))
          {
            self.error(Some(ViError::EP003.to_info()));
          }
          i += 2;
          let mut c = 0;
          while i < bytes.len()
            && char::is_ascii_hexdigit(&(bytes[i] as char))
          {
            c = (c << 4) + self.convert_hex(bytes[i] as char);
            i += 1;
          }
          unsafe {
            string.as_mut_vec().extend_from_slice(&[c as u8]);
          }
          continue;
        }
        match bytes[i + 1] as char {
          'a' => string.push(7 as char),
          'b' => string.push(8 as char),
          'f' => string.push(12 as char),
          'n' => string.push('\n'),
          'r' => string.push('\r'),
          't' => string.push('\t'),
          'v' => string.push(11 as char),
          // [GNU] \e for the ASCII escape character is a GNU C extension.
          'e' => string.push(27 as char),
          _ => {
            string.push(bytes[i + 1] as char);
          }
        }
        i += 1;
      } else {
        string.push(ch);
      }
      i += 1;
    }
    string.push('\0');
    string
  }

  fn is_typename(&self) -> bool {
    match self.current_token.t_type() {
      TokenType::INT | TokenType::CHAR => true,
      _ => false,
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
    let name: String = self.previous_token.value().into();
    let (ty, scope) = self.find_var_type(&name);
    let ty = RefCell::new(ty);
    AstNode::VarNode(VarNode { name, ty, scope })
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
    // primary = "({" stmt+ "})"
    //          | "(" expr ")"
    //          | "sizeof" unary
    //          | ident func-args?
    //          | num
    //          | str
    if self.match_tok(TokenType::LEFT_BRACKET) {
      if self.match_tok(TokenType::LEFT_CURLY) {
        if self.current_token.equal(TokenType::RIGHT_CURLY) {
          self.error(Some(ViError::EP004.to_info()));
        }
        let block = self.compound_stmt();
        let stmts = unbox!(BlockStmtNode, block).stmts;
        let node = AstNode::StmtExprNode(StmtExprNode { stmts });
        self.consume(TokenType::RIGHT_BRACKET);
        return node;
      }
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
    } else if self.match_tok(TokenType::STRING) {
      // create a new global variable, and associate it with the string
      let name = self.gen_id();
      let string = self.process_str_literal();
      let ty = Rc::new(Type::array_of(
        Type::new(TypeLiteral::TYPE_CHAR),
        string.len() as u32,
      ));
      self.store_global(&name, &ty, Some(string));
      AstNode::VarNode(VarNode {
        name,
        ty: RefCell::new(ty),
        scope: -1,
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
    // declspec = "char" | "int"
    if self.match_tok(TokenType::CHAR) {
      return Type::new(TypeLiteral::TYPE_CHAR);
    }
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
      let scope = self.store(&name, &ty);
      params.push(VarDeclNode {
        ty: RefCell::new(ty),
        name,
        value: None,
        scope,
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
    if self.match_tok(TokenType::SEMI_COLON) {
      self.error(Some(ViError::EP001.to_info()));
    }
    let mut decls = vec![];
    let mut i = 0;
    while !self.match_tok(TokenType::SEMI_COLON) {
      if i > 0 {
        self.consume(TokenType::COMMA);
      }
      let ((ty, _params), name) = self.declarator(&base_ty);
      let ty = RefCell::new(Rc::new(ty));
      // insert local
      let scope = self.store(&name, &ty.borrow());
      if !self.match_tok(TokenType::EQUAL) {
        decls.push(VarDeclNode {
          name,
          ty,
          value: None,
          scope,
        });
        continue;
      }
      let value = self.assign();
      decls.push(VarDeclNode {
        name,
        ty,
        value: Some(Box::new(value)),
        scope,
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
    self.enter_scope();
    while !self.match_tok(TokenType::RIGHT_CURLY) {
      if self.is_typename() {
        block.stmts.push(self.declaration());
      } else {
        block.stmts.push(self.stmt());
      }
    }
    self.leave_scope();
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

  fn global_var_decl(
    &mut self,
    base_ty: Type,
    ty: Type,
    name: String,
  ) -> AstNode {
    let mut vars = vec![];
    let ty = Rc::new(ty);
    self.store_global(&name, &ty, None);
    vars.push(VarDeclNode {
      name,
      ty: RefCell::new(ty),
      value: None,
      scope: -1,
    });
    while !self.match_tok(TokenType::SEMI_COLON) {
      self.consume(TokenType::COMMA);
      let ((ty, _), name) = self.declarator(&base_ty);
      let ty = Rc::new(ty);
      self.store_global(&name, &ty, None);
      vars.push(VarDeclNode {
        name,
        ty: RefCell::new(ty),
        value: None,
        scope: -1,
      });
    }
    AstNode::VarDeclListNode(VarDeclListNode { decls: vars })
  }

  fn function(&mut self) -> AstNode {
    // create new fn state
    self.enter_scope();
    let base_ty = self.declspec();
    let ((ty, params), name) = self.declarator(&base_ty);
    if ty.kind.get() != TypeLiteral::TYPE_FUNC {
      return self.global_var_decl(base_ty, ty, name);
    }
    self.consume(TokenType::LEFT_CURLY);
    let list = self.compound_stmt();
    // leave fn state
    self.leave_scope();
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
    // program = (function-definition | global-variable)*
    self.advance();
    let mut decls = VecDeque::new();
    while !self.match_tok(TokenType::EOF) {
      decls.push_back(self.function());
    }
    // hoist strings/static data
    for (ty, name, data) in self.globals.iter().rev() {
      if data.is_some() {
        decls.push_front(AstNode::VarDeclNode(VarDeclNode {
          name: name.clone(),
          ty: RefCell::new(ty.clone()),
          scope: -1,
          value: None,
        }));
      }
    }
    AstNode::ProgramNode(ProgramNode {
      decls,
      globals: std::mem::take(&mut self.globals),
    })
  }
}
