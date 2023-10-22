use crate::ast::*;
use crate::diagnostics::Diagnostic;
use crate::errors::{ErrorInfo, ViError};
use crate::lexer::{LexState, Lexer, OpType, Token, TokenType};
use crate::propagate::propagate_types;
use crate::types::{TMember, TParam, Type, TypeLiteral};
use crate::unbox;
use std::borrow::BorrowMut;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, VecDeque};
use std::process::exit;
use std::rc::Rc;

#[derive(Debug, Clone)]
struct VarProp {
  ty: Rc<Type>,
  is_typedef: bool,
}

impl VarProp {
  fn new(ty: &Rc<Type>, is_typedef: bool) -> Self {
    Self {
      ty: ty.clone(),
      is_typedef,
    }
  }
}

#[derive(Debug)]
struct Scope<K, V> {
  level: Cell<i32>,
  vars: RefCell<BTreeMap<K, VarProp>>,
  tags: RefCell<BTreeMap<K, V>>,
  enclosing: Option<RefCell<Rc<Scope<K, V>>>>,
}

#[derive(Debug)]
pub(crate) struct Parser<'a, 'b, 'c> {
  lexer: Lexer<'a, 'b>,
  current_token: Token<'a>,
  previous_token: Token<'a>,
  // name, type, scope
  locals: Vec<(String, Rc<Type>, i32)>,
  // type, name, init_data (string literal)
  globals: Vec<(Rc<Type>, String, Option<AstNode>)>,
  current_scope: Rc<Scope<String, Rc<Type>>>,
  scope_count: i32,
  diag: &'c mut Diagnostic,
}

impl<K, V> Scope<K, V> {
  fn new() -> Self {
    Self {
      level: Cell::new(0),
      vars: RefCell::new(BTreeMap::new()),
      tags: RefCell::new(BTreeMap::new()),
      enclosing: (None),
    }
  }
}

impl<'a, 'b, 'c> Parser<'a, 'b, 'c> {
  pub fn new(src: &'a str, diag: &'c mut Diagnostic) -> Self {
    Self {
      lexer: Lexer::new(src),
      current_token: Token::default(),
      previous_token: Token::default(),
      locals: Vec::new(),
      current_scope: Rc::new(Scope::new()),
      scope_count: 1,
      globals: vec![],
      diag,
    }
  }

  fn error(&self, code: Option<ErrorInfo<'a>>) -> ! {
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
    self.current_scope.level.set(level + 1 + self.scope_count);
    self.scope_count += 1;
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

  fn scope_var(&mut self, name: &str, prop: VarProp) {
    self
      .current_scope
      .vars
      .borrow_mut()
      .insert(name.into(), prop);
  }

  fn scope_tag(&mut self, name: &str, ty: &Rc<Type>) {
    self
      .current_scope
      .tags
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

  fn store(&mut self, name: &String, prop: VarProp) -> i32 {
    let scope = self.current_scope.level.get();
    self.locals.push((name.clone(), prop.ty.clone(), scope));
    self.scope_var(name, prop);
    scope
  }

  fn store_global(
    &mut self,
    name: &String,
    prop: VarProp,
    data: Option<AstNode>,
  ) -> i32 {
    self.globals.push((prop.ty.clone(), name.clone(), data));
    self.scope_var(name, prop);
    self.current_scope.level.get()
  }

  fn find_tag(&self, name: &String) -> (Rc<Type>, i32) {
    let mut scope = self.current_scope.clone();
    loop {
      if let Some(v) = scope.tags.borrow().get(name) {
        return (v.clone(), scope.level.get());
      }
      if scope.enclosing.is_none() {
        break;
      }
      let tmp = scope.enclosing.as_ref().unwrap().borrow().clone();
      scope = tmp;
    }
    // todo: need to handle this
    panic!(
      "struct/union tag '{}' is not defined in the current scope",
      name
    )
  }

  fn _find_var(&self, name: &str) -> Option<(VarProp, i32)> {
    let mut scope = self.current_scope.clone();
    loop {
      if let Some(v) = scope.vars.borrow().get(name) {
        return Some((v.clone(), scope.level.get()));
      }
      if scope.enclosing.is_none() {
        break;
      }
      let tmp = scope.enclosing.as_ref().unwrap().borrow().clone();
      scope = tmp;
    }
    None
  }

  fn find_var(&self, name: &str) -> (VarProp, i32) {
    if let Some(v) = self._find_var(name) {
      return v;
    }
    // todo: need to handle this
    panic!("variable '{}' is not defined in the current scope", name)
  }

  fn find_typedef(&self, name: &str) -> Option<Rc<Type>> {
    if let Some(ret) = self._find_var(name) {
      if ret.0.is_typedef {
        return Some(ret.0.ty.clone());
      }
    }
    None
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
      TokenType::INT
      | TokenType::SHORT
      | TokenType::LONG
      | TokenType::CHAR
      | TokenType::STRUCT
      | TokenType::VOID
      | TokenType::TYPEDEF
      | TokenType::UNION => true,
      TokenType::IDENT => {
        // for typedef'ed names
        self.find_typedef(self.current_token.value()).is_some()
      }
      _ => false,
    }
  }

  fn is_typedef(&self) -> bool {
    self.current_token.equal(TokenType::TYPEDEF)
  }

  fn resume(&mut self, snapshot: (LexState, Token<'a>)) {
    // snapshot -> (state, last_token)
    self.lexer.rewind(snapshot.0);
    self.current_token = snapshot.1;
  }

  fn pause(&mut self) -> (LexState, Token<'a>) {
    (self.lexer.snapshot(), self.current_token)
  }

  fn ty(&self) -> RefCell<Rc<Type>> {
    RefCell::new(Type::rc_default())
  }

  fn num(&mut self) -> AstNode {
    let line = self.current_token.line;
    self.consume(TokenType::NUM);
    AstNode::NumberNode(NumberNode {
      value: self.previous_token.to_int(),
      ty: RefCell::new(Rc::new(Type::new(TypeLiteral::TYPE_INT))),
      line,
    })
  }

  fn variable(&mut self) -> AstNode {
    let line = self.previous_token.line;
    let name: String = self.previous_token.value().into();
    let (prop, scope) = self.find_var(&name);
    let ty = RefCell::new(prop.ty);
    AstNode::VarNode(VarNode {
      name,
      ty,
      scope,
      line,
    })
  }

  fn call(&mut self, name: &str) -> AstNode {
    let line = self.previous_token.line;
    let name: String = name.into();
    // args
    let mut args: Vec<AstNode> = vec![];
    if !self.match_tok(TokenType::RIGHT_BRACKET) {
      let mut i = 0;
      while !self.match_tok(TokenType::RIGHT_BRACKET) {
        if i > 0 {
          self.consume(TokenType::COMMA);
        }
        i += 1;
        args.push(self.assign());
      }
    }
    AstNode::FnCallNode(FnCallNode {
      name,
      args,
      line,
      ty: self.ty(), // todo: change somewhere
    })
  }

  fn primary(&mut self) -> AstNode {
    // primary = "({" stmt+ "})"
    //          | "(" expr ")"
    //          | "sizeof" unary
    //          | "sizeof" "(" type-name ")"
    //          | ident func-args?
    //          | num
    //          | str
    if self.match_tok(TokenType::LEFT_BRACKET) {
      if self.match_tok(TokenType::LEFT_CURLY) {
        let line = self.previous_token.line;
        if self.current_token.equal(TokenType::RIGHT_CURLY) {
          self.error(Some(ViError::EP004.to_info()));
        }
        let block = self.compound_stmt();
        let stmts = unbox!(BlockStmtNode, block).stmts;
        let node = AstNode::StmtExprNode(StmtExprNode {
          stmts,
          line,
          ty: self.ty(),
        });
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
      // handle "sizeof" "(" type-name ")"
      if self.current_token.equal(TokenType::LEFT_BRACKET) {
        let snapshot: (LexState, Token) = self.pause();
        self.advance();
        if self.is_typename() {
          let line = self.current_token.line;
          let ty = self.typename();
          self.consume(TokenType::RIGHT_BRACKET);
          return AstNode::NumberNode(NumberNode {
            value: ty.size as i64,
            ty: RefCell::new(Rc::new(ty)),
            line,
          });
        }
        // rewind back to "(" and fallback to unary()
        self.resume(snapshot);
      }
      // handle "sizeof" unary
      let line = self.previous_token.line;
      AstNode::SizeofNode(SizeofNode {
        size: Cell::new(0),
        node: Box::new(self.unary()),
        ty: self.ty(),
        line,
      })
    } else if self.match_tok(TokenType::STRING) {
      // create a new global variable, and associate it with the string
      let line = self.previous_token.line;
      let name = self.gen_id();
      let string = self.process_str_literal();
      let ty = Rc::new(Type::array_of(
        Type::new(TypeLiteral::TYPE_CHAR),
        string.len() as u32,
      ));
      // we can't use the scope returned here, since scope level may not be 0.
      // storing into global to make the string static.
      self.store_global(
        &name,
        VarProp::new(&ty, false),
        Some(AstNode::StringNode(StringNode {
          value: string,
          line,
          ty: RefCell::new(ty.clone()),
        })),
      );
      AstNode::VarNode(VarNode {
        name,
        ty: RefCell::new(ty),
        scope: 0,
        line,
      })
    } else {
      self.num()
    }
  }

  fn member_offset(&self, name: &str, ty: &Rc<Type>) -> TMember {
    for mem in ty.members.as_ref().unwrap().borrow().iter() {
      if mem.name == name {
        return mem.clone();
      }
    }
    self.error(Some(ViError::EP006.to_info()));
  }

  fn member_access(
    &mut self,
    mut node: AstNode,
    name: &str,
    line: i32,
  ) -> AstNode {
    propagate_types(&mut node, &mut self.diag);
    let ty = node.get_type();
    if ty.kind.get() != TypeLiteral::TYPE_STRUCT
      && ty.kind.get() != TypeLiteral::TYPE_UNION
    {
      self.error(Some(ViError::EP005.to_info()));
    }
    let member = self.member_offset(name, &ty);
    let node_ty = member.ty.clone();
    AstNode::UnaryNode(UnaryNode {
      node: Box::new(node),
      op: OpType::DOT,
      line,
      member_t: Some(member),
      ty: RefCell::new(node_ty),
    })
  }

  fn postfix(&mut self) -> AstNode {
    // postfix = primary ("[" expr "]" | "." ident | "->" ident)*
    let mut node = self.primary();
    loop {
      if self.match_tok(TokenType::LEFT_SQR_BRACKET) {
        let line = self.previous_token.line;
        // x[y] is a sugar for *(x+y)
        let index = self.expr();
        self.consume(TokenType::RIGHT_SQR_BRACKET);
        let tmp = UnaryNode {
          op: OpType::DEREF,
          member_t: None,
          node: Box::new(AstNode::BinaryNode(BinaryNode {
            left: Box::new(node),
            right: Box::new(index),
            op: OpType::PLUS,
            ty: self.ty(),
          })),
          ty: self.ty(),
          line,
        };
        node = AstNode::UnaryNode(tmp);
      } else if self.match_tok(TokenType::DOT) {
        // expr.id (struct member access)
        let line = self.previous_token.line;
        self.consume(TokenType::IDENT);
        let name = self.previous_token.value();
        node = self.member_access(node, name, line);
      } else if self.match_tok(TokenType::ARROW) {
        // expr->y is short for (*expr).y
        // *expr
        let line = self.previous_token.line;
        self.consume(TokenType::IDENT);
        let name = self.previous_token.value();
        node = AstNode::UnaryNode(UnaryNode {
          node: Box::new(node),
          op: OpType::DEREF,
          line: self.previous_token.line,
          member_t: None,
          ty: self.ty(),
        });
        // (*expr).y
        node = self.member_access(node, name, line);
      } else {
        break;
      }
    }
    node
  }

  fn unary(&mut self) -> AstNode {
    // unary = ("+" | "-" | "*" | "&") cast
    //       | postfix
    match self.current_token.t_type() {
      TokenType::PLUS
      | TokenType::MINUS
      | TokenType::STAR
      | TokenType::AMP => {
        self.advance();
        let line = self.previous_token.line;
        let mut op = self.previous_token.t_type().to_optype();
        if op == OpType::MUL {
          op = OpType::DEREF;
        }
        let node = self.cast();
        AstNode::UnaryNode(UnaryNode {
          ty: self.ty(),
          node: Box::new(node),
          member_t: None,
          line,
          op,
        })
      }
      _ => self.postfix(),
    }
  }

  fn cast(&mut self) -> AstNode {
    // cast = "(" type-name ")" cast | unary
    if self.current_token.equal(TokenType::LEFT_BRACKET) {
      let snapshot: (LexState, Token) = self.pause();
      self.advance();
      // current token a typename?
      if self.is_typename() {
        let line = self.previous_token.line;
        let cast_ty = self.typename();
        self.consume(TokenType::RIGHT_BRACKET);
        let node = self.cast();
        return AstNode::CastNode(CastNode {
          cast_ty: RefCell::new(Rc::new(cast_ty)),
          line,
          node: Box::new(node),
        });
      } else {
        // backtrack to "(" token
        self.resume(snapshot);
      }
    }
    self.unary()
  }

  fn term(&mut self) -> AstNode {
    // term = cast ("*" primary | "/" cast)*
    let mut left = self.cast();
    while self.match_tok(TokenType::STAR)
      || self.match_tok(TokenType::FWD_SLASH)
    {
      let op = self.previous_token.t_type().to_optype();
      let right = self.cast();
      left = AstNode::BinaryNode(BinaryNode {
        left: Box::new(left),
        right: Box::new(right),
        ty: self.ty(),
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
        left: Box::new(left),
        right: Box::new(right),
        ty: self.ty(),
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
            left: Box::new(left),
            right: Box::new(right),
            ty: self.ty(),
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
        left: Box::new(left),
        right: Box::new(right),
        ty: self.ty(),
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
        left: Box::new(left),
        right: Box::new(right),
        ty: self.ty(),
        op,
      });
    }
    left
  }

  fn expr(&mut self) -> AstNode {
    // expr = assign ("," expr)?
    let node = self.assign();
    if self.match_tok(TokenType::COMMA) {
      return AstNode::BinaryNode(BinaryNode {
        left: Box::new(node),
        right: Box::new(self.expr()),
        ty: self.ty(),
        op: OpType::COMMA,
      });
    }
    node
  }

  fn expr_stmt(&mut self) -> AstNode {
    // expr-stmt = expr? ";"
    if self.match_tok(TokenType::SEMI_COLON) {
      return self.empty_stmt();
    }
    let line = self.current_token.line;
    let node = self.expr();
    self.consume(TokenType::SEMI_COLON);
    AstNode::ExprStmtNode(ExprStmtNode {
      node: Box::new(node),
      line,
    })
  }

  fn create_member(&mut self, base_ty: &Type) -> TMember {
    let ((ty, _params), name) = self.declarator(&base_ty);
    TMember {
      name,
      ty: Rc::new(ty),
      offset: 0,
    }
  }

  fn align_struct(
    &mut self,
    struct_ty: &mut Type,
    members: &mut Vec<TMember>,
  ) -> u32 {
    let mut offset = 0;
    for member in members {
      offset = Type::align_to(offset, member.ty.align);
      member.offset = offset;
      offset += member.ty.size;
      if member.ty.align > struct_ty.align {
        struct_ty.align = member.ty.align;
      }
    }
    offset
  }

  fn align_union(&mut self, union_ty: &mut Type, members: &Vec<TMember>) {
    // no need for offset computation for union
    for member in members {
      if member.ty.size > union_ty.size {
        union_ty.size = member.ty.size;
      }
      if member.ty.align > union_ty.align {
        union_ty.align = member.ty.align;
      }
    }
  }

  fn struct_union_decl(&mut self, is_struct: bool) -> Type {
    // struct-union-decl = ident? "{" (declspec declarator (","  declarator)* ";")* "}"
    let mut tag = String::new();
    if self.match_tok(TokenType::IDENT) {
      tag = self.previous_token.value().into();
      if !self.current_token.equal(TokenType::LEFT_CURLY) {
        let (ty, _scope) = self.find_tag(&tag);
        return ty.into();
      }
    }
    self.consume(TokenType::LEFT_CURLY);
    let mut members = vec![];
    let mut su_ty = Type::new(TypeLiteral::TYPE_STRUCT);
    while !self.match_tok(TokenType::RIGHT_CURLY) {
      let base_ty = self.declspec(false);
      members.push(self.create_member(&base_ty));
      while !self.match_tok(TokenType::SEMI_COLON) {
        self.consume(TokenType::COMMA);
        members.push(self.create_member(&base_ty));
      }
    }
    if is_struct {
      let offset = self.align_struct(&mut su_ty, &mut members);
      su_ty.members.replace(RefCell::new(members));
      su_ty.size = Type::align_to(offset, su_ty.align);
    } else {
      self.align_union(&mut su_ty, &mut members);
      su_ty.members.replace(RefCell::new(members));
      su_ty.size = Type::align_to(su_ty.size, su_ty.align);
    }
    if !tag.is_empty() {
      // todo: cloning the type here is pretty expensive.
      self.scope_tag(&tag, &Rc::new(su_ty.clone()));
    }
    su_ty
  }

  fn struct_decl(&mut self) -> Type {
    // struct-decl = struct-union-decl
    self.struct_union_decl(true)
  }

  fn union_decl(&mut self) -> Type {
    // union-decl = struct-union-decl
    self.struct_union_decl(false)
  }

  fn declspec(&mut self, allow_typedef: bool) -> Type {
    // declspec = ("char" | "int" | "short" | "long"
    //          | "void" | struct-decl | union-decl
    //          | "typedef")+
    #[allow(non_snake_case)]
    let (VOID, CHAR, SHORT, INT, LONG, OTHER) = (1, 4, 16, 64, 256, 1024);
    let mut count = 0;
    // typedef unknown -> unknown defaults to int type
    let mut ty = Type::new(TypeLiteral::TYPE_INT);
    while self.is_typename() {
      if self.is_typedef() {
        if allow_typedef {
          self.advance();
          continue;
        } else {
          self.error(Some(ViError::EP009.to_info()));
        }
      }
      // check if the current token is a user defined type (i.e. typedef'ed)
      if self.current_token.equal(TokenType::IDENT) {
        if let Some(tmp_ty) = self.find_typedef(self.current_token.value())
        {
          self.advance(); // skip the token (which is an identifier)
          ty = tmp_ty.into();
          break;
        }
      }
      if self.current_token.equal(TokenType::STRUCT)
        || self.current_token.equal(TokenType::UNION)
      {
        if self.match_tok(TokenType::STRUCT) {
          ty = self.struct_decl();
        } else {
          self.advance(); // skip token UNION
          ty = self.union_decl();
        }
        count += OTHER;
        continue;
      }
      if self.match_tok(TokenType::VOID) {
        count += VOID;
      } else if self.match_tok(TokenType::CHAR) {
        count += CHAR;
      } else if self.match_tok(TokenType::SHORT) {
        count += SHORT;
      } else if self.match_tok(TokenType::INT) {
        count += INT;
      } else if self.match_tok(TokenType::LONG) {
        count += LONG;
      } else {
        unreachable!()
      }
      // validate and assign type
      if count == VOID {
        ty = Type::new(TypeLiteral::TYPE_VOID);
      } else if count == CHAR {
        ty = Type::new(TypeLiteral::TYPE_CHAR);
      } else if count == SHORT || count == SHORT + INT {
        ty = Type::new(TypeLiteral::TYPE_SHORT);
      } else if count == INT {
        ty = Type::new(TypeLiteral::TYPE_INT);
      } else if count == LONG
        || count == LONG + INT
        || count == LONG + LONG
        || count == LONG + LONG + INT
      {
        ty = Type::new(TypeLiteral::TYPE_LONG)
      } else {
        self.error(Some(ViError::EP008.to_info()));
      }
    }
    return ty;
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
    if !params.is_empty() {
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
      i += 1;
      let line = self.current_token.line;
      let base_ty = self.declspec(false);
      let ((ty, _), name) = self.declarator(&base_ty);
      let ty = Rc::new(ty);
      params.push(VarDeclNode {
        ty: RefCell::new(ty),
        name,
        value: None,
        scope: 0,
        line,
      });
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

  fn typename(&mut self) -> Type {
    // type-name = declspec abstract-declarator
    let ty = self.declspec(false);
    self.abstract_declarator(ty).0
  }

  fn abstract_declarator(
    &mut self,
    mut ty: Type,
  ) -> (Type, Option<Vec<VarDeclNode>>) {
    // abstract-declarator = "*"* ("(" abstract-declarator ")")? type-suffix
    while self.match_tok(TokenType::STAR) {
      ty = Type::pointer_to(ty);
    }
    while self.match_tok(TokenType::LEFT_BRACKET) {
      let snapshot_1: (LexState, Token) = self.pause();
      self.abstract_declarator(Type::default());
      self.consume(TokenType::RIGHT_BRACKET);
      let (base_ty, _) = self.type_suffix(&ty);
      let snapshot_2: (LexState, Token) = self.pause();
      self.resume(snapshot_1);
      let (ty, p) = self.abstract_declarator(base_ty);
      self.resume(snapshot_2);
      return (ty, p);
    }
    self.type_suffix(&ty)
  }

  fn declarator(
    &mut self,
    ty: &Type,
  ) -> ((Type, Option<Vec<VarDeclNode>>), String) {
    // declarator = "*"* ("(" ident ")" | "(" declarator ")" | ident) type-suffix
    let mut ty = ty.clone();
    while self.match_tok(TokenType::STAR) {
      ty = Type::pointer_to(ty);
    }
    if self.match_tok(TokenType::LEFT_BRACKET) {
      // we need to skip everything within "(" and ")" to parse the actual type,
      // afterwards, use the actual type as base for (parsing) everything within "(" and ")"
      // this is achieved using self.pause() and self.resume().
      let (start_state, start_tok): (LexState, Token) = self.pause();
      self.declarator(&Type::default());
      self.consume(TokenType::RIGHT_BRACKET);
      let (base_ty, _) = self.type_suffix(&ty);
      let (end_state, end_tok): (LexState, Token) = self.pause();
      // reset to start_state and start token, and parse the inner type "("..")"
      self.resume((start_state, start_tok));
      let ((ty, _), name) = self.declarator(&base_ty);
      // reset to the actual end_state after parsing the inner type
      self.resume((end_state, end_tok));
      return ((ty, None), name);
    }
    self.consume(TokenType::IDENT);
    let name = self.previous_token.value().into();
    // = | ; -> var decl or ( -> func
    let suffixes = self.type_suffix(&ty);
    (suffixes, name)
  }

  fn declaration(&mut self) -> AstNode {
    // declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    let line = self.current_token.line;
    let base_ty = self.declspec(false);
    let mut decls = vec![];
    let mut i = 0;
    while !self.match_tok(TokenType::SEMI_COLON) {
      if i > 0 {
        self.consume(TokenType::COMMA);
      }
      i += 1;
      let line = self.current_token.line;
      let ((ty, _params), name) = self.declarator(&base_ty);
      if ty.kind_equal(TypeLiteral::TYPE_VOID) {
        self.error(Some(ViError::EP007.to_info()));
      }
      let ty = RefCell::new(Rc::new(ty));
      // insert local
      let scope = self.store(&name, VarProp::new(&ty.borrow(), false));
      if !self.match_tok(TokenType::EQUAL) {
        decls.push(VarDeclNode {
          name,
          ty,
          value: None,
          scope,
          line,
        });
        continue;
      }
      let value = self.assign();
      decls.push(VarDeclNode {
        name,
        ty,
        value: Some(Box::new(value)),
        scope,
        line,
      });
    }
    if decls.len() == 1 {
      return AstNode::VarDeclNode(decls.pop().unwrap());
    }
    AstNode::VarDeclListNode(VarDeclListNode { decls, line })
  }

  fn compound_stmt(&mut self) -> AstNode {
    // compound-stmt = (typedef | declaration | stmt)* "}"
    let mut block = BlockStmtNode {
      stmts: vec![],
      // line: self.current_token.line,
    };
    self.enter_scope();
    while !self.match_tok(TokenType::RIGHT_CURLY) {
      let node;
      if self.is_typename() {
        if self.is_typedef() {
          let base_ty = self.declspec(true);
          node = self.parse_typedef(base_ty);
        } else {
          node = self.declaration();
        }
      } else {
        node = self.stmt();
      }
      block.stmts.push(node);
    }
    self.leave_scope();
    AstNode::BlockStmtNode(block)
  }

  fn empty_stmt(&self) -> AstNode {
    AstNode::BlockStmtNode(BlockStmtNode {
      stmts: vec![],
      // line: self.current_token.line,
    })
  }

  fn empty_node(&self) -> AstNode {
    AstNode::EmptyNode(EmptyStmtNode {
      line: self.current_token.line,
    })
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
        let line = self.current_token.line;
        self.advance();
        self.consume(TokenType::LEFT_BRACKET);
        let condition = self.expr();
        self.consume(TokenType::RIGHT_BRACKET);
        let block = self.stmt();
        AstNode::WhileLoopNode(WhileLoopNode {
          condition: Box::new(condition),
          body: Box::new(block),
          line,
        })
      }
      TokenType::FOR => {
        let line = self.current_token.line;
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
          line,
        })
      }
      TokenType::IF => {
        let line = self.current_token.line;
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
          line,
        });
      }
      TokenType::RETURN => {
        let line = self.current_token.line;
        self.advance();
        let node: AstNode = self.expr();
        self.consume(TokenType::SEMI_COLON);
        return AstNode::ReturnNode(ReturnNode {
          expr: Box::new(node),
          ty: self.ty(),
          line,
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
    let scope = self.store_global(&name, VarProp::new(&ty, false), None);
    let line = self.previous_token.line;
    vars.push(VarDeclNode {
      name,
      ty: RefCell::new(ty),
      value: None,
      scope,
      line,
    });
    while !self.match_tok(TokenType::SEMI_COLON) {
      self.consume(TokenType::COMMA);
      let line = self.current_token.line;
      let ((ty, _), name) = self.declarator(&base_ty);
      let ty = Rc::new(ty);
      let scope = self.store_global(&name, VarProp::new(&ty, false), None);
      vars.push(VarDeclNode {
        name,
        ty: RefCell::new(ty),
        value: None,
        scope,
        line,
      });
    }
    AstNode::VarDeclListNode(VarDeclListNode { decls: vars, line })
  }

  fn parse_typedef(&mut self, base_ty: Type) -> AstNode {
    // typedef type alias ("," alias)* ";"
    //         ^^^^
    //        base_ty
    let mut i = 0;
    while !self.match_tok(TokenType::SEMI_COLON) {
      if i > 0 {
        self.consume(TokenType::COMMA);
      }
      i += 1;
      let ((ty, _), alias) = self.declarator(&base_ty);
      self.scope_var(
        &alias,
        VarProp {
          ty: Rc::new(ty),
          is_typedef: true,
        },
      );
    }
    self.empty_node()
  }

  fn function(
    &mut self,
    name: String,
    ty: Type,
    mut params: Option<Vec<VarDeclNode>>,
    line: i32,
  ) -> AstNode {
    // handle functions
    let ty = Rc::new(ty);
    // make function visible at the current scope
    self.scope_var(&name, VarProp::new(&ty, false));
    let list;
    let is_proto = self.match_tok(TokenType::SEMI_COLON);
    if is_proto {
      // function prototype
      list = self.empty_stmt();
    } else {
      // create new fn state
      self.enter_scope();
      // make parameters locally scoped to the function
      for param in params.as_mut().unwrap().iter_mut() {
        param.scope =
          self.store(&param.name, VarProp::new(&param.ty.borrow(), false));
      }
      self.consume(TokenType::LEFT_CURLY);
      list = self.compound_stmt();
      // leave fn state
      self.leave_scope();
    }
    if let AstNode::BlockStmtNode(block) = list {
      AstNode::FunctionNode(FunctionNode {
        name,
        params: params.unwrap_or(vec![]),
        stack_size: Cell::new(0),
        body: block,
        locals: std::mem::take(&mut self.locals),
        ty: RefCell::new(ty),
        is_proto,
        line,
      })
    } else {
      panic!("expected BlockStmtNode node")
    }
  }

  fn dispatch(&mut self) -> AstNode {
    // (typedef | function-definition | global-variable)*
    let line = self.current_token.line;
    let is_typedef = self.is_typedef();
    let base_ty = self.declspec(true);
    // handle typedef
    if is_typedef {
      return self.parse_typedef(base_ty);
    }
    // handle global variable declarations
    let ((ty, params), name) = self.declarator(&base_ty);
    if ty.kind.get() != TypeLiteral::TYPE_FUNC {
      return self.global_var_decl(base_ty, ty, name);
    }
    // handle functions
    self.function(name, ty, params, line)
  }

  pub fn parse(&mut self) -> AstNode {
    // program = dispatch..>
    self.advance();
    let mut decls = VecDeque::new();
    while !self.match_tok(TokenType::EOF) {
      // delegate..>
      decls.push_back(self.dispatch());
    }
    // hoist static/global data
    let globals = std::mem::take(&mut self.globals);
    for (ty, name, data) in globals.into_iter().rev() {
      // Only store nodes not already in global scope.
      // Usually, this could be a StringNode found inside an expression.
      if data.is_some() {
        decls.push_front(AstNode::VarDeclNode(VarDeclNode {
          name,
          ty: RefCell::new(ty),
          scope: 0, // global scope is 0
          value: Some(Box::new(data.unwrap())),
          line: 0, // use a virtual line
        }));
      }
    }
    AstNode::ProgramNode(ProgramNode { decls })
  }
}
