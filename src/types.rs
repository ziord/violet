use crate::ast::{AstNode, BlockStmtNode};
use crate::lexer::OpType;
use crate::unbox;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

#[derive(Debug, Copy, Clone, PartialOrd, PartialEq)]
#[allow(non_camel_case_types)]
pub enum TypeLiteral {
  TYPE_NIL,
  TYPE_INT,
  TYPE_PTR,
  // TYPE_VOID,
  // TYPE_CHAR,
  // TYPE_BOOL,
  // TYPE_ARRAY,
  // TYPE_FUNCTION,
}

#[derive(Debug, Clone)]
pub struct TParam {
  name: String,
  type_: Type,
}

#[derive(Debug, Clone)]
pub struct Type {
  pub(crate) kind: Cell<TypeLiteral>,
  pub(crate) subtype: RefCell<Option<RefCell<Rc<Type>>>>,
  pub(crate) params: Option<RefCell<Vec<TParam>>>,
}

#[derive(Debug, Clone)]
pub struct TypeStack {
  pub(crate) stack: VecDeque<RefCell<HashMap<String, Type>>>,
}

#[derive(Debug)]
pub struct TypeCheck<'a> {
  pub(crate) at_error: bool,
  pub(crate) error_msg: Option<&'a str>,
}

impl Type {
  pub fn new(kind: TypeLiteral) -> Self {
    Self {
      kind: Cell::new(kind),
      subtype: RefCell::new(None),
      params: None,
    }
  }

  pub fn equals(&self, other: &Self) -> bool {
    if self.kind != other.kind {
      return false;
    }
    if self.subtype.borrow().is_some() != other.subtype.borrow().is_some() {
      return false;
    }
    if self.subtype.borrow().is_some() {
      let sub_t1 = &self.subtype.borrow().clone().unwrap();
      let sub_t2 = other.subtype.borrow().clone().unwrap();
      if !sub_t1.borrow().equals(&*sub_t2.borrow()) {
        return false;
      }
    }
    if self.params.is_some() != other.params.is_some() {
      return false;
    }
    if self.params.is_some() {
      let sub_params_1 = &self.params.clone().unwrap();
      let sub_params_2 = other.params.clone().unwrap();
      if sub_params_1.borrow().len() != sub_params_2.borrow().len() {
        return false;
      }
      let sub_params_2 = sub_params_2.borrow();
      let mut sub_params_2_iter = sub_params_2.iter();
      for param in sub_params_1.borrow().iter() {
        if let Some(p) = sub_params_2_iter.next() {
          if param.name != p.name || !param.type_.equals(&p.type_) {
            return false;
          }
        } else {
          return false; // unreachable
        }
      }
    }
    return true;
  }
}

impl TypeStack {
  pub fn new() -> Self {
    Self {
      stack: VecDeque::new(),
    }
  }

  pub fn push_stack(&mut self) {
    self.stack.push_front(RefCell::new(HashMap::new()));
  }

  pub fn pop_stack(&mut self) {
    self.stack.pop_front();
  }

  pub fn insert_type(&mut self, name: String, ty: Type) {
    if self.stack.is_empty() {
      self.stack.push_front(RefCell::new(HashMap::new()));
    }
    let t = self.stack.front().unwrap();
    t.borrow_mut().insert(name, ty);
  }

  pub fn lookup(&self, name: &str) -> Option<Type> {
    for rc_tab in &self.stack {
      if let Some(ty) = rc_tab.borrow().get(name) {
        return Some(ty.clone());
      }
    }
    None
  }
}

pub struct TypeProp {}

impl TypeProp {
  pub fn new() -> Self {
    Self {}
  }

  fn p_num(&mut self, node: &AstNode) -> Rc<Type> {
    unbox!(NumberNode, node).ty.borrow().clone()
  }

  fn p_var(&mut self, node: &AstNode) -> Rc<Type> {
    unbox!(VarNode, node).ty.borrow().clone()
  }

  fn p_unary(&mut self, node: &AstNode) -> Rc<Type> {
    let node = unbox!(UnaryNode, node);
    // "cache"
    if node.ty.borrow().kind.get() != TypeLiteral::TYPE_NIL {
      return node.ty.borrow().clone();
    }
    // propagate
    match node.op {
      OpType::PLUS | OpType::MINUS => {
        let ty = self.p_(&*node.node);
        // let node_ty = node.ty.borrow_mut();
        node.ty.replace(ty);
        node.ty.borrow().clone()
      }
      OpType::ADDR => {
        let ty = self.p_(&*node.node);
        let node_ty = node.ty.borrow_mut();
        if node_ty.subtype.borrow().is_none() {
          node_ty.subtype.borrow_mut().replace(RefCell::new(ty));
        } else {
          // node_ty.subtype.borrow().clone().unwrap().replace(ty);
          node_ty.subtype.replace(Some(RefCell::new(ty)));
        }
        node_ty.kind.set(TypeLiteral::TYPE_PTR);
        node_ty.clone()
      }
      OpType::DEREF => {
        let ty = self.p_(&node.node);
        let node_ty = node.ty.borrow();
        if ty.kind.get() == TypeLiteral::TYPE_PTR {
          node_ty
            .kind
            .set(ty.subtype.borrow().clone().unwrap().borrow().kind.get());
        } else {
          node_ty.kind.set(TypeLiteral::TYPE_INT); // todo: other literal types
        }
        node_ty.clone()
      }
      _ => panic!("unknown unary operator '{:?}'", node.op),
    }
  }

  fn p_binary(&mut self, node: &AstNode) -> Rc<Type> {
    let node = unbox!(BinaryNode, node);
    self.p_(&*node.left_node);
    self.p_(&node.right_node)
  }

  fn p_block(&mut self, node: &BlockStmtNode) -> Rc<Type> {
    for n in &node.stmts {
      self.p_(n);
    }
    Rc::new(Type::new(TypeLiteral::TYPE_NIL))
  }

  fn p_function(&mut self, node: &AstNode) -> Rc<Type> {
    let node = unbox!(FunctionNode, node);
    self.p_block(&node.body)
  }

  fn p_assign(&mut self, node: &AstNode) -> Rc<Type> {
    let node = unbox!(AssignNode, node);
    self.p_(&*node.left_node);
    self.p_(&node.right_node)
  }

  fn p_if_else(&mut self, node: &AstNode) -> Rc<Type> {
    let node = unbox!(IfElseNode, node);
    self.p_(&node.condition);
    self.p_(&node.if_block);
    self.p_(&node.else_block)
  }

  fn p_for_loop(&mut self, node: &AstNode) -> Rc<Type> {
    let node = unbox!(ForLoopNode, node);
    self.p_(&node.init);
    self.p_(&node.condition);
    self.p_(&node.incr);
    self.p_(&node.body)
  }

  fn p_while_loop(&mut self, node: &AstNode) -> Rc<Type> {
    let node = unbox!(WhileLoopNode, node);
    self.p_(&node.condition);
    self.p_(&node.body)
  }

  fn p_return(&mut self, node: &AstNode) -> Rc<Type> {
    self.p_(&unbox!(ReturnNode, node).expr)
  }

  fn p_expr_stmt(&mut self, node: &AstNode) -> Rc<Type> {
    self.p_(&unbox!(ExprStmtNode, node).node)
  }

  fn p_(&mut self, node: &AstNode) -> Rc<Type> {
    match node {
      AstNode::NumberNode(_) => self.p_num(node),
      AstNode::BinaryNode(_) => self.p_binary(node),
      AstNode::UnaryNode(_) => self.p_unary(node),
      AstNode::ExprStmtNode(_) => self.p_expr_stmt(node),
      AstNode::FunctionNode(_) => self.p_function(node),
      AstNode::AssignNode(_) => self.p_assign(node),
      AstNode::VarNode(_) => self.p_var(node),
      AstNode::ReturnNode(_) => self.p_return(node),
      AstNode::BlockStmtNode(n) => self.p_block(n),
      AstNode::IfElseNode(_) => self.p_if_else(node),
      AstNode::ForLoopNode(_) => self.p_for_loop(node),
      AstNode::WhileLoopNode(_) => self.p_while_loop(node),
    }
  }

  pub fn propagate_types(&mut self, root: &AstNode) {
    self.p_(root);
  }
}

impl<'a> TypeCheck<'a> {
  pub fn new() -> Self {
    Self {
      at_error: false,
      error_msg: None,
    }
  }

  fn tc_num(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    Ok(unbox!(NumberNode, node).ty.borrow().clone())
  }

  fn tc_var(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    Ok(unbox!(VarNode, node).ty.borrow().clone())
  }

  fn tc_binary(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(BinaryNode, node);
    let left_ty = self.tc(&node.left_node);
    if left_ty.is_err() {
      return left_ty;
    }
    let right_ty = self.tc(&node.right_node);
    if right_ty.is_err() {
      return right_ty;
    }
    let left_ty = left_ty.unwrap();
    let right_ty = right_ty.unwrap();
    match node.op {
      OpType::PLUS | OpType::MINUS => {
        if left_ty.kind.get() == TypeLiteral::TYPE_INT {
          // int, int
          if right_ty.kind.get() == TypeLiteral::TYPE_INT {
            return Ok(left_ty);
          }
          // int, ptr
          else if right_ty.kind.get() == TypeLiteral::TYPE_PTR {
            if node.op != OpType::MINUS { // int - ptr -> err
              return Ok(right_ty);
            }
          }
        } else if left_ty.kind.get() == TypeLiteral::TYPE_PTR {
          // ptr, int
          if right_ty.kind.get() == TypeLiteral::TYPE_INT {
            return Ok(left_ty);
          }
          // ptr, ptr
          else if right_ty.kind.get() == TypeLiteral::TYPE_PTR {
            return Ok(Rc::new(Type::new(TypeLiteral::TYPE_INT)));
          }
        }
      }
      OpType::DIV => {
        // int, int
        if left_ty.kind == right_ty.kind
          && left_ty.kind.get() == TypeLiteral::TYPE_INT
        {
          return Ok(left_ty);
        }
      }
      OpType::MUL => {
        // int, int
        if left_ty.kind == right_ty.kind
          && left_ty.kind.get() == TypeLiteral::TYPE_INT
        {
          return Ok(left_ty);
        }
      }
      OpType::LEQ
      | OpType::GEQ
      | OpType::LT
      | OpType::GT
      | OpType::EQQ
      | OpType::NEQ => {
        if left_ty.equals(&right_ty) {
          return Ok(left_ty);
        }
      }
      _ => unreachable!(),
    }
    // todo: better error reporting
    eprintln!("Type mismatch - for binary operation: {:#?}", node);
    Err("Type mismatch")
  }

  fn tc_unary(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(UnaryNode, node);
    let ty = self.tc(&node.node);
    if ty.is_err() {
      return ty;
    }
    let ty = ty.unwrap();
    let node_ty = node.ty.borrow().clone();
    match node.op {
      OpType::PLUS | OpType::MINUS => {
        if ty.kind.get() == TypeLiteral::TYPE_INT {
          return Ok(node_ty);
        }
      }
      OpType::ADDR => {
        if ty.kind.get() == TypeLiteral::TYPE_INT {
          return Ok(node_ty);
        }
      }
      OpType::DEREF => {
        if ty.kind.get() == TypeLiteral::TYPE_PTR {
          return Ok(node_ty);
        }
      }
      _ => unreachable!(),
    }
    // todo: better error reporting
    eprintln!("Type mismatch - for unary operation: {:#?}", node);
    Err("Type mismatch")
  }

  fn tc_assign(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(AssignNode, node);
    let left_ty = self.tc(&node.left_node);
    if left_ty.is_err() {
      return left_ty;
    }
    let right_ty = self.tc(&node.right_node);
    if right_ty.is_err() {
      return right_ty;
    }
    let left_ty = left_ty.unwrap();
    if left_ty.equals(&right_ty.unwrap()) {
      return Ok(left_ty);
    }
    // todo: better error reporting
    eprintln!("Type mismatch - for assignment operation: {:?}", node);
    Err("Invalid assignment target")
  }

  fn tc_return(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    // todo: use function signature
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    self.tc(&unbox!(ReturnNode, node).expr)
  }

  fn tc_function(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(FunctionNode, node);
    self.tc_block(&node.body)
  }

  fn tc_block(
    &mut self,
    node: &BlockStmtNode,
  ) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let mut ty;
    for n in &node.stmts {
      ty = self.tc(n);
      if ty.is_err() {
        return ty;
      }
    }
    Ok(Rc::new(Type::new(TypeLiteral::TYPE_NIL)))
  }

  fn tc_if_else(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(IfElseNode, node);
    let mut ty = self.tc(&node.condition);
    if ty.is_err() {
      return ty;
    }
    ty = self.tc(&node.if_block);
    if ty.is_err() {
      return ty;
    }
    self.tc(&node.else_block)
  }

  fn tc_for_loop(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(ForLoopNode, node);
    let mut ty = self.tc(&node.init);
    if ty.is_err() {
      return ty;
    }
    ty = self.tc(&node.condition);
    if ty.is_err() {
      return ty;
    }
    ty = self.tc(&node.incr);
    if ty.is_err() {
      return ty;
    }
    self.tc(&node.body)
  }

  fn tc_while_loop(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(WhileLoopNode, node);
    let mut ty = self.tc(&node.condition);
    if ty.is_err() {
      return ty;
    }
    self.tc(&node.body)
  }

  fn tc_expr_stmt(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let ty = self.tc(&unbox!(ExprStmtNode, node).node);
    if ty.is_err() {
      return ty;
    }
    Ok(Rc::new(Type::new(TypeLiteral::TYPE_NIL)))
  }

  pub(crate) fn tc(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    match node {
      AstNode::NumberNode(_) => self.tc_num(node),
      AstNode::BinaryNode(_) => self.tc_binary(node),
      AstNode::UnaryNode(_) => self.tc_unary(node),
      AstNode::VarNode(_) => self.tc_var(node),
      AstNode::AssignNode(_) => self.tc_assign(node),
      AstNode::ReturnNode(_) => self.tc_return(node),
      AstNode::ExprStmtNode(_) => self.tc_expr_stmt(node),
      AstNode::FunctionNode(_) => self.tc_function(node),
      AstNode::BlockStmtNode(nd) => self.tc_block(nd),
      AstNode::IfElseNode(_) => self.tc_if_else(node),
      AstNode::ForLoopNode(_) => self.tc_for_loop(node),
      AstNode::WhileLoopNode(_) => self.tc_while_loop(node),
    }
  }

  pub fn typecheck(&mut self, node: &AstNode) -> Result<(), &'a str> {
    let ty = self.tc(node);
    if ty.is_ok() {
      return Ok(());
    }
    Err(self.error_msg.unwrap())
  }
}
