use crate::analyzer::{SymbolStack, SymbolTable};
use crate::ast::{AstNode, BlockStmtNode, VarDeclNode, VarNode};
use crate::lexer::OpType;
use crate::unbox;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

#[derive(Debug, Copy, Clone, PartialOrd, PartialEq)]
#[allow(non_camel_case_types)]
pub enum TypeLiteral {
  TYPE_NIL,
  TYPE_INT,
  TYPE_PTR,
  TYPE_FUNC,
  // TYPE_VOID,
  // TYPE_CHAR,
  // TYPE_BOOL,
  // TYPE_ARRAY,
}

#[derive(Debug, Clone)]
pub struct TParam {
  pub(crate) name: String,
  pub(crate) ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct Type {
  pub(crate) kind: Cell<TypeLiteral>,
  pub(crate) subtype: RefCell<Option<RefCell<Rc<Type>>>>,
  pub(crate) params: Option<RefCell<Vec<TParam>>>,
}

#[derive(Debug)]
pub struct TypeCheck<'a> {
  pub(crate) at_error: bool,
  pub(crate) error_msg: Option<&'a str>,
  pub(crate) sym_tab: SymbolTable,
  pub(crate) current_fn: String,
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
      let tmp = self.subtype.borrow();
      let sub_t1 = tmp.as_ref().unwrap();
      let tmp = other.subtype.borrow();
      let sub_t2 = tmp.as_ref().unwrap();
      if !sub_t1.borrow().equals(&*sub_t2.borrow()) {
        return false;
      }
    }
    if self.params.is_some() != other.params.is_some() {
      return false;
    }
    if self.params.is_some() {
      let sub_params_1 = self.params.as_ref().unwrap();
      let sub_params_2 = other.params.as_ref().unwrap();
      if sub_params_1.borrow().len() != sub_params_2.borrow().len() {
        return false;
      }
      let sub_params_2 = sub_params_2.borrow();
      let mut sub_params_2_iter = sub_params_2.iter();
      for param in sub_params_1.borrow().iter() {
        if let Some(p) = sub_params_2_iter.next() {
          if param.name != p.name || !param.ty.equals(&p.ty) {
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

impl<'a> TypeCheck<'a> {
  pub fn new(type_tabs: SymbolTable) -> Self {
    Self {
      at_error: false,
      error_msg: None,
      sym_tab: type_tabs,
      current_fn: String::new(),
    }
  }

  fn get_func_table(&self) -> &(Rc<Type>, SymbolStack<String, Rc<Type>>) {
    &(self
      .sym_tab
      .symbols()
      .get(&self.current_fn)
      .expect("Table not found"))
  }

  fn table(&self) -> &SymbolStack<String, Rc<Type>> {
    &self.get_func_table().1
  }

  fn tc_num(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    Ok(unbox!(NumberNode, node).ty.borrow().clone())
  }

  fn tc_var(&mut self, node: &VarNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let ty = self.table().lookup_symbol(&node.name);
    Ok(ty.unwrap())
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
    // propagate
    match node.op {
      OpType::PLUS | OpType::MINUS => {
        if ty.kind.get() == TypeLiteral::TYPE_INT {
          return Ok(ty);
        }
      }
      OpType::ADDR => {
        let node_ty = node.ty.borrow_mut().clone();
        node_ty.subtype.replace(Some(RefCell::new(ty)));
        node_ty.kind.set(TypeLiteral::TYPE_PTR);
        return Ok(node_ty);
      }
      OpType::DEREF => {
        if ty.kind.get() == TypeLiteral::TYPE_PTR {
          return Ok(ty.subtype.borrow_mut().clone().unwrap().into_inner());
        } else {
          eprintln!("Expected pointer type as subtype for dereference");
        }
      }
      _ => panic!("unknown unary operator '{:?}'", node.op),
    }
    // todo: better error reporting
    eprintln!("Type mismatch - for unary operation: {:#?}", node);
    self.error_msg = Some("Type mismatch");
    Err(self.error_msg.unwrap())
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
            if node.op != OpType::MINUS {
              // int - ptr -> err
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
    self.error_msg = Some("Type mismatch");
    Err(self.error_msg.unwrap())
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
    eprintln!("Type mismatch - for assignment operation: {:#?}", node);
    self.error_msg = Some("Assignment target type mismatch");
    Err(self.error_msg.unwrap())
  }

  fn tc_return(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let ret_ty = self.tc(&unbox!(ReturnNode, node).expr);
    let (func_ret_ty, _) =
      self.sym_tab.symbols().get(&self.current_fn).unwrap();
    if let Ok(ret_ty) = ret_ty {
      if func_ret_ty
        .subtype
        .borrow()
        .as_ref()
        .unwrap()
        .borrow()
        .equals(&ret_ty)
      {
        return Ok(ret_ty);
      } else {
        eprintln!("Type mismatch - return type does not match function definition: {:?}", node);
        self.error_msg = Some("Return type mismatch");
      }
    }
    Err(self.error_msg.unwrap())
  }

  fn tc_function(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let node = unbox!(FunctionNode, node);
    self.current_fn = node.name.clone();
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
    let ty = self.tc(&node.condition);
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

  fn tc_var_decl(
    &mut self,
    node: &VarDeclNode,
  ) -> Result<Rc<Type>, &'a str> {
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    let left_ty = node.ty.borrow();
    if let Some(value) = &node.value {
      let right_ty = self.tc(&*value);
      if right_ty.is_err() {
        return right_ty;
      }
      let ty = right_ty.as_ref().unwrap();
      if !left_ty.equals(ty) {
        // todo: better error handling
        eprintln!(
          "Type mismatch:\n{:#?} is not equal to {:#?}",
          left_ty, right_ty
        );
        self.error_msg = Some("Type mismatch");
        return Err(self.error_msg.unwrap());
      }
      return right_ty;
    }
    Ok(left_ty.clone())
  }

  fn tc_var_decl_list(
    &mut self,
    node: &AstNode,
  ) -> Result<Rc<Type>, &'a str> {
    let node = unbox!(VarDeclListNode, node);
    let mut res: Result<Rc<Type>, &'a str>;
    for decl in &node.decls {
      res = self.tc_var_decl(decl);
      if res.is_err() {
        return res;
      }
    }
    Ok(Rc::new(Type::new(TypeLiteral::TYPE_NIL)))
  }

  fn tc_call(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    let node = unbox!(FnCallNode, node);
    // using unwrap() as semantic analysis guarantees that the
    // function exists before arriving at typechecking
    let (ty, _) = self.sym_tab.symbols().get(&node.name).unwrap();
    let ty = ty.clone();
    // check that it's a function
    if ty.kind.get() != TypeLiteral::TYPE_FUNC {
      self.error_msg = Some("variable is not callable");
      return Err(self.error_msg.unwrap());
    }
    // check that params have expected types
    let tmp = ty.params.as_ref().unwrap().borrow();
    let mut param_types = tmp.iter();
    for arg in &node.args {
      let exp_ty = param_types.next();
      if let Ok(got_ty) = self.tc(arg) {
        if !exp_ty.as_ref().unwrap().ty.equals(&got_ty) {
          eprintln!(
            "Type error: Expected type {:#?}, bot got type {:#?}",
            exp_ty, got_ty
          );
          self.error_msg = Some("Parameter type mismatch");
          return Err(self.error_msg.unwrap());
        }
      } else {
        return Err(self.error_msg.unwrap());
      }
    }
    // return the return type of the function
    Ok(ty.clone())
  }

  fn tc_prog(&mut self, node: &AstNode) -> Result<Rc<Type>, &'a str> {
    let node = unbox!(ProgramNode, node);
    for decl in &node.decls {
      let res = self.tc(decl);
      if res.is_err() {
        return res;
      }
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
      AstNode::VarNode(nd) => self.tc_var(nd),
      AstNode::AssignNode(_) => self.tc_assign(node),
      AstNode::ReturnNode(_) => self.tc_return(node),
      AstNode::ExprStmtNode(_) => self.tc_expr_stmt(node),
      AstNode::FunctionNode(_) => self.tc_function(node),
      AstNode::BlockStmtNode(nd) => self.tc_block(nd),
      AstNode::IfElseNode(_) => self.tc_if_else(node),
      AstNode::ForLoopNode(_) => self.tc_for_loop(node),
      AstNode::WhileLoopNode(_) => self.tc_while_loop(node),
      AstNode::VarDeclNode(nd) => self.tc_var_decl(nd),
      AstNode::VarDeclListNode(_) => self.tc_var_decl_list(node),
      AstNode::FnCallNode(_) => self.tc_call(node),
      AstNode::ProgramNode(_) => self.tc_prog(node),
    }
  }

  pub(crate) fn set_current_fn(&mut self, curr_fn: &str) {
    self.current_fn = curr_fn.into();
  }

  pub fn typecheck(&mut self, node: &AstNode) -> Result<(), &'a str> {
    let ty = self.tc(node);
    if ty.is_ok() {
      return Ok(());
    }
    Err(ty.unwrap_err())
  }
}
