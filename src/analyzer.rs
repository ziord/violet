use crate::ast::{AstNode, BlockStmtNode, VarDeclNode};
use crate::check::TypeCheck;
use crate::types::Type;
use crate::unbox;
use std::borrow::{Borrow, BorrowMut};
use std::collections::{BTreeMap, VecDeque};
use std::fmt::Debug;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct SymbolStack<K, V> {
  // each map represents a scope
  curr: i32,
  stack: VecDeque<BTreeMap<K, V>>,
}

#[derive(Debug)]
pub struct SymbolTable {
  // function name -to- its return-type & symbols
  symbols: BTreeMap<String, (Rc<Type>, SymbolStack<String, Rc<Type>>)>,
}

impl<K, V> Default for SymbolStack<K, V>
where
  K: Debug + Ord + Clone,
  V: Clone,
{
  fn default() -> Self {
    Self {
      curr: 0,
      stack: VecDeque::new(),
    }
  }
}

impl<K, V> SymbolStack<K, V>
where
  K: Debug + Ord + Clone,
  V: Clone,
{
  pub fn new() -> Self {
    Self::default()
  }

  fn index(&self) -> usize {
    self.stack.len() - self.curr as usize
  }

  pub fn scope(&self) -> i32 {
    // self.curr will always be >= 1 as long as self.stack isn't empty
    self.curr - 1
  }

  pub fn clear(&mut self) {
    self.stack.clear();
    self.curr = 0;
  }

  pub fn push_tab(&mut self) {
    self.curr += 1;
    self.stack.push_front(BTreeMap::new());
  }

  pub fn pop_tab(&mut self) {
    // the map at the bottom/first map pushed needs to be accessible
    // hence, we can't decrease self.curr once it's at 1.
    if self.curr <= 1 {
      return;
    }
    self.curr -= 1;
  }

  pub fn get_stack(&self) -> &VecDeque<BTreeMap<K, V>> {
    &self.stack
  }

  pub fn insert_symbol(&mut self, name: &K, v: &V) {
    if self.stack.is_empty() {
      self.push_tab();
    }
    if let Some(t) = self.stack.get_mut(self.index()) {
      t.insert(name.clone(), v.clone());
    }
  }

  pub fn remove_symbol(&mut self, name: K) {
    assert!(!self.stack.is_empty(), "stack shouldn't be empty::remove");
    if let Some(t) = self.stack.get_mut(self.index()) {
      t.remove(&name);
    }
  }

  pub fn lookup_symbol(&self, name: &K) -> Option<V> {
    /*
     * scope increases from 0
     * scp 2<-[...] ---> third scope  (idx 0) <---inner (third in second) ...↓
     * scp 1<-[...] ---> second scope (idx 1) <---inner (second in first) .....↓
     * scp 0<-[...] ---> first scope  (idx 2) <---outer                   .......↓
     */
    // need to start from the current scope
    let tabs: Vec<(_, &BTreeMap<_, _>)> = self
      .stack
      .iter()
      .enumerate()
      .filter(|(pos, _tab)| pos >= &self.index())
      .collect();
    for (_, rc_tab) in tabs {
      if let Some(v) = rc_tab.get(name) {
        return Some(v.clone());
      }
    }
    None
  }

  pub fn rec_lookup(
    tab: &SymbolStack<K, Self>,
    key: &K,
    rec: bool,
  ) -> Option<V> {
    for map in &tab.stack {
      for (_, v) in map {
        let res = v.lookup_symbol(key);
        if res.is_some() {
          return res;
        }
      }
      if !rec {
        break;
      }
    }
    None
  }
}

impl SymbolTable {
  pub fn new() -> Self {
    Self {
      symbols: BTreeMap::new(),
    }
  }

  pub fn symbols(
    &self,
  ) -> &BTreeMap<String, (Rc<Type>, SymbolStack<String, Rc<Type>>)> {
    &self.symbols.borrow()
  }

  pub fn new_func_tab(&mut self, key: &str, val: &Rc<Type>) {
    // automatically create a new function tab
    self
      .symbols
      .borrow_mut()
      .insert(key.into(), (val.clone(), SymbolStack::new()));
  }
}

pub struct SemAnalyzer<'a> {
  sym_tab: Option<SymbolTable>,
  current: String,
  at_error: bool,
  error_msg: Option<&'a str>,
}

impl<'a> SemAnalyzer<'a> {
  pub fn new() -> Self {
    Self {
      sym_tab: Some(SymbolTable::new()),
      current: String::new(),
      at_error: false,
      error_msg: None,
    }
  }

  pub fn move_tab(&mut self) -> SymbolTable {
    self.sym_tab.take().unwrap()
  }

  pub fn curr_tab(
    &mut self,
  ) -> Option<&mut (Rc<Type>, SymbolStack<String, Rc<Type>>)> {
    self
      .sym_tab
      .as_mut()
      .unwrap()
      .symbols
      .get_mut(&self.current)
  }

  pub fn sym_tab(&mut self) -> &SymbolTable {
    self.sym_tab.as_ref().unwrap()
  }

  fn sem_num(&mut self, node: &AstNode) {
    unbox!(NumberNode, node);
  }

  fn sem_var(&mut self, node: &AstNode) {
    unbox!(VarNode, node);
  }

  fn sem_unary(&mut self, node: &AstNode) {
    let node = unbox!(UnaryNode, node);
    self.sem(&node.node);
  }

  fn sem_binary(&mut self, node: &AstNode) {
    let node = unbox!(BinaryNode, node);
    self.sem(&*node.left_node);
    self.sem(&node.right_node);
  }

  fn sem_assign(&mut self, node: &AstNode) {
    let node = unbox!(AssignNode, node);
    self.sem(&*node.left_node);
    self.sem(&node.right_node)
  }

  fn sem_if_else(&mut self, node: &AstNode) {
    let node = unbox!(IfElseNode, node);
    self.sem(&node.condition);
    self.sem(&node.if_block);
    self.sem(&node.else_block)
  }

  fn sem_for_loop(&mut self, node: &AstNode) {
    let node = unbox!(ForLoopNode, node);
    self.sem(&node.init);
    self.sem(&node.condition);
    self.sem(&node.incr);
    self.sem(&node.body)
  }

  fn sem_while_loop(&mut self, node: &AstNode) {
    let node = unbox!(WhileLoopNode, node);
    self.sem(&node.condition);
    self.sem(&node.body)
  }

  fn sem_return(&mut self, node: &AstNode) {
    self.sem(&unbox!(ReturnNode, node).expr)
  }

  fn sem_expr_stmt(&mut self, node: &AstNode) {
    self.sem(&unbox!(ExprStmtNode, node).node)
  }

  fn sem_var_decl(&mut self, node: &VarDeclNode) {
    // todo: need to check for duplicate symbols
    if node.scope == -1 {
      // global
      // pretend the variable is a function and store it in the symbol table
      // but its symbol stack would always be empty
      self
        .sym_tab
        .as_mut()
        .unwrap()
        .new_func_tab(&node.name, &node.ty.borrow());
      return;
    }
    let (_, fn_sym) = self
      .curr_tab()
      .expect("Undefined function access in sym_tab");
    fn_sym.insert_symbol(&node.name, &node.ty.borrow());
  }

  fn sem_var_decl_list(&mut self, node: &AstNode) {
    let node = unbox!(VarDeclListNode, node);
    for decl in &node.decls {
      self.sem_var_decl(decl);
    }
  }

  fn sem_call(&mut self, node: &AstNode) {
    let node = unbox!(FnCallNode, node);
    for arg in &node.args {
      self.sem(arg);
    }
  }

  fn sem_sizeof(&mut self, node: &AstNode) {
    // todo
  }

  fn sem_stmt_expr(&mut self, node: &AstNode) {
    let node = unbox!(StmtExprNode, node);
    for stmt in &node.stmts {
      self.sem(stmt);
    }
  }

  fn sem_block(&mut self, node: &BlockStmtNode) {
    for n in &node.stmts {
      self.sem(n);
    }
  }

  fn sem_function(&mut self, node: &AstNode) {
    let node = unbox!(FunctionNode, node);
    // push a new function symbol table
    self
      .sym_tab
      .as_mut()
      .unwrap()
      .new_func_tab(&node.name, &node.ty.borrow());
    self.current = node.name.clone();
    for param in &node.params {
      self.sem_var_decl(param);
    }
    self.sem_block(&node.body);
  }

  fn sem_prog(&mut self, node: &AstNode) {
    let node = unbox!(ProgramNode, node);
    for decl in &node.decls {
      self.sem(decl);
    }
  }

  fn sem(&mut self, node: &AstNode) {
    match node {
      AstNode::NumberNode(_) => self.sem_num(node),
      AstNode::BinaryNode(_) => self.sem_binary(node),
      AstNode::UnaryNode(_) => self.sem_unary(node),
      AstNode::ExprStmtNode(_) => self.sem_expr_stmt(node),
      AstNode::FunctionNode(_) => self.sem_function(node),
      AstNode::AssignNode(_) => self.sem_assign(node),
      AstNode::VarNode(_) => self.sem_var(node),
      AstNode::ReturnNode(_) => self.sem_return(node),
      AstNode::BlockStmtNode(n) => self.sem_block(n),
      AstNode::IfElseNode(_) => self.sem_if_else(node),
      AstNode::ForLoopNode(_) => self.sem_for_loop(node),
      AstNode::WhileLoopNode(_) => self.sem_while_loop(node),
      AstNode::VarDeclNode(n) => self.sem_var_decl(n),
      AstNode::VarDeclListNode(_) => self.sem_var_decl_list(node),
      AstNode::FnCallNode(_) => self.sem_call(node),
      AstNode::ProgramNode(_) => self.sem_prog(node),
      AstNode::SizeofNode(_) => self.sem_sizeof(node),
      AstNode::StmtExprNode(_) => self.sem_stmt_expr(node),
    }
  }

  // handle semantic checks
  // (e.g. use of undefined variables, variables defined multiple times in the same scope, etc.)
  // handle typechecking

  pub fn analyze(
    &mut self,
    root: &AstNode,
    dis_tc: bool,
  ) -> Result<(), &'a str> {
    // build the symbol table, and perform semantic analysis
    self.sem(root);
    // return if we're already at error
    if self.at_error {
      return Err(self.error_msg.unwrap());
    }
    if !dis_tc {
      // type-check
      let mut tc = TypeCheck::new(self.move_tab());
      let res = tc.typecheck(root);
      self.sym_tab.replace(tc.sym_tab); // collect back
      return res;
    }
    Ok(())
  }
}
