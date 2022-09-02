use crate::analyzer::SemAnalyzer;
use crate::ast::{
  AstNode, BinaryNode, BlockStmtNode, FunctionNode, VarDeclListNode,
  VarDeclNode,
};
use crate::lexer::OpType;
use crate::parser::Parser;
use crate::types::{Type, TypeCheck, TypeLiteral};
use crate::util;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug)]
struct GenState {
  symbols: HashMap<String, i32>,
  stack_size: i32,
  counter: i32,
  current_fn: Option<String>,
}

impl Default for GenState {
  fn default() -> Self {
    Self {
      symbols: HashMap::new(),
      stack_size: 0,
      counter: 0,
      current_fn: None,
    }
  }
}

impl GenState {
  fn get_offset(&self, name: &str) -> i32 {
    if let Some(offset) = self.symbols.get(name) {
      *offset
    } else {
      panic!("Unknown variable '{}'", name);
    }
  }

  fn set_current_fn(&mut self, name: &str) {
    self.current_fn.replace(name.into());
  }

  fn current_fn(&self) -> &str {
    self.current_fn.as_ref().unwrap().as_str()
  }
}

#[derive(Debug)]
pub struct Compiler<'a> {
  filename: &'a str,
  depth: i32,
  gen: GenState,
  arg_regs: Vec<&'a str>,
  tc: Option<TypeCheck<'a>>,
}

#[macro_export]
macro_rules! unbox {
  ($tt: tt, $nd: expr) => {
    if let AstNode::$tt(v_) = $nd {
      v_
    } else {
      panic!("Couldn't unbind AstNode::{}", stringify!($tt));
    }
  };
}

impl<'a> Compiler<'a> {
  pub fn new(filename: &'a str) -> Self {
    Self {
      filename,
      depth: 0,
      gen: GenState::default(),
      arg_regs: vec!["rdi", "rsi", "rdx", "rcx", "r8", "r9"],
      tc: None,
    }
  }

  fn setup(&self) -> Result<AstNode, &'a str> {
    let content = util::read_file(self.filename);
    if content.is_ok() {
      let content = content.unwrap();
      let mut parser = Parser::new(&content);
      return Ok(parser.parse());
    }
    Err("An error occurred while reading file.")
  }

  ///********************
  ///* Codegen Utilities
  ///********************
  fn push_reg(&mut self) {
    println!("  push %rax");
    self.depth += 1;
  }

  fn pop_reg(&mut self, reg: &str) {
    println!("  pop %{}", reg);
    self.depth -= 1;
  }

  fn align_to(&self, n: i32, align: i32) -> i32 {
    (n + align - 1) / align * align
  }

  fn store_lvar_offsets(&mut self, func: &FunctionNode) {
    /*
     *    |
     *    | ^ <- goes up the stack
     *    | |
     */
    let mut offset = 8;
    for var in &func.locals {
      self.gen.symbols.insert(var.clone(), -offset);
      offset += 8;
    }
    func
      .stack_size
      .set(self.align_to(func.locals.len() as i32, 16));
  }

  fn get_address(&mut self, name: &str) -> String {
    // get the offset from rbp
    let offset = self.gen.get_offset(&name);
    format!("{offset}(%rbp)")
  }

  fn create_label(&mut self, prefix: &str) -> String {
    let count = self.gen.counter;
    self.gen.counter += 1;
    format!(".L.{prefix}.{count}")
  }

  fn tc(&mut self, node: &AstNode) -> Result<Rc<Type>, &str> {
    self
      .tc
      .as_mut()
      .unwrap()
      .set_current_fn(&self.gen.current_fn.as_ref().unwrap());
    self.tc.as_mut().unwrap().tc(node)
  }

  ///********************
  ///* Emitters
  ///********************
  fn emit_comment(&self, comment: &str) {
    println!("# {comment}");
  }

  fn emit_label(&self, txt: &str) {
    println!("{txt}:");
  }

  fn emit_jmp(&self, txt: &str) {
    println!("  jmp {}", txt);
  }

  fn emit_prologue(&mut self, func: &FunctionNode) {
    self.emit_comment("(begin prologue)");
    // set up frame pointer
    println!("  .global _{}", func.name);
    println!("_{}:", func.name);
    println!("  push %rbp");
    println!("  mov %rsp, %rbp");
    // reserve space for locals
    if func.stack_size.get() > 0 {
      println!("  sub ${}, %rsp", func.stack_size.get());
    }
    self.gen.stack_size = func.stack_size.get();
    self.emit_comment("(end prologue)");
  }

  fn emit_epilogue(&mut self) {
    self.emit_comment("(begin epilogue)");
    self.emit_label(&format!(".L.return.{}", self.gen.current_fn()));
    // reset the stack pointer to its original value
    // since (rbp holds the original value,, see prolog())
    println!("  mov %rbp, %rsp");
    // pop frame pointer
    println!("  pop %rbp");
    println!("  ret");
    self.emit_comment("(end epilogue)");
  }

  fn emit_address(&mut self, node: &AstNode) {
    match node {
      AstNode::VarNode(n) => {
        println!("  lea {}, %rax", self.get_address(&n.name));
      }
      AstNode::UnaryNode(ref addr_node) => {
        match addr_node.op {
          OpType::DEREF => {
            // assuming n is UnaryNode(*)
            // &*var -> var
            self.c_(&addr_node.node);
          }
          _ => self.emit_address(&addr_node.node),
        }
      }
      _ => panic!("Unsupported node for emit_address"),
    }
  }

  ///***********************
  ///* Compilation routines
  ///***********************
  fn c_number(&mut self, node: &AstNode) {
    let node = unbox!(NumberNode, node);
    println!("  mov ${}, %rax", node.value);
  }

  fn c_var(&mut self, node: &AstNode) {
    // store address in rax
    self.emit_address(node);
    // move value at address in memory into rax
    println!("  mov (%rax), %rax");
  }

  fn c_assign(&mut self, node: &AstNode) {
    self.emit_comment("(begin assignment)");
    let node = unbox!(AssignNode, node);
    // todo!!! use op
    if let AstNode::VarNode(left) = &*node.left_node {
      self.c_(&node.right_node);
      println!("  mov %rax, {}", self.get_address(&left.name));
    } else {
      self.c_(&node.right_node);
      self.push_reg();
      self.emit_address(&node.left_node);
      self.pop_reg("rdi"); // val
      println!("  mov %rdi, (%rax)");
    }
    self.emit_comment("(end assignment)");
  }

  fn c_ptr_binary(
    &mut self,
    node: &BinaryNode,
    left_ty: &Rc<Type>,
    right_ty: &Rc<Type>,
  ) {
    let left: &AstNode;
    let right: &AstNode;
    if left_ty.kind.get() == TypeLiteral::TYPE_PTR {
      left = &node.left_node;
      right = &node.right_node;
    } else {
      left = &node.right_node;
      right = &node.left_node;
    }
    if node.op == OpType::PLUS {
      // ptr + int (int + ptr) -> ptr + (int * 8)
      self.c_(right);
      println!("  imul $8, %rax, %rax");
      self.push_reg();
      self.c_(left);
      self.pop_reg("rdi");
      // %rax -> %rax + %rdi
      println!("  add %rdi, %rax"); // left + right
    } else {
      if right_ty.kind.get() == TypeLiteral::TYPE_INT {
        // ptr - int -> ptr - (int * 8)
        self.c_(right);
        println!("  imul $8, %rax, %rax");
        self.push_reg();
        self.c_(left);
        self.pop_reg("rdi");
        // %rax -> %rax - %rdi
        println!("  sub %rdi, %rax"); // left - right
      } else {
        // ptr - ptr -> (ptr - ptr) / 8
        self.c_(right);
        self.push_reg();
        self.c_(left);
        self.pop_reg("rdi");
        println!("  sub %rdi, %rax"); // right -> left - right
        println!("  mov $8, %rdi");
        println!("  cqo");
        println!("  idiv %rdi");
      }
    }
  }

  fn c_binary(&mut self, node: &AstNode) {
    self.emit_comment("(begin binary expr)");
    let node = unbox!(BinaryNode, node);
    if node.op == OpType::PLUS || node.op == OpType::MINUS {
      // type-check, if any of the operand is a pointer, use c_ptr_binary
      let left_ty = self.tc(&node.left_node).unwrap();
      let right_ty = self.tc(&node.right_node).unwrap();
      if left_ty.kind.get() == TypeLiteral::TYPE_PTR
        && right_ty.kind.get() == TypeLiteral::TYPE_INT
        || left_ty.kind.get() == TypeLiteral::TYPE_INT
          && right_ty.kind.get() == TypeLiteral::TYPE_PTR
        || left_ty.kind.get() == TypeLiteral::TYPE_PTR
          && right_ty.kind.get() == TypeLiteral::TYPE_PTR
      {
        return self.c_ptr_binary(node, &left_ty, &right_ty);
      }
    }
    self.c_(&node.right_node);
    self.push_reg();
    self.c_(&node.left_node); // places left into %rax
    self.pop_reg("rdi"); // pop right into %rdi
    match node.op {
      OpType::MINUS => {
        println!("  sub %rdi, %rax");
      }
      OpType::PLUS => {
        println!("  add %rdi, %rax");
      }
      OpType::DIV => {
        println!("  cqo"); // %rdx -> %rdx:%rax
        println!("  idiv %rdi");
      }
      OpType::MUL => {
        println!("  imul %rdi, %rax");
      }
      // relational ops
      _ => {
        println!("  cmp %rdi, %rax");
        match node.op {
          OpType::LEQ => {
            println!("  setle %al");
          }
          OpType::GEQ => {
            println!("  setge %al");
          }
          OpType::LT => {
            println!("  setl %al");
          }
          OpType::GT => {
            println!("  setg %al");
          }
          OpType::EQQ => {
            println!("  sete %al");
          }
          OpType::NEQ => {
            println!("  setne %al");
          }
          _ => {
            panic!("Unrecognized operator '{}'", node.op);
          }
        }
        println!("  movzb %al, %rax");
      }
    }
    self.emit_comment("(end binary expr)");
  }

  fn c_unary(&mut self, node: &AstNode) {
    let u_node = unbox!(UnaryNode, node);
    match u_node.op {
      OpType::PLUS => {
        self.c_(&*u_node.node);
      }
      OpType::MINUS => {
        self.c_(&*u_node.node);
        println!("  neg %rax");
      }
      OpType::DEREF => {
        self.emit_comment("(begin deref)");
        self.c_(&*u_node.node);
        println!("  mov (%rax), %rax");
        self.emit_comment("(end deref)");
      }
      OpType::ADDR => {
        self.emit_address(&*u_node.node);
      }
      _ => unreachable!(),
    }
  }

  fn c_return(&mut self, node: &AstNode) {
    let node = unbox!(ReturnNode, node);
    self.c_(&node.expr);
    // emit a jmp to the return site
    // .L.return currently in prologue
    self.emit_jmp(&format!(".L.return.{}", self.gen.current_fn()));
  }

  fn c_expr_stmt(&mut self, node: &AstNode) {
    self.c_(&unbox!(ExprStmtNode, node).node);
  }

  fn c_stmt_list(&mut self, stmt_list: &BlockStmtNode) {
    for stmt in &stmt_list.stmts {
      self.c_(stmt);
      assert_eq!(self.depth, 0, "Expected depth to be zero");
    }
  }

  fn c_if_else(&mut self, node: &AstNode) {
    let node = unbox!(IfElseNode, node);
    self.c_(&node.condition);
    // cmp $0, %rax
    // je else_label
    let else_label = self.create_label("else");
    println!("  cmp $0, %rax");
    println!("  je {}", else_label);
    self.c_(&node.if_block);
    // jmp end_label
    let end_label = self.create_label("endif");
    self.emit_jmp(&end_label);
    self.emit_label(&else_label);
    self.c_(&node.else_block);
    self.emit_label(&end_label);
  }

  fn c_for_loop(&mut self, node: &AstNode) {
    let node = unbox!(ForLoopNode, node);
    self.c_(&node.init);
    let cond_label = self.create_label("for_cond");
    // let incr_label = self.create_label("for_incr");
    let end_label = self.create_label("for_end");
    // let body_label = self.create_label("for_body");
    // condition block
    self.emit_label(&cond_label);
    self.c_(&node.condition);
    println!("  cmp $0, %rax");
    println!("  je {}", end_label);
    // body block
    self.c_(&node.body);
    // incr block
    self.c_(&node.incr);
    self.emit_jmp(&cond_label); // go to condition
    self.emit_label(&end_label); // end of loop
  }

  fn c_while_loop(&mut self, node: &AstNode) {
    let node = unbox!(WhileLoopNode, node);
    let cond_label = self.create_label("while_cond");
    let end_label = self.create_label("while_end");
    self.emit_label(&cond_label);
    self.c_(&node.condition);
    println!("  cmp $0, %rax");
    println!("  je {}", end_label);
    self.c_(&node.body);
    self.emit_jmp(&cond_label);
    self.emit_label(&end_label);
  }

  fn c_var_decl(&mut self, node: &VarDeclNode) {
    if let Some(val) = &node.value {
      self.c_(val);
      println!("  mov %rax, {}", self.get_address(&node.name));
    }
  }

  fn c_var_decl_list(&mut self, node: &VarDeclListNode) {
    for decl in &node.decls {
      self.c_var_decl(decl);
    }
  }

  fn c_call(&mut self, node: &AstNode) {
    let node = unbox!(FnCallNode, node);
    for arg in &node.args {
      self.c_(arg);
      self.push_reg();
    }
    // store args in the six registers (reversed)
    for i in (0..node.args.len()).rev() {
      self.pop_reg(self.arg_regs[i]);
    }
    println!("  mov $0, %rax");
    // info: clang prepends "_" to function names
    println!("  call _{}", node.name);
  }

  fn c_function(&mut self, node: &AstNode) {
    let mut func = unbox!(FunctionNode, node);
    self.gen.set_current_fn(&func.name);
    self.store_lvar_offsets(&mut func);
    self.emit_prologue(func);
    self.c_stmt_list(&func.body);
    self.emit_epilogue();
  }

  fn c_prog(&mut self, node: &AstNode) {
    let node = unbox!(ProgramNode, node);
    for decl in &node.decls {
      self.c_(decl);
    }
  }

  fn c_(&mut self, node: &AstNode) {
    match node {
      AstNode::NumberNode(_) => self.c_number(node),
      AstNode::BinaryNode(_) => self.c_binary(node),
      AstNode::UnaryNode(_) => self.c_unary(node),
      AstNode::ExprStmtNode(_) => self.c_expr_stmt(node),
      AstNode::FunctionNode(_) => self.c_function(node),
      AstNode::AssignNode(_) => self.c_assign(node),
      AstNode::VarNode(_) => self.c_var(node),
      AstNode::ReturnNode(_) => self.c_return(node),
      AstNode::BlockStmtNode(n) => self.c_stmt_list(n),
      AstNode::IfElseNode(_) => self.c_if_else(node),
      AstNode::ForLoopNode(_) => self.c_for_loop(node),
      AstNode::WhileLoopNode(_) => self.c_while_loop(node),
      AstNode::VarDeclNode(n) => self.c_var_decl(n),
      AstNode::VarDeclListNode(n) => self.c_var_decl_list(n),
      AstNode::FnCallNode(_) => self.c_call(node),
      AstNode::ProgramNode(_) => self.c_prog(node),
    }
  }

  pub fn compile(&mut self) -> Result<i32, &'a str> {
    let res = self.setup();
    if res.is_err() {
      return Err(res.unwrap_err());
    }
    let root = res.unwrap();
    // semantic analysis
    let mut sem = SemAnalyzer::new();
    if let Err(msg) = sem.analyze(&root) {
      return Err(msg);
    }
    self.tc.replace(TypeCheck::new(sem.move_tab()));
    self.c_(&root);
    Ok(0)
  }
}
