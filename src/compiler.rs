use crate::analyzer::SemAnalyzer;
use crate::ast::{
  AstNode, BinaryNode, BlockStmtNode, FunctionNode, NumberNode,
  ProgramNode, VarDeclListNode, VarDeclNode, VarNode,
};
use crate::lexer::OpType;
use crate::parser::Parser;
use crate::types::{Type, TypeCheck, TypeLiteral};
use crate::util;
use std::borrow::Borrow;
use std::cell::RefCell;
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
  arg_regs64: Vec<&'a str>,
  arg_regs8: Vec<&'a str>,
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
      arg_regs64: vec!["rdi", "rsi", "rdx", "rcx", "r8", "r9"],
      arg_regs8: vec!["dil", "sil", "dl", "cl", "r8b", "r9b"],
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
    let mut offset = 0;
    for (var_ty, var_name) in &func.locals {
      offset += var_ty.size;
      self.gen.symbols.insert(var_name.clone(), -(offset as i32));
    }
    func.stack_size.set(self.align_to(offset as i32, 16));
  }

  fn get_address(&self, name: &str) -> String {
    // get the offset from rbp
    let offset = self.gen.get_offset(&name);
    format!("{offset}(%rbp)")
  }

  fn create_label(&mut self, prefix: &str, incr: bool) -> String {
    if incr {
      self.gen.counter += 1;
    }
    let count = self.gen.counter;
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
    println!("  .text");
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
    self.emit_label(&format!(".L.return._{}", self.gen.current_fn()));
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
        if n.is_local {
          println!("  lea {}, %rax", self.get_address(&n.name));
        } else {
          println!("  lea {}(%rip), %rax", n.name);
        }
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

  fn emit_store(&mut self, ty: &Type) {
    // val
    self.pop_reg("rdi");
    // store val in memory location identified by rax
    if ty.size == 1 {
      println!("  mov %al, (%rdi)");
    } else {
      println!("  mov %rax, (%rdi)");
    }
  }

  fn emit_load(&mut self, ty: &Type) {
    // move value at address in memory into rax
    if ty.kind.get() == TypeLiteral::TYPE_ARRAY {
      // can't load entire array into register
      return;
    }
    if ty.size == 1 {
      // load a value at %rax in memory, and sign-extend it to 64 bits
      // storing it in %rax
      println!("  movsbq (%rax), %rax");
    } else {
      println!("  mov (%rax), %rax");
    }
  }

  fn emit_data(&mut self, node: &ProgramNode) {
    if node.globals.is_empty() {
      return;
    }
    println!("  .data");
    print!("  .global ");
    let len = node.globals.len();
    for (i, (_, name, _)) in node.globals.iter().enumerate() {
      print!("{}", name);
      if i != len - 1 {
        print!(", ");
      }
    }
    println!();
    for (ty, name, data) in &node.globals {
      println!("{}:", name);
      if let Some(dat) = data {
        for val in dat.as_str().as_bytes() {
          println!("  .byte {}", val);
        }
      } else {
        println!("  .zero {}", ty.size);
      }
    }
  }

  fn emit_text(&mut self, node: &ProgramNode) {
    for decl in &node.decls {
      self.c_(decl);
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
    self.emit_load(unbox!(VarNode, node).ty.borrow().as_ref());
  }

  fn _c_assign(
    &mut self,
    left_node: &AstNode,
    right_node: &AstNode,
    op: &OpType,
  ) {
    // todo: use op
    self.emit_comment("(begin assignment)");
    self.emit_address(left_node);
    self.push_reg();
    self.c_(right_node);
    let ty = self.tc(left_node).unwrap();
    self.emit_store(&ty);
    self.emit_comment("(end assignment)");
  }

  fn c_assign(&mut self, node: &AstNode) {
    let node = unbox!(AssignNode, node);
    self._c_assign(&node.left_node, &node.right_node, &node.op);
  }

  fn c_ptr_binary(
    &mut self,
    node: &BinaryNode,
    left_ty: &Rc<Type>,
    right_ty: &Rc<Type>,
  ) {
    let left: &AstNode;
    let right: &AstNode;
    let _ty;
    if left_ty.subtype.borrow().is_some() {
      left = &node.left_node;
      right = &node.right_node;
      _ty = left_ty;
    } else {
      left = &node.right_node;
      right = &node.left_node;
      _ty = right_ty;
    }
    // 'unwrap()' because semantic analysis guarantees
    let ptr_size = _ty
      .subtype
      .borrow()
      .as_ref()
      .borrow()
      .unwrap()
      .borrow()
      .size;
    if node.op == OpType::PLUS {
      // ptr + int (int + ptr) -> ptr + (int * ptr_size)
      self.c_(right);
      println!("  imul ${}, %rax, %rax", ptr_size);
      self.push_reg();
      self.c_(left);
      self.pop_reg("rdi");
      // %rax -> %rax + %rdi
      println!("  add %rdi, %rax"); // left + right
    } else {
      if right_ty.kind.get() == TypeLiteral::TYPE_INT {
        // ptr - int -> ptr - (int * ptr_size)
        self.c_(right);
        println!("  imul ${}, %rax, %rax", ptr_size);
        self.push_reg();
        self.c_(left);
        self.pop_reg("rdi");
        // %rax -> %rax - %rdi
        println!("  sub %rdi, %rax"); // left - right
      } else {
        // ptr - ptr -> (ptr - ptr) / ptr_size
        self.c_(right);
        self.push_reg();
        self.c_(left);
        self.pop_reg("rdi");
        println!("  sub %rdi, %rax"); // right -> left - right
        println!("  mov ${}, %rdi", ptr_size);
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
      if left_ty.subtype.borrow().is_some()
        && right_ty.kind.get() == TypeLiteral::TYPE_INT
        || left_ty.kind.get() == TypeLiteral::TYPE_INT
          && right_ty.subtype.borrow().is_some()
        || left_ty.subtype.borrow().is_some()
          && right_ty.subtype.borrow().is_some()
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
        // move value in %al and zero-extend to a byte.
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
        // todo: once type-checking is enabled, we can use the
        //   unary node's type directly here, since it'll already
        //   be propagated by the type checker
        let node_ty = self.tc(node).unwrap();
        self.emit_load(&node_ty);
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
    self.emit_jmp(&format!(".L.return._{}", self.gen.current_fn()));
  }

  fn c_expr_stmt(&mut self, node: &AstNode) {
    self.c_(&unbox!(ExprStmtNode, node).node);
  }

  fn c_stmt_list(&mut self, stmt_list: &BlockStmtNode) {
    for stmt in &stmt_list.stmts {
      self.c_(stmt);
    }
  }

  fn c_if_else(&mut self, node: &AstNode) {
    let node = unbox!(IfElseNode, node);
    self.c_(&node.condition);
    // cmp $0, %rax
    // je else_label
    let else_label = self.create_label("else", true);
    // jmp end_label
    let end_label = self.create_label("endif", false);
    println!("  cmp $0, %rax");
    println!("  je {}", else_label);
    self.c_(&node.if_block);
    self.emit_jmp(&end_label);
    self.emit_label(&else_label);
    self.c_(&node.else_block);
    self.emit_label(&end_label);
  }

  fn c_for_loop(&mut self, node: &AstNode) {
    let node = unbox!(ForLoopNode, node);
    self.c_(&node.init);
    let cond_label = self.create_label("for_cond", true);
    let end_label = self.create_label("for_end", false);
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
    let cond_label = self.create_label("while_cond", true);
    let end_label = self.create_label("while_end", false);
    self.emit_label(&cond_label);
    self.c_(&node.condition);
    println!("  cmp $0, %rax");
    println!("  je {}", end_label);
    self.c_(&node.body);
    self.emit_jmp(&cond_label);
    self.emit_label(&end_label);
  }

  fn c_var_decl(&mut self, node: &VarDeclNode) {
    if !node.is_local {
      return;
    }
    if let Some(val) = &node.value {
      let right_node = val;
      let left_node = Box::new(AstNode::VarNode(VarNode {
        name: node.name.clone(),
        ty: RefCell::new(node.ty.borrow().clone()),
        is_local: node.is_local,
      }));
      self._c_assign(&left_node, &right_node, &OpType::EQ);
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
      self.pop_reg(self.arg_regs64[i]);
    }
    println!("  mov $0, %rax");
    // info: clang prepends "_" to function names
    println!("  call _{}", node.name);
  }

  fn c_sizeof(&mut self, node: &AstNode) {
    // todo: remove call to tc when typechecking is enabled in semantic analysis
    let ty = self.tc(node);
    let node = unbox!(SizeofNode, node);
    let node = AstNode::NumberNode(NumberNode {
      value: node.size.get() as i32,
      ty: RefCell::new(ty.unwrap()),
    });
    self.c_number(&node);
  }

  fn c_function(&mut self, node: &AstNode) {
    let mut func = unbox!(FunctionNode, node);
    self.gen.set_current_fn(&func.name);
    self.store_lvar_offsets(&mut func);
    self.emit_prologue(func);
    // params
    for i in 0..func.params.len() {
      let param = func.params.get(i).unwrap();
      println!(
        "  mov %{}, {}",
        if param.ty.borrow().size == 1 {
          self.arg_regs8[i]
        } else {
          self.arg_regs64[i]
        },
        self.get_address(&func.params[i].name)
      );
    }
    self.c_stmt_list(&func.body);
    assert_eq!(self.depth, 0, "Expected depth to be zero");
    self.emit_epilogue();
  }

  fn c_prog(&mut self, node: &AstNode) {
    let node = unbox!(ProgramNode, node);
    self.emit_data(node);
    self.emit_text(node);
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
      AstNode::SizeofNode(_) => self.c_sizeof(node),
    }
  }

  pub fn compile(&mut self, dis_tc: bool) -> Result<i32, &'a str> {
    // lex and parse
    let res = self.setup();
    if res.is_err() {
      return Err(res.unwrap_err());
    }
    let root = res.unwrap();
    // semantic analysis
    let mut sem = SemAnalyzer::new();
    if let Err(msg) = sem.analyze(&root, dis_tc) {
      return Err(msg);
    }
    // compile
    self.tc.replace(TypeCheck::new(sem.move_tab()));
    self.c_(&root);
    Ok(0)
  }
}
