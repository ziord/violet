use crate::ast::{AstNode, BlockStmtNode, FunctionNode, VarNode};
use crate::lexer::OpType;
use crate::parser::Parser;
use crate::util;
use std::collections::HashMap;

#[derive(Debug)]
struct GenState {
  symbols: HashMap<String, i32>,
  stack_size: i32,
  counter: i32,
}

impl Default for GenState {
  fn default() -> Self {
    Self {
      symbols: HashMap::new(),
      stack_size: 0,
      counter: 0,
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
}

#[derive(Debug)]
pub struct Compiler<'a> {
  filename: &'a str,
  depth: i32,
  gen: GenState,
}

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

  fn get_address(&mut self, var: &VarNode) -> String {
    // get the offset from rbp
    let offset = self.gen.get_offset(&var.name);
    format!("{offset}(%rbp)")
  }

  fn create_label(&mut self, prefix: &str) -> String {
    let label = prefix.to_string() + &self.gen.counter.to_string();
    self.gen.counter += 1;
    format!(".L.{}", label)
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

  fn emit_prologue(&mut self, func: &FunctionNode) {
    self.emit_comment("(begin prologue)");
    // set up frame pointer
    println!("  push %rbp");
    println!("  mov %rsp, %rbp");
    // reserve space for locals
    println!("  sub ${}, %rsp", func.stack_size.get());
    self.gen.stack_size = func.stack_size.get();
    self.emit_comment("(end prologue)");
  }

  fn emit_epilogue(&mut self) {
    self.emit_comment("(begin epilogue)");
    self.emit_label(".L.return");
    // reset the stack pointer to its original value
    // since (rbp holds the original value,, see prolog())
    println!("  mov %rbp, %rsp");
    // pop frame pointer
    println!("  pop %rbp");
    self.emit_comment("(end epilogue)");
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
    println!("  lea {}, %rax", self.get_address(unbox!(VarNode, node)));
    // move value at address in memory into rax
    println!("  mov (%rax), %rax");
  }

  fn c_assign(&mut self, node: &AstNode) {
    self.emit_comment("(begin assignment)");
    let node = unbox!(AssignNode, node);
    self.c_(&node.right_node);
    // todo!!! assuming left is VarNode
    let left = unbox!(VarNode, &*node.left_node);
    println!("  mov %rax, {}", self.get_address(left));
    // todo!!! use op
    self.emit_comment("(end assignment)");
  }

  fn c_binary(&mut self, node: &AstNode) {
    self.emit_comment("(begin binary expr)");
    let node = unbox!(BinaryNode, node);
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
    let node = unbox!(UnaryNode, node);
    match node.op {
      OpType::PLUS => {
        self.c_(&*node.node);
      }
      OpType::MINUS => {
        self.c_(&*node.node);
        println!("  neg %rax");
      }
      _ => unreachable!(),
    }
  }

  fn c_return(&mut self, node: &AstNode) {
    let node = unbox!(ReturnNode, node);
    self.c_(&node.expr);
    // emit a jmp to the return site
    println!("  jmp .L.return"); // .L.return currently in prologue
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
    println!("  jmp {}", end_label);
    self.emit_label(&else_label);
    self.c_(&node.else_block);
    self.emit_label(&end_label);
  }

  fn c_function(&mut self, node: &AstNode) {
    let mut func = unbox!(FunctionNode, node);
    self.store_lvar_offsets(&mut func);
    self.emit_prologue(func);
    self.c_stmt_list(&func.body);
    self.emit_epilogue();
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
    }
  }

  pub fn compile(&mut self) -> Result<i32, &'a str> {
    let res = self.setup();
    if res.is_err() {
      return Err(res.unwrap_err());
    }
    let root = res.unwrap();
    println!("  .global _main");
    println!("_main:");
    self.c_(&root);
    println!("  ret");
    Ok(0)
  }
}
