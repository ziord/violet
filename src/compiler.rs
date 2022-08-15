use crate::ast::AstNode;
use crate::lexer::OpType;
use crate::parser::Parser;
use crate::util;

#[derive(Debug)]
pub struct Compiler<'a> {
  filename: &'a str,
  depth: i32,
}

macro_rules! unbind {
  ($tt: tt, $nd: ident) => {
    if let AstNode::$tt(v_) = $nd {
      v_
    } else {
      panic!("Couldn't unbind AstNode::{}", stringify!($tt));
    }
  };
}

impl<'a> Compiler<'a> {
  pub fn new(filename: &'a str) -> Self {
    Self { filename, depth: 0 }
  }

  pub fn setup(&self) -> Result<AstNode, &'a str> {
    let content = util::read_file(self.filename);
    if content.is_ok() {
      let content = content.unwrap();
      let mut parser = Parser::new(&content);
      return Ok(parser.parse());
    }
    Err("An error occurred while reading file.")
  }

  pub fn push_reg(&mut self) {
    println!("  push %rax");
    self.depth += 1;
  }

  pub fn pop_reg(&mut self, reg: &str) {
    println!("  pop %{}", reg);
    self.depth -= 1;
  }

  pub fn c_number(&mut self, node: &AstNode) {
    let node = unbind!(NumberNode, node);
    println!("  mov ${}, %rax", node.value);
  }

  pub fn c_binary(&mut self, node: &AstNode) {
    let node = unbind!(BinaryNode, node);
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
    }
  }

  pub fn c_unary(&mut self, node: &AstNode) {
    let node = unbind!(UnaryNode, node);
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

  pub fn c_(&mut self, node: &AstNode) {
    match node {
      AstNode::NumberNode(_) => self.c_number(node),
      AstNode::BinaryNode(_) => self.c_binary(node),
      AstNode::UnaryNode(_) => self.c_unary(node),
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
