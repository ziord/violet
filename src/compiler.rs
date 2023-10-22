use crate::ast::{
  AssignNode, AstNode, BinaryNode, BlockStmtNode, CastNode, ExprStmtNode,
  FnCallNode, ForLoopNode, FunctionNode, IfElseNode, NumberNode,
  ProgramNode, ReturnNode, SizeofNode, StmtExprNode, StringNode,
  VarDeclListNode, VarDeclNode, VarNode, WhileLoopNode,
};
use crate::diagnostics::Diagnostic;
use crate::lexer::OpType;
use crate::parser::Parser;
use crate::propagate::propagate_types;
use crate::types::{Type, TypeLiteral};
use crate::unbox;
use crate::util;
use std::borrow::{Borrow, BorrowMut};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

const V_STDIN: &str = "-";

#[derive(Debug)]
struct VarInfo {
  name: String,
  scope: i32,
  offset: i32,
}

#[derive(Debug)]
struct GenState {
  // name, scope, offset
  symbols: Vec<VarInfo>,
  stack_size: u32,
  counter: i32,
  current_fn: Option<String>,
}

impl Default for GenState {
  fn default() -> Self {
    Self {
      symbols: Vec::new(),
      stack_size: 0,
      counter: 0,
      current_fn: None,
    }
  }
}

impl GenState {
  fn get_offset(&self, name: &str, scope: i32) -> i32 {
    for info in &self.symbols {
      if info.scope == scope && info.name == name {
        return info.offset;
      }
    }
    panic!("Unknown variable '{}'", name);
  }

  fn insert(&mut self, name: &str, scope: i32, offset: i32) {
    self.symbols.push(VarInfo {
      name: name.into(),
      scope,
      offset,
    });
  }

  fn set_current_fn(&mut self, name: &str) {
    self.current_fn.replace(name.into());
  }

  fn current_fn(&self) -> &str {
    self.current_fn.as_ref().unwrap().as_str()
  }
}

pub struct Compiler<'a> {
  in_path: &'a str,
  out_file: Box<dyn io::Write>,
  depth: i32,
  diag: Diagnostic,
  gen: GenState,
  arg_regs8: Vec<&'a str>,
  arg_regs16: Vec<&'a str>,
  arg_regs32: Vec<&'a str>,
  arg_regs64: Vec<&'a str>,
}

macro_rules! vprint {
  ($sf:ident) => {
    write!($sf.out_file).expect("Failed to write to file -")
  };
  ($sf:ident, $($tok:tt)*) => {
    write!($sf.out_file, $($tok)*).expect("Failed to write to file -*")
  }
}

macro_rules! vprintln {
  ($sf:ident) => {
    writeln!($sf.out_file).expect("Failed to writeln to file -")
  };
  ($sf:ident, $($tok:tt)*) => {
    writeln!($sf.out_file, $($tok)*).expect("Failed to writeln to file -*")
  }
}

const I8_I32: &str = "movsbl %al, %eax";
const I16_I32: &str = "movswl %ax, %eax";
const I32_I64: &str = "movslq %eax, %rax";
#[rustfmt::skip]
const CAST_TABLE: &'static [[Option<&str>; 4]; 4] = &[
  // i8,  i16,  i32,  i64
  [None, None, None, Some(I32_I64)],                  // i8
  [Some(I8_I32), None, None, Some(I32_I64)],          // i16
  [Some(I8_I32), Some(I16_I32), None, Some(I32_I64)], // i32
  [Some(I8_I32), Some(I16_I32), None, None],          // i64
];

impl<'a> Compiler<'a> {
  pub fn new(in_file: &'a str, out_file: &'a str) -> Self {
    Self {
      in_path: in_file,
      out_file: if out_file.is_empty() {
        Box::new(io::stdout())
      } else {
        Box::new(util::open_file(out_file))
      },
      depth: 0,
      gen: GenState::default(),
      diag: Diagnostic::new(),
      arg_regs8: vec!["dil", "sil", "dl", "cl", "r8b", "r9b"],
      arg_regs16: vec!["di", "si", "dx", "cx", "r8w", "r9w"],
      arg_regs32: vec!["edi", "esi", "edx", "ecx", "r8d", "r9d"],
      arg_regs64: vec!["rdi", "rsi", "rdx", "rcx", "r8", "r9"],
    }
  }

  fn setup(&mut self) -> Result<AstNode, &'a str> {
    let content = if self.in_path == V_STDIN {
      util::read_stdin()
    } else {
      util::read_file(self.in_path)
    };
    if content.is_ok() {
      let content = content.unwrap();
      let mut parser = Parser::new(&content, &mut self.diag);
      return Ok(parser.parse());
    }
    Err("An error occurred while reading file.")
  }

  ///********************
  ///* Codegen Utilities
  ///********************
  fn push_reg(&mut self) {
    vprintln!(self, "  push %rax");
    self.depth += 1;
  }

  fn pop_reg(&mut self, reg: &str) {
    vprintln!(self, "  pop %{}", reg);
    self.depth -= 1;
  }

  fn store_lvar_offsets(&mut self, func: &FunctionNode) {
    /*
     *    |
     *    | ^ <- goes up the stack
     *    | |
     */
    let mut offset = 0;
    self.gen.symbols.clear();
    for (var_name, var_ty, scope) in &func.locals {
      offset += var_ty.size;
      offset = Type::align_to(offset, var_ty.align);
      self.gen.insert(var_name, *scope, -(offset as i32));
    }
    func.stack_size.set(Type::align_to(offset, 16));
  }

  fn get_address(&self, name: &str, scope: i32) -> String {
    // get the offset from rbp
    let offset = self.gen.get_offset(&name, scope);
    format!("{offset}(%rbp)")
  }

  fn create_label(&mut self, prefix: &str, incr: bool) -> String {
    if incr {
      self.gen.counter += 1;
    }
    let count = self.gen.counter;
    format!(".L.{prefix}.{count}")
  }

  fn store_param(&mut self, param: &VarDeclNode, idx: usize) {
    let size = param.ty.borrow().size;
    vprintln!(
      self,
      "  mov %{}, {}",
      if size == 1 {
        self.arg_regs8[idx]
      } else if size == 2 {
        self.arg_regs16[idx]
      } else if size == 4 {
        self.arg_regs32[idx]
      } else {
        self.arg_regs64[idx]
      },
      self.get_address(&param.name, param.scope)
    );
  }

  fn get_axdi(&self, ty: &Rc<Type>) -> (&'a str, &'a str) {
    if ty.kind_equal(TypeLiteral::TYPE_LONG)
      || ty.subtype.borrow().is_some()
    {
      // ax, di
      ("rax", "rdi")
    } else {
      // ax, di
      ("eax", "edi")
    }
  }

  ///********************
  ///* Emitters
  ///********************
  fn emit_comment(&mut self, comment: &str) {
    vprintln!(self, "# {comment}");
  }

  fn emit_label(&mut self, txt: &str) {
    vprintln!(self, "{txt}:");
  }

  fn emit_jmp(&mut self, txt: &str) {
    vprintln!(self, "  jmp {}", txt);
  }

  fn emit_prologue(&mut self, func: &FunctionNode) {
    self.emit_comment("(begin prologue)");
    // set up frame pointer
    vprintln!(self, "  .global _{}", func.name);
    vprintln!(self, "  .text");
    vprintln!(self, "_{}:", func.name);
    vprintln!(self, "  push %rbp");
    vprintln!(self, "  mov %rsp, %rbp");
    // reserve space for locals
    if func.stack_size.get() > 0 {
      vprintln!(self, "  sub ${}, %rsp", func.stack_size.get());
    }
    self.gen.stack_size = func.stack_size.get();
    self.emit_comment("(end prologue)");
  }

  fn emit_epilogue(&mut self) {
    self.emit_comment("(begin epilogue)");
    self.emit_label(&format!(".L.return._{}", self.gen.current_fn()));
    // reset the stack pointer to its original value
    // since (rbp holds the original value,, see prolog())
    vprintln!(self, "  mov %rbp, %rsp");
    // pop frame pointer
    vprintln!(self, "  pop %rbp");
    vprintln!(self, "  ret");
    self.emit_comment("(end epilogue)");
  }

  fn emit_address(&mut self, node: &AstNode) {
    match node {
      AstNode::VarNode(n) => {
        if n.scope > 0 {
          vprintln!(
            self,
            "  lea {}, %rax",
            self.get_address(&n.name, n.scope)
          );
        } else {
          vprintln!(self, "  lea {}(%rip), %rax", n.name);
        }
      }
      AstNode::UnaryNode(ref u_node) => {
        match u_node.op {
          OpType::DEREF => {
            // assuming n is UnaryNode(*)
            // &*var -> var
            self.c_(&u_node.node);
          }
          OpType::DOT => {
            self.emit_address(&u_node.node);
            vprintln!(
              self,
              "  add ${}, %rax",
              u_node.member_t.as_ref().unwrap().offset
            );
          }
          _ => self.emit_address(&u_node.node),
        }
      }
      AstNode::BinaryNode(n) => {
        if n.op == OpType::COMMA {
          self.c_(&n.left);
          self.emit_address(&n.right);
        } else {
          panic!(
            "Unsupported optype for binary node emit_address: {:#?}",
            node
          );
        }
      }
      _ => panic!("Unsupported node for emit_address: {:#?}", node),
    }
  }

  fn emit_store(&mut self, ty: &Type) {
    // val
    self.pop_reg("rdi");
    if ty.kind_equal(TypeLiteral::TYPE_STRUCT)
      || ty.kind_equal(TypeLiteral::TYPE_UNION)
    {
      // copy byte-by-byte into destination
      for i in 0..ty.size {
        vprintln!(self, "  mov {}(%rax), %r8b", i);
        vprintln!(self, "  mov %r8b, {}(%rdi)", i);
      }
      return;
    }
    // store val in memory location identified by rax
    if ty.size == 1 {
      vprintln!(self, "  mov %al, (%rdi)");
    } else if ty.size == 2 {
      vprintln!(self, "  mov %ax, (%rdi)");
    } else if ty.size == 4 {
      vprintln!(self, "  mov %eax, (%rdi)");
    } else {
      vprintln!(self, "  mov %rax, (%rdi)");
    }
  }

  fn emit_load(&mut self, ty: &Type) {
    // move value at address in memory into rax
    match ty.kind.get() {
      // can't load entire array into register
      TypeLiteral::TYPE_ARRAY
      | TypeLiteral::TYPE_STRUCT
      | TypeLiteral::TYPE_UNION => return,
      _ => {}
    };
    // - [[chibicc]]
    // When we load a char or a short value to a register, we always
    // extend them to the size of int, so we can assume the lower half of
    // a register always contains a valid value. The upper half of a
    // register for char, short and int may contain garbage. When we load
    // a long value to a register, it simply occupies the entire register.
    if ty.size == 1 {
      // load a value at (%rax) in memory, and sign-extend it to 32 bits
      // storing it in %eax - lower half or %rax
      vprintln!(self, "  movsbl (%rax), %eax");
    } else if ty.size == 2 {
      vprintln!(self, " movswl (%rax), %eax");
    } else if ty.size == 4 {
      vprintln!(self, " movslq (%rax), %rax");
    } else {
      vprintln!(self, "  mov (%rax), %rax");
    }
  }

  fn emit_data(&mut self, node: &ProgramNode) {
    let decls = node
      .decls
      .iter()
      .filter(|n| n.is_var_decl() || n.is_var_decl_list())
      .collect::<Vec<_>>();
    let mut all_decls = vec![];
    for decl in decls {
      if decl.is_var_decl() {
        all_decls.push(unbox!(VarDeclNode, decl));
      } else {
        let decl_list = unbox!(VarDeclListNode, decl);
        for decl in &decl_list.decls {
          all_decls.push(decl);
        }
      }
    }
    if all_decls.is_empty() {
      return;
    }
    let len = all_decls.len();
    vprintln!(self, "  .data");
    vprint!(self, "  .global ");
    for (i, decl) in all_decls.iter().enumerate() {
      vprint!(self, "{}", decl.name);
      if i != len - 1 {
        vprint!(self, ", ");
      }
    }
    vprintln!(self);
    for decl in all_decls {
      vprintln!(self, "{}:", decl.name);
      if let Some(dat) = &decl.value {
        self.c_(dat);
      } else {
        vprintln!(self, "  .zero {}", decl.ty.borrow().size);
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
  fn c_number(&mut self, node: &NumberNode) {
    vprintln!(self, "  mov ${}, %rax", node.value);
  }

  fn c_str(&mut self, node: &StringNode) {
    for ch in node.value.as_bytes() {
      vprintln!(self, "  .byte {}", ch);
    }
  }

  fn c_var(&mut self, node: &AstNode) {
    // store address in rax
    self.emit_address(node);
    self.emit_load(unbox!(VarNode, node).ty.borrow().as_ref());
  }

  fn _c_assign(&mut self, left: &AstNode, right: &AstNode, _op: &OpType) {
    self.emit_comment("(begin assignment)");
    self.emit_address(left);
    self.push_reg();
    self.c_(right);
    self.emit_store(&left.get_type());
    self.emit_comment("(end assignment)");
  }

  fn c_assign(&mut self, node: &AssignNode) {
    self._c_assign(&node.left, &node.right, &node.op);
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
      left = &node.left;
      right = &node.right;
      _ty = left_ty;
    } else {
      left = &node.right;
      right = &node.left;
      _ty = right_ty;
    }
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
      vprintln!(self, "  imul ${}, %rax, %rax", ptr_size);
      self.push_reg();
      self.c_(left);
      self.pop_reg("rdi");
      // %rax -> %rax + %rdi
      vprintln!(self, "  add %rdi, %rax"); // left + right
    } else {
      if right_ty.is_integer() {
        // ptr - int -> ptr - (int * ptr_size)
        self.c_(right);
        vprintln!(self, "  imul ${}, %rax, %rax", ptr_size);
        self.push_reg();
        self.c_(left);
        self.pop_reg("rdi");
        // %rax -> %rax - %rdi
        vprintln!(self, "  sub %rdi, %rax"); // left - right
      } else {
        // ptr - ptr -> (ptr - ptr) / ptr_size
        self.c_(right);
        self.push_reg();
        self.c_(left);
        self.pop_reg("rdi");
        vprintln!(self, "  sub %rdi, %rax"); // right -> left - right
        vprintln!(self, "  mov ${}, %rdi", ptr_size);
        vprintln!(self, "  cqo");
        vprintln!(self, "  idiv %rdi");
      }
    }
  }

  fn c_binary(&mut self, node: &BinaryNode) {
    self.emit_comment("(begin binary expr)");
    if node.op == OpType::PLUS || node.op == OpType::MINUS {
      // type-check, if any of the operand is a pointer, use c_ptr_binary
      let left_ty = node.left.get_type();
      let right_ty = node.right.get_type();
      if left_ty.subtype.borrow().is_some() && right_ty.is_integer()
        || left_ty.is_integer() && right_ty.subtype.borrow().is_some()
        || left_ty.subtype.borrow().is_some()
          && right_ty.subtype.borrow().is_some()
      {
        return self.c_ptr_binary(node, &left_ty, &right_ty);
      }
    } else if node.op == OpType::COMMA {
      self.c_(&node.left);
      self.c_(&node.right);
      self.emit_comment("(end binary expr)");
      return;
    }
    let ty = node.left.get_type();
    let (ax, di) = self.get_axdi(&ty);
    self.c_(&node.right);
    self.push_reg();
    self.c_(&node.left); // places left into %rax
    self.pop_reg("rdi"); // pop right into %rdi
    match node.op {
      OpType::MINUS => {
        vprintln!(self, "  sub %{di}, %{ax}");
      }
      OpType::PLUS => {
        vprintln!(self, "  add %{di}, %{ax}");
      }
      OpType::DIV => {
        // cqo => %rdx -> %rdx:%rax, cdq => %edx -> %edx:%eax
        vprintln!(self, "{}", if ty.size == 8 { "  cqo" } else { "  cdq" });
        vprintln!(self, "  idiv %{di}");
      }
      OpType::MUL => {
        vprintln!(self, "  imul %{di}, %{ax}");
      }
      // relational ops
      _ => {
        vprintln!(self, "  cmp %{di}, %{ax}");
        match node.op {
          OpType::LEQ => {
            vprintln!(self, "  setle %al");
          }
          OpType::GEQ => {
            vprintln!(self, "  setge %al");
          }
          OpType::LT => {
            vprintln!(self, "  setl %al");
          }
          OpType::GT => {
            vprintln!(self, "  setg %al");
          }
          OpType::EQQ => {
            vprintln!(self, "  sete %al");
          }
          OpType::NEQ => {
            vprintln!(self, "  setne %al");
          }
          _ => {
            panic!("Unrecognized operator '{}'", node.op);
          }
        }
        // copy value in %al to %rax and zero-extend.
        vprintln!(self, "  movzb %al, %rax");
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
        vprintln!(self, "  neg %rax");
      }
      OpType::DEREF => {
        self.emit_comment("(begin deref)");
        self.c_(&*u_node.node);
        let node_ty = &u_node.ty.borrow();
        self.emit_load(node_ty);
        self.emit_comment("(end deref)");
      }
      OpType::ADDR => {
        self.emit_address(&*u_node.node);
      }
      OpType::DOT => {
        self.emit_address(node);
        self.emit_load(&u_node.ty.borrow());
      }
      _ => unreachable!(),
    }
  }

  fn c_return(&mut self, node: &ReturnNode) {
    self.c_(&node.expr);
    // emit a jmp to the return site
    // .L.return currently in prologue
    self.emit_jmp(&format!(".L.return._{}", self.gen.current_fn()));
  }

  fn c_expr_stmt(&mut self, node: &ExprStmtNode) {
    self.c_(&node.node);
  }

  fn c_stmt_list(&mut self, stmt_list: &BlockStmtNode) {
    for stmt in &stmt_list.stmts {
      self.c_(stmt);
    }
  }

  fn c_if_else(&mut self, node: &IfElseNode) {
    self.c_(&node.condition);
    // cmp $0, %rax
    // je else_label
    let else_label = self.create_label("else", true);
    // jmp end_label
    let end_label = self.create_label("endif", false);
    vprintln!(self, "  cmp $0, %rax");
    vprintln!(self, "  je {}", else_label);
    self.c_(&node.if_block);
    self.emit_jmp(&end_label);
    self.emit_label(&else_label);
    self.c_(&node.else_block);
    self.emit_label(&end_label);
  }

  fn c_for_loop(&mut self, node: &ForLoopNode) {
    self.c_(&node.init);
    let cond_label = self.create_label("for_cond", true);
    let end_label = self.create_label("for_end", false);
    // condition block
    self.emit_label(&cond_label);
    self.c_(&node.condition);
    vprintln!(self, "  cmp $0, %rax");
    vprintln!(self, "  je {}", end_label);
    // body block
    self.c_(&node.body);
    // incr block
    self.c_(&node.incr);
    self.emit_jmp(&cond_label); // go to condition
    self.emit_label(&end_label); // end of loop
  }

  fn c_while_loop(&mut self, node: &WhileLoopNode) {
    let cond_label = self.create_label("while_cond", true);
    let end_label = self.create_label("while_end", false);
    self.emit_label(&cond_label);
    self.c_(&node.condition);
    vprintln!(self, "  cmp $0, %rax");
    vprintln!(self, "  je {}", end_label);
    self.c_(&node.body);
    self.emit_jmp(&cond_label);
    self.emit_label(&end_label);
  }

  fn c_var_decl(&mut self, node: &VarDeclNode) {
    if node.scope < 1 {
      // global
      return;
    }
    if let Some(val) = &node.value {
      let right_node = val;
      let left_node = Box::new(AstNode::VarNode(VarNode {
        name: node.name.clone(),
        ty: RefCell::new(node.ty.borrow().clone()),
        scope: node.scope,
        line: node.line,
      }));
      self._c_assign(&left_node, &right_node, &OpType::EQ);
    }
  }

  fn c_var_decl_list(&mut self, node: &VarDeclListNode) {
    for decl in &node.decls {
      self.c_var_decl(decl);
    }
  }

  fn c_call(&mut self, node: &FnCallNode) {
    for arg in &node.args {
      self.c_(arg);
      self.push_reg();
    }
    // store args in the six registers (reversed)
    for i in (0..node.args.len()).rev() {
      self.pop_reg(self.arg_regs64[i]);
    }
    vprintln!(self, "  mov $0, %rax");
    // info: clang prepends "_" to function names
    vprintln!(self, "  call _{}", node.name);
  }

  fn c_sizeof(&mut self, node: &SizeofNode) {
    let node = NumberNode {
      value: node.size.get() as i64,
      ty: RefCell::new(node.ty.borrow().clone()),
      line: node.line,
    };
    self.c_number(&node);
  }

  fn _cast(&mut self, from_ty: &Rc<Type>, to_ty: &Rc<Type>) {
    if to_ty.kind_equal(TypeLiteral::TYPE_VOID) {
      return;
    }
    if let Some(inst) =
      CAST_TABLE[from_ty.get_typeid() as usize][to_ty.get_typeid() as usize]
    {
      vprintln!(self, "{}", inst);
    }
  }

  fn c_cast(&mut self, node: &CastNode) {
    self.c_(&node.node);
    self._cast(&node.node.get_type(), &node.cast_ty.borrow());
  }

  fn c_stmt_expr(&mut self, node: &StmtExprNode) {
    for stmt in &node.stmts {
      self.c_(stmt);
    }
  }

  fn c_function(&mut self, func: &FunctionNode) {
    if func.is_proto {
      return;
    }
    self.gen.set_current_fn(&func.name);
    self.store_lvar_offsets(func);
    self.emit_prologue(func);
    // params
    for i in 0..func.params.len() {
      let param = func.params.get(i).unwrap();
      self.store_param(param, i);
    }
    self.c_stmt_list(&func.body);
    assert_eq!(self.depth, 0, "Expected depth to be zero");
    self.emit_epilogue();
  }

  fn c_prog(&mut self, node: &ProgramNode) {
    self.emit_data(node);
    self.emit_text(node);
  }

  fn c_(&mut self, node: &AstNode) {
    if let Some(line) = node.get_line() {
      vprintln!(self, "  .loc 1 {}", line);
    }

    match node {
      AstNode::NumberNode(n) => self.c_number(n),
      AstNode::StringNode(n) => self.c_str(n),
      AstNode::EmptyNode(_) => {}
      AstNode::BinaryNode(n) => self.c_binary(n),
      AstNode::UnaryNode(_) => self.c_unary(node),
      AstNode::ExprStmtNode(n) => self.c_expr_stmt(n),
      AstNode::FunctionNode(n) => self.c_function(n),
      AstNode::AssignNode(n) => self.c_assign(n),
      AstNode::VarNode(_) => self.c_var(node),
      AstNode::ReturnNode(n) => self.c_return(n),
      AstNode::BlockStmtNode(n) => self.c_stmt_list(n),
      AstNode::IfElseNode(n) => self.c_if_else(n),
      AstNode::ForLoopNode(n) => self.c_for_loop(n),
      AstNode::WhileLoopNode(n) => self.c_while_loop(n),
      AstNode::VarDeclNode(n) => self.c_var_decl(n),
      AstNode::VarDeclListNode(n) => self.c_var_decl_list(n),
      AstNode::FnCallNode(n) => self.c_call(n),
      AstNode::ProgramNode(n) => self.c_prog(n),
      AstNode::SizeofNode(n) => self.c_sizeof(n),
      AstNode::CastNode(n) => self.c_cast(n),
      AstNode::StmtExprNode(n) => self.c_stmt_expr(n),
    }
  }

  pub fn compile(&mut self) -> Result<i32, &'a str> {
    // lex and parse
    let res = self.setup();
    if res.is_err() {
      return Err(res.unwrap_err());
    }
    let mut root = res.unwrap();
    propagate_types(root.borrow_mut(), &mut self.diag);
    if self.diag.has_error() {
      return Err("compile error");
    }
    vprintln!(self, ".file 1 \"{}\"", self.in_path);
    self.c_(&root);
    Ok(0)
  }
}

pub(crate) fn compile_file(in_file: &str, out_file: &str) {
  let mut cmp = Compiler::new(in_file, out_file);
  let res = cmp.compile();
  if let Err(_v) = res {
    eprintln!("{}", _v);
    cmp.diag.show_error();
  }
}
