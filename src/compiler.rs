use crate::analyzer::SemAnalyzer;
use crate::ast::{
  AstNode, BinaryNode, BlockStmtNode, FunctionNode, NumberNode,
  ProgramNode, VarDeclListNode, VarDeclNode, VarNode,
};
use crate::check::TypeCheck;
use crate::lexer::OpType;
use crate::parser::Parser;
use crate::propagate::{get_type, propagate_types};
use crate::types::{Type, TypeLiteral};
use crate::unbox;
use crate::util;
use std::borrow::Borrow;
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
  gen: GenState,
  arg_regs64: Vec<&'a str>,
  arg_regs8: Vec<&'a str>,
  tc: Option<TypeCheck<'a>>,
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
      arg_regs64: vec!["rdi", "rsi", "rdx", "rcx", "r8", "r9"],
      arg_regs8: vec!["dil", "sil", "dl", "cl", "r8b", "r9b"],
      tc: None,
    }
  }

  fn setup(&self) -> Result<AstNode, &'a str> {
    let content = if self.in_path == V_STDIN {
      util::read_stdin()
    } else {
      util::read_file(self.in_path)
    };
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
          self.c_(&n.left_node);
          self.emit_address(&n.right_node);
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
    if ty.size == 1 {
      // load a value at %rax in memory, and sign-extend it to 64 bits
      // storing it in %rax
      vprintln!(self, "  movsbq (%rax), %rax");
    } else {
      vprintln!(self, "  mov (%rax), %rax");
    }
  }

  fn emit_data(&mut self, node: &ProgramNode) {
    if node.globals.is_empty() {
      return;
    }
    vprintln!(self, "  .data");
    vprint!(self, "  .global ");
    let len = node.globals.len();
    for (i, (_, name, _)) in node.globals.iter().enumerate() {
      vprint!(self, "{}", name);
      if i != len - 1 {
        vprint!(self, ", ");
      }
    }
    vprintln!(self);
    for (ty, name, data) in &node.globals {
      vprintln!(self, "{}:", name);
      if let Some(dat) = data {
        for val in dat.as_str().as_bytes() {
          vprintln!(self, "  .byte {}", val);
        }
      } else {
        vprintln!(self, "  .zero {}", ty.size);
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
    vprintln!(self, "  mov ${}, %rax", node.value);
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
    let ty = get_type(left_node);
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

  fn c_binary(&mut self, node: &AstNode) {
    self.emit_comment("(begin binary expr)");
    let node = unbox!(BinaryNode, node);
    if node.op == OpType::PLUS || node.op == OpType::MINUS {
      // type-check, if any of the operand is a pointer, use c_ptr_binary
      let left_ty = get_type(&node.left_node);
      let right_ty = get_type(&node.right_node);
      if left_ty.subtype.borrow().is_some() && right_ty.is_integer()
        || left_ty.is_integer() && right_ty.subtype.borrow().is_some()
        || left_ty.subtype.borrow().is_some()
          && right_ty.subtype.borrow().is_some()
      {
        return self.c_ptr_binary(node, &left_ty, &right_ty);
      }
    } else if node.op == OpType::COMMA {
      self.c_(&node.left_node);
      self.c_(&node.right_node);
      self.emit_comment("(end binary expr)");
      return;
    }
    self.c_(&node.right_node);
    self.push_reg();
    self.c_(&node.left_node); // places left into %rax
    self.pop_reg("rdi"); // pop right into %rdi
    match node.op {
      OpType::MINUS => {
        vprintln!(self, "  sub %rdi, %rax");
      }
      OpType::PLUS => {
        vprintln!(self, "  add %rdi, %rax");
      }
      OpType::DIV => {
        vprintln!(self, "  cqo"); // %rdx -> %rdx:%rax
        vprintln!(self, "  idiv %rdi");
      }
      OpType::MUL => {
        vprintln!(self, "  imul %rdi, %rax");
      }
      // relational ops
      _ => {
        vprintln!(self, "  cmp %rdi, %rax");
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
        // move value in %al and zero-extend to a byte.
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
    vprintln!(self, "  cmp $0, %rax");
    vprintln!(self, "  je {}", else_label);
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
    vprintln!(self, "  cmp $0, %rax");
    vprintln!(self, "  je {}", end_label);
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
    vprintln!(self, "  cmp $0, %rax");
    vprintln!(self, "  je {}", end_label);
    self.c_(&node.body);
    self.emit_jmp(&cond_label);
    self.emit_label(&end_label);
  }

  fn c_var_decl(&mut self, node: &VarDeclNode) {
    if node.scope == -1 {
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
    vprintln!(self, "  mov $0, %rax");
    // info: clang prepends "_" to function names
    vprintln!(self, "  call _{}", node.name);
  }

  fn c_sizeof(&mut self, node: &AstNode) {
    let node = unbox!(SizeofNode, node);
    let node = AstNode::NumberNode(NumberNode {
      value: node.size.get() as i32,
      ty: RefCell::new(node.ty.borrow().clone()),
      line: node.line,
    });
    self.c_number(&node);
  }

  fn c_stmt_expr(&mut self, node: &AstNode) {
    let node = unbox!(StmtExprNode, node);
    for stmt in &node.stmts {
      self.c_(stmt);
    }
  }

  fn c_function(&mut self, node: &AstNode) {
    let mut func = unbox!(FunctionNode, node);
    self.gen.set_current_fn(&func.name);
    self.store_lvar_offsets(&mut func);
    self.emit_prologue(func);
    // params
    for i in 0..func.params.len() {
      let param = func.params.get(i).unwrap();
      vprintln!(
        self,
        "  mov %{}, {}",
        if param.ty.borrow().size == 1 {
          self.arg_regs8[i]
        } else {
          self.arg_regs64[i]
        },
        self.get_address(&func.params[i].name, func.params[i].scope)
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
    if let Some(line) = node.get_line() {
      vprintln!(self, "  .loc 1 {}", line);
    }

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
      AstNode::StmtExprNode(_) => self.c_stmt_expr(node),
    }
  }

  pub fn compile(&mut self, dis_tc: bool) -> Result<i32, &'a str> {
    // lex and parse
    let res = self.setup();
    if res.is_err() {
      return Err(res.unwrap_err());
    }
    let root = res.unwrap();
    propagate_types(&root);
    // semantic analysis
    let mut sem = SemAnalyzer::new();
    if let Err(msg) = sem.analyze(&root, dis_tc) {
      return Err(msg);
    }
    // compile
    self.tc.replace(TypeCheck::new(sem.move_tab()));
    vprintln!(self, ".file 1 \"{}\"", self.in_path);
    self.c_(&root);
    Ok(0)
  }
}

pub(crate) fn compile_file(in_file: &str, out_file: &str, dis_tc: bool) {
  // todo: remove dis_tc
  let mut cmp = Compiler::new(in_file, out_file);
  let res = cmp.compile(dis_tc);
  if let Err(_v) = res {
    eprintln!("{}", _v);
  }
}
