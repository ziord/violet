use crate::lexer::OpType;
use crate::types::Type;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

#[derive(Debug)]
pub struct NumberNode {
  pub(crate) value: i32,
  pub(crate) ty: RefCell<Rc<Type>>,
}

#[derive(Debug)]
pub struct BinaryNode {
  pub(crate) left_node: Box<AstNode>,
  pub(crate) right_node: Box<AstNode>,
  pub(crate) op: OpType,
}

#[derive(Debug)]
pub struct UnaryNode {
  pub(crate) node: Box<AstNode>,
  pub(crate) op: OpType,
  pub(crate) ty: RefCell<Rc<Type>>,
}

#[derive(Debug)]
pub struct ExprStmtNode {
  pub(crate) node: Box<AstNode>,
}

#[derive(Debug)]
pub struct BlockStmtNode {
  pub(crate) stmts: Vec<AstNode>,
}

#[derive(Debug)]
pub struct VarNode {
  pub(crate) name: String,
  pub(crate) ty: RefCell<Rc<Type>>,
}

#[derive(Debug)]
pub struct AssignNode {
  pub(crate) left_node: Box<AstNode>,
  pub(crate) right_node: Box<AstNode>,
  pub(crate) op: OpType,
}

#[derive(Debug)]
pub struct FunctionNode {
  pub(crate) name: String,
  pub(crate) stack_size: Cell<i32>,
  pub(crate) params: Vec<VarDeclNode>,
  pub(crate) body: BlockStmtNode,
  pub(crate) locals: Vec<(Rc<Type>, String)>,
  pub(crate) ty: RefCell<Rc<Type>>,
}

#[derive(Debug)]
pub struct ReturnNode {
  pub(crate) expr: Box<AstNode>,
}

#[derive(Debug)]
pub struct IfElseNode {
  pub(crate) condition: Box<AstNode>,
  pub(crate) if_block: Box<AstNode>,
  pub(crate) else_block: Box<AstNode>,
}

#[derive(Debug)]
pub struct ForLoopNode {
  pub(crate) init: Box<AstNode>,
  pub(crate) condition: Box<AstNode>,
  pub(crate) incr: Box<AstNode>,
  pub(crate) body: Box<AstNode>,
}

#[derive(Debug)]
pub struct WhileLoopNode {
  pub(crate) condition: Box<AstNode>,
  pub(crate) body: Box<AstNode>,
}

#[derive(Debug)]
pub struct VarDeclNode {
  pub(crate) ty: RefCell<Rc<Type>>,
  pub(crate) name: String,
  pub(crate) value: Option<Box<AstNode>>,
}

#[derive(Debug)]
pub struct VarDeclListNode {
  pub(crate) decls: Vec<VarDeclNode>,
}

#[derive(Debug)]
pub struct FnCallNode {
  pub(crate) name: String,
  pub(crate) args: Vec<AstNode>,
}

#[derive(Debug)]
pub struct ProgramNode {
  pub(crate) decls: Vec<AstNode>,
}

#[derive(Debug)]
pub enum AstNode {
  NumberNode(NumberNode),
  BinaryNode(BinaryNode),
  UnaryNode(UnaryNode),
  ExprStmtNode(ExprStmtNode),
  FunctionNode(FunctionNode),
  AssignNode(AssignNode),
  VarNode(VarNode),
  ReturnNode(ReturnNode),
  BlockStmtNode(BlockStmtNode),
  IfElseNode(IfElseNode),
  ForLoopNode(ForLoopNode),
  WhileLoopNode(WhileLoopNode),
  VarDeclNode(VarDeclNode),
  VarDeclListNode(VarDeclListNode),
  FnCallNode(FnCallNode),
  ProgramNode(ProgramNode),
}
