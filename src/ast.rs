use std::cell::Cell;
use crate::lexer::OpType;

#[derive(Debug)]
pub struct NumberNode {
  pub(crate) value: i32,
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
}

#[derive(Debug)]
pub struct ExprStmtNode {
  pub(crate) node: Box<AstNode>,
}

#[derive(Debug)]
pub struct StmtListNode {
  pub(crate) stmts: Vec<AstNode>,
}

#[derive(Debug)]
pub struct VarNode {
  pub(crate) name: String,
}

#[derive(Debug)]
pub struct AssignNode {
  pub(crate) left_node: Box<AstNode>,
  pub(crate) right_node: Box<AstNode>,
  pub(crate) op: OpType,
}

#[derive(Debug)]
pub struct FunctionNode {
  pub(crate) stack_size: Cell<i32>,
  pub(crate) body: StmtListNode,
  pub(crate) locals: Vec<String>,
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
}
