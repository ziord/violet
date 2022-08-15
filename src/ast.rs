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
pub struct StmtList {
  pub(crate) stmts: Vec<AstNode>,
}

#[derive(Debug)]
pub enum AstNode {
  NumberNode(NumberNode),
  BinaryNode(BinaryNode),
  UnaryNode(UnaryNode),
  ExprStmtNode(ExprStmtNode),
  StmtList(StmtList),
}
