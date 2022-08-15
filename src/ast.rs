use crate::lexer::OpType;

#[derive(Debug)]
pub struct NumberNode {
  pub value: i32,
}

#[derive(Debug)]
pub struct BinaryNode {
  pub left: Box<AstNode>,
  pub right: Box<AstNode>,
  pub op: OpType,
}

#[derive(Debug)]
pub enum AstNode {
  NumberNode(NumberNode),
  BinaryNode(BinaryNode),
}

