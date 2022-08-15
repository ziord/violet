use crate::lexer::OpType;

#[derive(Debug)]
pub struct NumberNode {
  pub value: i32,
}

#[derive(Debug)]
pub struct BinaryNode {
  pub left_node: Box<AstNode>,
  pub right_node: Box<AstNode>,
  pub op: OpType,
}

#[derive(Debug)]
pub struct UnaryNode {
  pub node: Box<AstNode>,
  pub op: OpType,
}

#[derive(Debug)]
pub enum AstNode {
  NumberNode(NumberNode),
  BinaryNode(BinaryNode),
  UnaryNode(UnaryNode),
}
