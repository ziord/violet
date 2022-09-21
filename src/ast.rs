use crate::lexer::OpType;
use crate::types::Type;
use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::rc::Rc;

#[derive(Debug)]
pub struct NumberNode {
  pub(crate) value: i32,
  pub(crate) line: i32,
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
  pub(crate) line: i32,
  pub(crate) ty: RefCell<Rc<Type>>,
}

#[derive(Debug)]
pub struct ExprStmtNode {
  pub(crate) node: Box<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct BlockStmtNode {
  pub(crate) stmts: Vec<AstNode>,
}

#[derive(Debug)]
pub struct VarNode {
  pub(crate) name: String,
  pub(crate) ty: RefCell<Rc<Type>>,
  pub(crate) scope: i32, // globals -> -1, locals > 0
  pub(crate) line: i32,
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
  // name, type, scope
  pub(crate) locals: Vec<(String, Rc<Type>, i32)>,
  pub(crate) line: i32,
  pub(crate) ty: RefCell<Rc<Type>>,
}

#[derive(Debug)]
pub struct ReturnNode {
  pub(crate) expr: Box<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct IfElseNode {
  pub(crate) condition: Box<AstNode>,
  pub(crate) if_block: Box<AstNode>,
  pub(crate) else_block: Box<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct ForLoopNode {
  pub(crate) init: Box<AstNode>,
  pub(crate) condition: Box<AstNode>,
  pub(crate) incr: Box<AstNode>,
  pub(crate) body: Box<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct WhileLoopNode {
  pub(crate) condition: Box<AstNode>,
  pub(crate) body: Box<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct VarDeclNode {
  pub(crate) ty: RefCell<Rc<Type>>,
  pub(crate) name: String,
  pub(crate) value: Option<Box<AstNode>>,
  pub(crate) scope: i32,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct VarDeclListNode {
  pub(crate) decls: Vec<VarDeclNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct FnCallNode {
  pub(crate) name: String,
  pub(crate) args: Vec<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct SizeofNode {
  pub(crate) size: Cell<u32>,
  pub(crate) node: Box<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct StmtExprNode {
  pub(crate) stmts: Vec<AstNode>,
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct ProgramNode {
  pub(crate) decls: VecDeque<AstNode>,
  // type, name, init_data (string literal)
  pub(crate) globals: Vec<(Rc<Type>, String, Option<String>)>,
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
  SizeofNode(SizeofNode),
  StmtExprNode(StmtExprNode),
  ProgramNode(ProgramNode),
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

impl AstNode {
  pub(crate) fn get_line(&self) -> Option<i32> {
    match self {
      AstNode::NumberNode(n) => Some(n.line),
      AstNode::BinaryNode(_) => None,
      AstNode::UnaryNode(n) => Some(n.line),
      AstNode::ExprStmtNode(n) => Some(n.line),
      AstNode::FunctionNode(n) => Some(n.line),
      AstNode::AssignNode(_) => None,
      AstNode::VarNode(n) => Some(n.line),
      AstNode::ReturnNode(n) => Some(n.line),
      AstNode::BlockStmtNode(_) => None,
      AstNode::IfElseNode(n) => Some(n.line),
      AstNode::ForLoopNode(n) => Some(n.line),
      AstNode::WhileLoopNode(n) => Some(n.line),
      AstNode::VarDeclNode(n) => {
        if n.line == 0 {
          None
        } else {
          Some(n.line)
        }
      }
      AstNode::VarDeclListNode(n) => Some(n.line),
      AstNode::FnCallNode(n) => Some(n.line),
      AstNode::SizeofNode(n) => Some(n.line),
      AstNode::StmtExprNode(n) => Some(n.line),
      AstNode::ProgramNode(_) => None,
    }
  }
}
