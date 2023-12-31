use crate::ast::AstNode::EmptyNode;
use crate::lexer::OpType;
use crate::types::{CType, TMember, Type};
use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;

#[derive(Debug)]
pub struct NumberNode {
  pub(crate) value: i64,
  pub(crate) line: i32,
  pub(crate) ty: CType,
}

#[derive(Debug)]
pub struct StringNode {
  pub(crate) value: String,
  pub(crate) line: i32,
  pub(crate) ty: CType,
}

#[derive(Debug)]
pub struct BinaryNode {
  pub(crate) left: Box<AstNode>,
  pub(crate) right: Box<AstNode>,
  pub(crate) op: OpType,
  pub(crate) ty: CType,
}

#[derive(Debug)]
pub struct UnaryNode {
  pub(crate) node: Box<AstNode>,
  pub(crate) op: OpType,
  pub(crate) line: i32,
  pub(crate) member_t: Option<TMember>,
  pub(crate) ty: CType,
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
  pub(crate) ty: CType,
  pub(crate) scope: i32, // globals -> -1, locals > 0
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct AssignNode {
  pub(crate) left: Box<AstNode>,
  pub(crate) right: Box<AstNode>,
  pub(crate) op: OpType,
  pub(crate) ty: CType,
}

#[allow(dead_code)]
#[derive(Debug)]
pub struct FunctionNode {
  pub(crate) name: String,
  pub(crate) stack_size: Cell<u32>,
  pub(crate) params: Vec<VarDeclNode>,
  pub(crate) body: BlockStmtNode,
  // name, type, scope
  pub(crate) locals: Vec<(String, Rc<Type>, i32)>,
  // is function definition/prototype
  pub(crate) is_proto: bool,
  pub(crate) line: i32,
  pub(crate) ty: CType,
}

#[derive(Debug)]
pub struct ReturnNode {
  pub(crate) expr: Box<AstNode>,
  pub(crate) line: i32,
  pub(crate) ty: CType,
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
  pub(crate) ty: CType,
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
  pub(crate) ty: CType,
}

#[derive(Debug)]
pub struct SizeofNode {
  pub(crate) size: Cell<u32>,
  pub(crate) node: Box<AstNode>,
  pub(crate) line: i32,
  pub(crate) ty: CType,
}

#[derive(Debug)]
pub struct StmtExprNode {
  pub(crate) stmts: Vec<AstNode>,
  pub(crate) line: i32,
  pub(crate) ty: CType,
}

#[derive(Debug)]
pub struct EmptyStmtNode {
  pub(crate) line: i32,
}

#[derive(Debug)]
pub struct CastNode {
  pub(crate) node: Box<AstNode>,
  pub(crate) line: i32,
  pub(crate) cast_ty: CType,
}

#[derive(Debug)]
pub struct ProgramNode {
  pub(crate) decls: VecDeque<AstNode>,
}

#[derive(Debug)]
pub enum AstNode {
  NumberNode(NumberNode),
  StringNode(StringNode),
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
  EmptyNode(EmptyStmtNode),
  CastNode(CastNode),
  ProgramNode(ProgramNode),
}

#[macro_export]
macro_rules! unbox {
  ($tt: tt, $nd: expr) => {
    if let AstNode::$tt(v_) = $nd {
      v_
    } else {
      panic!(
        "Couldn't unbind to AstNode::{}, {:#?}",
        stringify!($tt),
        $nd
      );
    }
  };
}

impl Default for AstNode {
  fn default() -> Self {
    EmptyNode(EmptyStmtNode { line: -1 })
  }
}

impl AstNode {
  pub(crate) fn is_var_decl(&self) -> bool {
    match self {
      AstNode::VarDeclNode(_) => true,
      _ => false,
    }
  }

  pub(crate) fn is_var_decl_list(&self) -> bool {
    match self {
      AstNode::VarDeclListNode(_) => true,
      _ => false,
    }
  }

  pub(crate) fn get_line(&self) -> Option<i32> {
    let line = match self {
      AstNode::NumberNode(n) => Some(n.line),
      AstNode::StringNode(n) => Some(n.line),
      AstNode::EmptyNode(n) => Some(n.line),
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
      AstNode::CastNode(n) => Some(n.line),
      AstNode::ProgramNode(_) => None,
    };
    if let Some(l) = line {
      if l > 0 {
        return line;
      }
    }
    return None;
  }

  pub(crate) fn get_type(&self) -> Rc<Type> {
    match self {
      AstNode::NumberNode(n) => n.ty.borrow().clone(),
      AstNode::StringNode(n) => n.ty.borrow().clone(),
      AstNode::BinaryNode(n) => n.ty.borrow().clone(),
      AstNode::UnaryNode(n) => n.ty.borrow().clone(),
      AstNode::CastNode(n) => n.cast_ty.borrow().clone(),
      AstNode::AssignNode(n) => n.ty.borrow().clone(),
      AstNode::VarNode(n) => n.ty.borrow().clone(),
      AstNode::ReturnNode(n) => n.ty.borrow().clone(),
      AstNode::VarDeclNode(n) => n.ty.borrow().clone(),
      AstNode::FnCallNode(n) => n.ty.borrow().clone(),
      AstNode::SizeofNode(n) => n.ty.borrow().clone(),
      AstNode::StmtExprNode(n) => n.ty.borrow().clone(),
      AstNode::ExprStmtNode(_)
      | AstNode::FunctionNode(_)
      | AstNode::BlockStmtNode(_)
      | AstNode::IfElseNode(_)
      | AstNode::ForLoopNode(_)
      | AstNode::WhileLoopNode(_)
      | AstNode::VarDeclListNode(_)
      | AstNode::EmptyNode(_)
      | AstNode::ProgramNode(_) => Type::rc_default(),
    }
  }
}
