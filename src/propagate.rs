use crate::ast::{AstNode, BinaryNode, BlockStmtNode, VarDeclNode};
use crate::lexer::OpType;
use crate::types::{Type, TypeLiteral};
use crate::{unbox, verror};
use std::rc::Rc;

type Ty = Rc<Type>;

// todo: better error reporting
fn prop_num(node: &AstNode) -> Ty {
  unbox!(NumberNode, node).ty.borrow().clone()
}

fn prop_var(node: &AstNode) -> Ty {
  unbox!(VarNode, node).ty.borrow().clone()
}

fn prop_unary(node: &AstNode) -> Ty {
  let node = unbox!(UnaryNode, node);
  let ty = prop(&node.node);
  // propagate
  match node.op {
    OpType::PLUS | OpType::MINUS => {
      if ty.is_integer() {
        node.ty.replace(ty.clone());
        return ty;
      }
    }
    OpType::ADDR => {
      return {
        if ty.kind.get() == TypeLiteral::TYPE_ARRAY {
          node.ty.replace(Rc::new(Type::pointer_to(
            ty.subtype
              .borrow()
              .as_ref()
              .unwrap()
              .borrow()
              .clone()
              .into(),
          )));
        } else {
          node.ty.replace(Rc::new(Type::pointer_to(ty.into())));
        }
        node.ty.borrow().clone()
      }
    }
    OpType::DEREF => {
      if ty.subtype.borrow().is_some() {
        node
          .ty
          .replace(ty.subtype.borrow_mut().clone().unwrap().into_inner());
        return node.ty.borrow().clone();
      } else {
        verror!("Invalid target for dereference");
      }
    }
    _ => verror!("unknown unary operator '{:?}'", &node.op),
  }
  verror!("Type mismatch - for unary operation: {:#?}", node);
}

fn binary_ty(node: &BinaryNode, left_ty: Ty, right_ty: Ty) -> Ty {
  match node.op {
    OpType::PLUS | OpType::MINUS => {
      if left_ty.is_integer() {
        // int, int
        if right_ty.is_integer() {
          return Type::promote_ty(left_ty, right_ty);
        }
        // int, ptr/array/function
        else if right_ty.subtype.borrow().is_some() {
          if node.op != OpType::MINUS {
            // int - ptr -> err
            return right_ty;
          }
        }
      } else if left_ty.subtype.borrow().is_some() {
        // ptr/array/function, int
        if right_ty.is_integer() {
          return left_ty;
        }
        // ptr, ptr
        else if right_ty.kind.get() == TypeLiteral::TYPE_PTR {
          return Rc::new(Type::new(TypeLiteral::TYPE_INT));
        }
      }
    }
    OpType::DIV => {
      // int, int
      if left_ty.is_integer() && right_ty.is_integer() {
        return left_ty;
      }
    }
    OpType::MUL => {
      // int, int
      if left_ty.is_integer() && right_ty.is_integer() {
        return left_ty;
      }
    }
    OpType::LEQ
    | OpType::GEQ
    | OpType::LT
    | OpType::GT
    | OpType::EQQ
    | OpType::NEQ => {
      if left_ty.equals(&right_ty) {
        return left_ty;
      }
    }
    OpType::COMMA => return right_ty,
    _ => unreachable!(),
  };
  Type::rc_default()
}

fn prop_binary(node: &AstNode) -> Ty {
  let node = unbox!(BinaryNode, node);
  let left_ty = prop(&node.left_node);
  let right_ty = prop(&node.right_node);
  let ty = binary_ty(node, left_ty, right_ty);
  node.ty.replace(ty.clone());
  ty
}

fn prop_expr_stmt(node: &AstNode) -> Ty {
  let node = unbox!(ExprStmtNode, node);
  prop(&node.node);
  Type::rc_default()
}

fn prop_function(node: &AstNode) -> Ty {
  let node = unbox!(FunctionNode, node);
  prop_block(&node.body);
  Type::rc_default()
}

fn prop_assign(node: &AstNode) -> Ty {
  let node = unbox!(AssignNode, node);
  let ty = prop(&node.left_node);
  prop(&node.right_node);
  node.ty.replace(ty.clone());
  ty
}

fn prop_return(node: &AstNode) -> Ty {
  let node = unbox!(ReturnNode, node);
  let ty = prop(&node.expr);
  node.ty.replace(ty.clone());
  ty
}

fn prop_block(node: &BlockStmtNode) -> Ty {
  for n in &node.stmts {
    prop(n);
  }
  Type::rc_default()
}

fn prop_if_else(node: &AstNode) -> Ty {
  let node = unbox!(IfElseNode, node);
  prop(&node.if_block);
  prop(&node.else_block)
}

fn prop_for_loop(node: &AstNode) -> Ty {
  let node = unbox!(ForLoopNode, node);
  prop(&node.init);
  prop(&node.condition);
  prop(&node.incr);
  prop(&node.body)
}

fn prop_while_loop(node: &AstNode) -> Ty {
  let node = unbox!(WhileLoopNode, node);
  prop(&node.condition);
  prop(&node.body)
}

fn prop_var_decl(node: &VarDeclNode) -> Ty {
  if let Some(v) = &node.value {
    prop(v);
  }
  Type::rc_default()
}

fn prop_var_decl_list(node: &AstNode) -> Ty {
  let node = unbox!(VarDeclListNode, node);
  for n in &node.decls {
    prop_var_decl(n);
  }
  Type::rc_default()
}

fn prop_sizeof(node: &AstNode) -> Ty {
  let node = unbox!(SizeofNode, node);
  let ty = prop(&node.node);
  node.size.set(ty.size);
  let ty = Rc::new(Type::new(TypeLiteral::TYPE_INT));
  node.ty.replace(ty.clone());
  ty
}

fn prop_stmt_expr(node: &AstNode) -> Ty {
  let node = unbox!(StmtExprNode, node);
  let mut ty = Type::rc_default();
  for n in &node.stmts {
    ty = prop(n);
  }
  node.ty.replace(ty.clone());
  ty
}

fn prop_call(node: &AstNode) -> Ty {
  let node = unbox!(FnCallNode, node);
  for arg in &node.args {
    prop(arg);
  }
  // todo: actually use the function definition's return type
  Rc::new(Type::new(TypeLiteral::TYPE_INT))
}

fn prop_prog(node: &AstNode) -> Ty {
  let node = unbox!(ProgramNode, node);
  for decl in &node.decls {
    prop(decl);
  }
  Type::rc_default()
}

fn prop(node: &AstNode) -> Ty {
  match node {
    AstNode::NumberNode(_) => prop_num(node),
    AstNode::BinaryNode(_) => prop_binary(node),
    AstNode::UnaryNode(_) => prop_unary(node),
    AstNode::ExprStmtNode(_) => prop_expr_stmt(node),
    AstNode::FunctionNode(_) => prop_function(node),
    AstNode::AssignNode(_) => prop_assign(node),
    AstNode::VarNode(_) => prop_var(node),
    AstNode::ReturnNode(_) => prop_return(node),
    AstNode::BlockStmtNode(n) => prop_block(n),
    AstNode::IfElseNode(_) => prop_if_else(node),
    AstNode::ForLoopNode(_) => prop_for_loop(node),
    AstNode::WhileLoopNode(_) => prop_while_loop(node),
    AstNode::VarDeclNode(n) => prop_var_decl(n),
    AstNode::VarDeclListNode(_) => prop_var_decl_list(node),
    AstNode::FnCallNode(_) => prop_call(node),
    AstNode::SizeofNode(_) => prop_sizeof(node),
    AstNode::StmtExprNode(_) => prop_stmt_expr(node),
    AstNode::ProgramNode(_) => prop_prog(node),
  }
}

pub(crate) fn get_type(node: &AstNode) -> Ty {
  match node {
    AstNode::NumberNode(n) => n.ty.borrow().clone(),
    AstNode::BinaryNode(n) => n.ty.borrow().clone(),
    AstNode::UnaryNode(n) => n.ty.borrow().clone(),
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
    | AstNode::ProgramNode(_) => Type::rc_default(),
  }
}

pub(crate) fn propagate_types(node: &AstNode) {
  prop(node);
}
