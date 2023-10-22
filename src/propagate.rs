use crate::ast::{
  AssignNode, AstNode, BinaryNode, BlockStmtNode, CastNode, ExprStmtNode,
  FnCallNode, ForLoopNode, FunctionNode, IfElseNode, NumberNode,
  ProgramNode, ReturnNode, SizeofNode, StmtExprNode, UnaryNode,
  VarDeclListNode, VarDeclNode, WhileLoopNode,
};
use crate::diagnostics::Diagnostic;
use crate::lexer::OpType;
use crate::types::{Type, TypeLiteral};
use crate::verror;
use std::cell::RefCell;
use std::rc::Rc;

type Ty = Rc<Type>;

pub struct Propagate<'a> {
  diag: &'a mut Diagnostic,
}

impl<'a> Propagate<'a> {
  pub fn new(diag: &'a mut Diagnostic) -> Self {
    Self { diag }
  }

  fn new_cast(&self, node: AstNode, ty: Type, line: i32) -> AstNode {
    AstNode::CastNode(CastNode {
      node: Box::new(node),
      cast_ty: RefCell::new(Rc::new(ty)),
      line,
    })
  }

  pub(crate) fn usual_arith_conv(
    &self,
    l_node: &mut AstNode,
    r_node: &mut AstNode,
  ) {
    let ty = Type::get_common_type(&l_node.get_type(), &r_node.get_type());
    let l_line = l_node.get_line().unwrap_or(-1);
    let r_line = r_node.get_line().unwrap_or(-1);
    *l_node = self.new_cast(std::mem::take(l_node), ty.clone(), l_line);
    *r_node = self.new_cast(std::mem::take(r_node), ty, r_line);
  }

  // todo: better error reporting
  fn prop_num(&mut self, node: &NumberNode) {
    if node.value > i32::MAX as i64 || node.value < i32::MIN as i64 {
      node.ty.replace(Rc::new(Type::new(TypeLiteral::TYPE_LONG)));
    }
  }

  fn prop_cast(&mut self, node: &mut CastNode) {
    self.prop(&mut node.node);
  }

  fn prop_unary(&mut self, node: &mut UnaryNode) {
    if node.member_t.is_some() {
      // struct member access, type is set at parse time.
      return;
    }
    self.prop(&mut node.node);
    let ty = node.node.get_type();
    // propagate
    match node.op {
      OpType::PLUS | OpType::MINUS => {
        if ty.is_integer() {
          let new_ty = Type::get_common_type(
            &Rc::new(Type::new(TypeLiteral::TYPE_INT)),
            &ty,
          );
          node.node = Box::new(self.new_cast(
            std::mem::take(&mut *node.node),
            new_ty.clone(),
            node.line,
          ));
          node.ty.replace(Rc::new(new_ty));
          return;
        }
      }
      OpType::ADDR => {
        return {
          if ty.kind_equal(TypeLiteral::TYPE_ARRAY) {
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
        }
      }
      OpType::DEREF => {
        let tmp = ty.subtype.borrow();
        if tmp.is_some() {
          // ensure pointer to void isn't being de-referenced.
          if !tmp
            .as_ref()
            .unwrap()
            .borrow()
            .kind_equal(TypeLiteral::TYPE_VOID)
          {
            node.ty.replace(tmp.clone().unwrap().into_inner());
            return;
          }
          verror!("Invalid target for dereference: attempt to dereference a void pointer");
        } else {
          verror!("Invalid target for dereference");
        }
      }
      _ => verror!("unknown unary operator '{:?}'", &node.op),
    }
    verror!("Type mismatch - for unary operation");
  }

  fn binary_ty(
    &mut self,
    node: &BinaryNode,
    left_ty: Ty,
    right_ty: Ty,
  ) -> Ty {
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
          else if right_ty.kind_equal(TypeLiteral::TYPE_PTR) {
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

  fn prop_binary(&mut self, node: &mut BinaryNode) {
    self.prop(&mut node.left);
    self.prop(&mut node.right);
    if node.op != OpType::COMMA {
      if node.left.get_type().is_integer()
        && node.right.get_type().is_integer()
      {
        self.usual_arith_conv(&mut node.left, &mut node.right);
      }
    }
    let ty =
      self.binary_ty(node, node.left.get_type(), node.right.get_type());
    node.ty.replace(ty);
  }

  fn prop_expr_stmt(&mut self, node: &mut ExprStmtNode) {
    self.prop(&mut node.node);
  }

  fn prop_function(&mut self, node: &mut FunctionNode) {
    self.prop_block(&mut node.body);
  }

  fn prop_assign(&mut self, node: &mut AssignNode) {
    self.prop(&mut node.left);
    self.prop(&mut node.right);
    let ty = node.left.get_type();
    let line = node.left.get_line().unwrap_or(-1);
    if ty.kind_equal(TypeLiteral::TYPE_ARRAY) {
      self
        .diag
        .add(String::from("assignment to non-lvalue"), line);
    }
    if !ty.kind_equal(TypeLiteral::TYPE_STRUCT) {
      node.right = Box::new(self.new_cast(
        std::mem::take(&mut *node.right),
        ty.clone().into(),
        line,
      ));
    }
    node.ty.replace(ty);
  }

  fn prop_return(&mut self, node: &mut ReturnNode) {
    self.prop(&mut node.expr);
    node.ty.replace(node.expr.get_type());
  }

  fn prop_block(&mut self, node: &mut BlockStmtNode) {
    for n in &mut node.stmts {
      self.prop(n);
    }
  }

  fn prop_if_else(&mut self, node: &mut IfElseNode) {
    self.prop(&mut node.if_block);
    self.prop(&mut node.else_block)
  }

  fn prop_for_loop(&mut self, node: &mut ForLoopNode) {
    self.prop(&mut node.init);
    self.prop(&mut node.condition);
    self.prop(&mut node.incr);
    self.prop(&mut node.body)
  }

  fn prop_while_loop(&mut self, node: &mut WhileLoopNode) {
    self.prop(&mut node.condition);
    self.prop(&mut node.body)
  }

  fn prop_var_decl(&mut self, node: &mut VarDeclNode) {
    if let Some(v) = &mut node.value {
      self.prop(v);
    }
  }

  fn prop_var_decl_list(&mut self, node: &mut VarDeclListNode) {
    for n in &mut node.decls {
      self.prop_var_decl(n);
    }
  }

  fn prop_sizeof(&mut self, node: &mut SizeofNode) {
    self.prop(&mut node.node);
    node.size.set(node.node.get_type().size);
    node.ty.replace(Rc::new(Type::new(TypeLiteral::TYPE_INT)));
  }

  fn prop_stmt_expr(&mut self, node: &mut StmtExprNode) {
    let mut ty = Type::rc_default();
    for n in &mut node.stmts {
      self.prop(n);
      ty = n.get_type();
    }
    node.ty.replace(ty);
  }

  fn prop_call(&mut self, node: &mut FnCallNode) {
    for arg in &mut node.args {
      self.prop(arg);
    }
    // todo: actually use the function definition's return type
    node.ty = RefCell::new(Rc::new(Type::new(TypeLiteral::TYPE_LONG)));
  }

  fn prop_prog(&mut self, node: &mut ProgramNode) {
    for decl in &mut node.decls {
      self.prop(decl);
    }
  }

  fn prop(&mut self, node: &mut AstNode) {
    match node {
      AstNode::NumberNode(n) => self.prop_num(n),
      AstNode::BinaryNode(n) => self.prop_binary(n),
      AstNode::UnaryNode(n) => self.prop_unary(n),
      AstNode::ExprStmtNode(n) => self.prop_expr_stmt(n),
      AstNode::FunctionNode(n) => self.prop_function(n),
      AstNode::AssignNode(n) => self.prop_assign(n),
      AstNode::ReturnNode(n) => self.prop_return(n),
      AstNode::BlockStmtNode(n) => self.prop_block(n),
      AstNode::IfElseNode(n) => self.prop_if_else(n),
      AstNode::ForLoopNode(n) => self.prop_for_loop(n),
      AstNode::WhileLoopNode(n) => self.prop_while_loop(n),
      AstNode::VarDeclNode(n) => self.prop_var_decl(n),
      AstNode::VarDeclListNode(n) => self.prop_var_decl_list(n),
      AstNode::FnCallNode(n) => self.prop_call(n),
      AstNode::SizeofNode(n) => self.prop_sizeof(n),
      AstNode::StmtExprNode(n) => self.prop_stmt_expr(n),
      AstNode::CastNode(n) => self.prop_cast(n),
      AstNode::ProgramNode(n) => self.prop_prog(n),
      _ => {}
    }
  }
}

pub(crate) fn propagate_types(node: &mut AstNode, diag: &mut Diagnostic) {
  let mut prp = Propagate::new(diag);
  prp.prop(node);
}
