use std::cell::{Cell, RefCell};
use std::rc::Rc;

#[derive(Debug, Copy, Clone, PartialOrd, PartialEq)]
#[allow(non_camel_case_types)]
pub enum TypeLiteral {
  TYPE_NIL,
  TYPE_CHAR,
  TYPE_INT,
  TYPE_PTR,
  TYPE_FUNC,
  TYPE_ARRAY,
  TYPE_STRUCT,
  // TYPE_VOID,
  // TYPE_CHAR,
  // TYPE_BOOL,
}

#[derive(Debug, Clone)]
pub struct TParam {
  pub(crate) name: String,
  pub(crate) ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct TMember {
  pub(crate) name: String,
  pub(crate) ty: Rc<Type>,
  pub(crate) offset: u32,
}

#[derive(Debug, Clone)]
pub struct Type {
  pub(crate) kind: Cell<TypeLiteral>,
  pub(crate) subtype: RefCell<Option<RefCell<Rc<Type>>>>,
  pub(crate) params: Option<RefCell<Vec<TParam>>>,
  pub(crate) members: Option<RefCell<Vec<TMember>>>,
  pub(crate) size: u32,
  pub(crate) array_len: u32,
}

impl Default for Type {
  fn default() -> Self {
    Self {
      kind: Cell::new(TypeLiteral::TYPE_NIL),
      subtype: RefCell::new(None),
      params: None,
      members: None,
      size: 0,
      array_len: 0,
    }
  }
}

impl From<Rc<Type>> for Type {
  fn from(ty: Rc<Type>) -> Self {
    Self {
      kind: ty.kind.clone(),
      subtype: ty.subtype.clone(),
      params: ty.params.clone(),
      members: ty.members.clone(),
      size: ty.size,
      array_len: ty.array_len,
    }
  }
}

impl Type {
  pub(crate) fn new(kind: TypeLiteral) -> Self {
    Self {
      kind: Cell::new(kind),
      subtype: RefCell::new(None),
      params: None,
      members: None,
      size: match kind {
        // sub.size comes from here
        TypeLiteral::TYPE_INT | TypeLiteral::TYPE_PTR => 8,
        TypeLiteral::TYPE_CHAR => 1,
        _ => 0,
      },
      array_len: 0,
    }
  }

  pub(crate) fn rc_default() -> Rc<Self> {
    Rc::new(Self::default())
  }

  pub(crate) fn pointer_to(sub: Type) -> Self {
    let ty = Type::new(TypeLiteral::TYPE_PTR);
    ty.subtype.borrow_mut().replace(RefCell::new(Rc::new(sub)));
    ty
  }

  pub(crate) fn array_of(sub: Type, len: u32) -> Type {
    let mut ty = Type::new(TypeLiteral::TYPE_ARRAY);
    ty.size = sub.size * len;
    ty.array_len = len;
    ty.subtype.borrow_mut().replace(RefCell::new(Rc::new(sub)));
    ty
  }

  pub(crate) fn promote_ty(_self: Rc<Self>, other: Rc<Self>) -> Rc<Self> {
    // promote approximately equal types
    if _self.kind.get() > other.kind.get() {
      return _self;
    }
    other
  }

  pub(crate) fn is_integer(&self) -> bool {
    match self.kind.get() {
      TypeLiteral::TYPE_INT | TypeLiteral::TYPE_CHAR => true,
      _ => false,
    }
  }

  pub(crate) fn equals(&self, other: &Self) -> bool {
    // todo: not exhaustive. fix this.
    if self.kind != other.kind {
      if !(self.is_integer() && other.is_integer()) {
        return false;
      }
    }
    if self.subtype.borrow().is_some() != other.subtype.borrow().is_some() {
      return false;
    }
    if self.subtype.borrow().is_some() {
      let tmp = self.subtype.borrow();
      let sub_t1 = tmp.as_ref().unwrap();
      let tmp = other.subtype.borrow();
      let sub_t2 = tmp.as_ref().unwrap();
      if !sub_t1.borrow().equals(&*sub_t2.borrow()) {
        return false;
      }
    }
    if self.params.is_some() != other.params.is_some() {
      return false;
    }
    if self.params.is_some() {
      let sub_params_1 = self.params.as_ref().unwrap();
      let sub_params_2 = other.params.as_ref().unwrap();
      if sub_params_1.borrow().len() != sub_params_2.borrow().len() {
        return false;
      }
      let sub_params_2 = sub_params_2.borrow();
      let mut sub_params_2_iter = sub_params_2.iter();
      for param in sub_params_1.borrow().iter() {
        if let Some(p) = sub_params_2_iter.next() {
          if param.name != p.name || !param.ty.equals(&p.ty) {
            return false;
          }
        } else {
          return false; // unreachable
        }
      }
    }
    return true;
  }
}
