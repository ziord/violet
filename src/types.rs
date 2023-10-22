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
  TYPE_UNION,
  TYPE_LONG,
  TYPE_SHORT,
  TYPE_VOID,
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
  pub(crate) size: u32,      // size of type
  pub(crate) align: u32,     // alignment
  pub(crate) array_len: u32, // length of array if array type
}

pub(crate) type CType = RefCell<Rc<Type>>;

pub(crate) enum TypeId {
  I8 = 0,
  I16,
  I32,
  I64,
}

impl Default for Type {
  fn default() -> Self {
    Self {
      kind: Cell::new(TypeLiteral::TYPE_NIL),
      subtype: RefCell::new(None),
      params: None,
      members: None,
      size: 0,
      align: 1,
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
      align: ty.align,
      array_len: ty.array_len,
    }
  }
}

impl Type {
  pub(crate) fn new(kind: TypeLiteral) -> Self {
    let (sz, al) = Self::get_sal(kind);
    Self {
      kind: Cell::new(kind),
      subtype: RefCell::new(None),
      params: None,
      members: None,
      size: sz,
      align: al,
      array_len: 0,
    }
  }

  fn get_sal(kind: TypeLiteral) -> (u32, u32) {
    // size, align
    let sz;
    let al;
    match kind {
      // sub.size comes from here
      TypeLiteral::TYPE_SHORT => {
        sz = 2;
        al = 2;
      }
      TypeLiteral::TYPE_INT => {
        sz = 4;
        al = 4;
      }
      TypeLiteral::TYPE_LONG | TypeLiteral::TYPE_PTR => {
        sz = 8;
        al = 8;
      }
      TypeLiteral::TYPE_CHAR => {
        sz = 1;
        al = 1;
      }
      TypeLiteral::TYPE_STRUCT => {
        sz = 0;
        al = 1;
      }
      TypeLiteral::TYPE_VOID => {
        sz = 1;
        al = 1;
      }
      _ => {
        sz = 0;
        al = 0;
      }
    };
    (sz, al)
  }

  pub(crate) fn get_typeid(&self) -> TypeId {
    match self.kind.get() {
      TypeLiteral::TYPE_CHAR => TypeId::I8,
      TypeLiteral::TYPE_SHORT => TypeId::I16,
      TypeLiteral::TYPE_INT => TypeId::I32,
      _ => TypeId::I64,
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
    ty.align = sub.align;
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

  pub(crate) fn get_common_type(ty_1: &Rc<Self>, ty_2: &Rc<Self>) -> Self {
    if ty_1.subtype.borrow().is_some() {
      return Self::pointer_to(
        ty_1
          .subtype
          .borrow()
          .as_ref()
          .unwrap()
          .borrow()
          .clone()
          .into(),
      );
    }
    if ty_1.size == 8 || ty_2.size == 8 {
      return Type::new(TypeLiteral::TYPE_LONG);
    }
    Type::new(TypeLiteral::TYPE_INT)
  }

  pub(crate) fn is_integer(&self) -> bool {
    match self.kind.get() {
      TypeLiteral::TYPE_INT
      | TypeLiteral::TYPE_CHAR
      | TypeLiteral::TYPE_SHORT
      | TypeLiteral::TYPE_LONG => true,
      _ => false,
    }
  }

  pub(crate) fn kind_equal(&self, kind: TypeLiteral) -> bool {
    self.kind.get() == kind
  }

  pub(crate) fn align_to(n: u32, align: u32) -> u32 {
    (n + align - 1) / align * align
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
