#[derive(Debug, Copy, Clone)]
pub enum ViError {
  E0000, // placeholder
  EL000, // already at error
  EL001, // unrecognized token
  EL002, // unterminated string
  EL003, // unterminated comment
  EP001, // mismatch token
  EP002, // missing type
  EP003, // invalid hex sequence
  EP004, // void statement expression
  EP005, // member (.) access on non-struct/union
  EP006, // no such struct/union member
  EP007, // variable declared void (void x;)
}

#[derive(Debug, Clone)]
pub struct ErrorInfo<'a> {
  pub error_code: ViError,
  pub error_msg: &'a str,
  pub help_msg: &'a str,
}

impl<'a> ErrorInfo<'a> {
  fn new(code: ViError, msg: &'a str, help: &'a str) -> Self {
    Self {
      error_code: code,
      error_msg: msg,
      help_msg: help,
    }
  }
}
macro_rules! info {
  ($code: expr, $msg: tt, $help: tt) => {
    ErrorInfo::new(*$code, $msg, $help)
  };
}

impl ViError {
  pub fn to_info(&self) -> ErrorInfo {
    match self {
      ViError::E0000 => info!(self, "", ""),
      ViError::EL000 => info!(
        self,
        "Error previously encountered",
        "Cannot continue due to previously encountered error(s)."
      ),
      ViError::EL001 => info!(
        self,
        "Unrecognized token",
        "The token found at this context is illegal/unknown."
      ),
      ViError::EL002 => info!(
        self,
        "Unterminated string", "A string should be closed with a '\"'."
      ),
      ViError::EL003 => info!(
        self,
        "Unterminated comment", "Multiline comments should be closed with a '*/'."
      ),
      ViError::EP001 => info!(self, "Token mismatch", ""),
      ViError::EP002 => info!(
        self,
        "Missing type: variable referenced before declaration",
        "Consider declaring the variable before use."
      ),
      ViError::EP003 => info!(
        self,
        "Invalid hex escape sequence",
        "A hex escape sequence is of the form \\x<nnn>, where <nnn> is 0-9 | a-f | A-F."
      ),
      ViError::EP004 => info!(
        self,
        "Void statement expression",
        "Void statement expressions are not supported."
      ),
      ViError::EP005 => info!(
        self,
        "Invalid member access",
        "The left hand side expression should be a struct or union for '.' access."
      ),
      ViError::EP006 => info!(
        self,
        "No such member",
        "The member referenced is not defined for this type."
      ),
      ViError::EP007 => info!(
        self,
        "Variable declared 'void'",
        "Maybe you meant to use 'void *' ?"
      ),
    }
  }
}
