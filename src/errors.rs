#[derive(Debug, Copy, Clone)]
pub enum ViError {
  EL001, // unrecognized token
  EP001, // mismatch token
  EP002, // missing type
}

#[derive(Debug)]
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
      ViError::EL001 => info!(
        self,
        "Unrecognized token",
        "The token found at this context is illegal/unknown."
      ),
      ViError::EP001 => info!(self, "Token mismatch", ""),
      ViError::EP002 => info!(self, "Missing type", "Variable referenced before declaration"),
    }
  }
}
