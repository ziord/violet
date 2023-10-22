#[derive(Debug)]
pub struct DiagInfo {
  msg: String,
  line: i32,
}

#[derive(Debug)]
pub struct Diagnostic {
  pub(crate) msgs: Vec<DiagInfo>,
}

impl Diagnostic {
  pub fn new() -> Self {
    Self { msgs: vec![] }
  }

  pub fn add(&mut self, msg: String, line: i32) {
    self.msgs.push(DiagInfo { msg, line });
  }

  pub fn has_error(&self) -> bool {
    self.msgs.len() > 0
  }

  pub fn show_error(&self) {
    for err in self.msgs.iter() {
      eprintln!("line: {}", err.line);
      eprintln!("\t{}", err.msg);
    }
  }
}
