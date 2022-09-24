use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, Error};
pub use std::process::exit;

pub(crate) fn read_file(filename: &str) -> Result<String, Error> {
  Ok(fs::read_to_string(filename)?)
}

pub(crate) fn read_stdin() -> Result<String, Error> {
  let stdin = io::stdin();
  let mut content = String::new();
  let mut line = String::new();
  while stdin.lock().read_line(&mut line)? != 0 {
    content.push_str(&std::mem::take(&mut line));
  }
  Ok(content)
}

#[allow(dead_code)] // todo
pub(crate) fn write_file(
  filename: &str,
  content: String,
) -> Result<(), Error> {
  Ok(fs::write(filename, content)?)
}

pub(crate) fn open_file(filename: &str) -> File {
  let f = OpenOptions::new()
    .write(true)
    .create(true)
    .truncate(true)
    .open(filename)
    .expect(&format!("Unable to open file '{filename}'"));
  f
}

pub(crate) fn error(why: &str, code: i32) -> ! {
  eprintln!("{}", why);
  exit(code);
}

#[macro_export]
macro_rules! verror {
  ($($msg:tt)*) => {
    {
      dbg!($($msg)*);
      panic!($($msg)*)
    }
  }
}
