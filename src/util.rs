use std::fs;
use std::io::{self, BufRead, Error};

pub(crate) fn read_file(filename: &str) -> Result<String, Error> {
  Ok(fs::read_to_string(filename)?)
}

pub(crate) fn read_stdin() -> Result<String, Error> {
  let stdin = io::stdin();
  let mut content = String::new();
  for line in stdin.lock().lines() {
    content.push_str(&line.unwrap());
  }
  Ok(content)
}

#[macro_export]
macro_rules! vprint {
  () => {
    print!()
  };
  ($($tok:tt)*) => {
    print!($($tok)*)
  }
}

#[macro_export]
macro_rules! vprintln {
  () => {
    println!()
  };
  ($($tok:tt)*) => {
    println!($($tok)*)
  }
}

#[allow(dead_code)] // todo
pub(crate) fn write_file(
  filename: &str,
  content: String,
) -> Result<(), Error> {
  Ok(fs::write(filename, content)?)
}
