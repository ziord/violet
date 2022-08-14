use std::fs;
use std::io::Error;

pub(crate) fn read_file(filename: &str) -> Result<String, Error> {
  Ok(fs::read_to_string(filename)?)
}

#[allow(dead_code)] // todo
pub(crate) fn write_file(filename: &str, content: String) -> Result<(), Error> {
  Ok(fs::write(filename, content)?)
}
