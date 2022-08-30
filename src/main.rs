mod ast;
mod compiler;
mod errors;
mod lexer;
mod parser;
mod util;
mod types;

use std::env;

fn print_help() {
  println!(
    "{}",
    "This is Violet, a mini C compiler.
To compile your C file(s), do: violet file.c"
  )
}

pub(crate) fn compile_file(filename: &str) {
  let mut cmp = compiler::Compiler::new(filename);
  let res = cmp.compile();
  if let Ok(_v) = res {
    // println!("Exited with code {v}"); // todo
  } else {
    eprintln!("Exited with error {}", res.unwrap_err());
  }
}

fn main() {
  let args: Vec<String> = env::args().collect();
  if args.len() != 2 {
    eprintln!("Invalid number of arguments. Use --help for more info.");
    return;
  }
  // let args = vec![String::from(""), String::from("samples/1.c")];
  dbg!(&args);
  match args[1].as_str() {
    "--help" => print_help(),
    _ => compile_file(&args[1]),
  }
}

mod test {
  #[cfg(test)]
  use std::process::Command;
  #[test]
  fn test_args() {
    // no args
    let output = Command::new("./target/debug/violet")
      .output()
      .expect("Failed to execute 'violet' command");
    let stdout = String::from_utf8_lossy(&output.stderr);
    assert!(stdout.contains("Use --help"));

    // help arg
    let output = Command::new("./target/debug/violet")
      .arg("--help")
      .output()
      .expect("Failed to execute './violet --help' command");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("This is Violet, a mini C compiler"));

    // todo: compile arg
  }

  #[test]
  fn test_help() {
    let output = Command::new("./target/debug/violet")
      .arg("--help")
      .output()
      .expect("Failed to execute 'violet --help' command");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("This is Violet, a mini C compiler."));
  }
}
