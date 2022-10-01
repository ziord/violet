mod analyzer;
mod ast;
mod check;
mod compiler;
mod errors;
mod lexer;
mod parser;
mod propagate;
mod types;
mod util;

use std::env;

fn print_usage() {
  println!("This is Violet, a mini C compiler.");
  println!("Usage: violet [-o <output-file>] <input-file>");
  util::exit(0);
}

fn parse_args() {
  // compiler::compile_file("../violet/grammars/foo.c", "");
  // return;
  let args: Vec<String> = env::args().collect();
  if args.len() < 2 {
    print_usage();
  }
  match args[1].as_str() {
    "--help" => print_usage(),
    "-" => {
      // read from input
      compiler::compile_file("-", "");
    }
    "-o" => {
      // specifies output path
      if args.len() < 3 {
        util::error(
          "Invalid number of arguments for '-o'. Expected output path.",
          1,
        );
      } else if args.len() != 4 {
        util::error("No input file specified", 1);
      }
      compiler::compile_file(&args[3], &args[2]);
    }
    _ => {
      if args.len() > 2 {
        util::error("Invalid number of arguments", 1);
      }
      compiler::compile_file(&args[1], "")
    }
  }
}

fn main() {
  parse_args();
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
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Usage:"));

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
