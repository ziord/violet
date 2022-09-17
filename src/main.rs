mod analyzer;
mod ast;
mod compiler;
mod errors;
mod lexer;
mod parser;
mod types;
mod util;

use std::env;

fn print_help() {
  println!(
    "{}",
    "This is Violet, a mini C compiler.
To compile your C file(s), do: violet file.c"
  )
}

pub(crate) fn compile_file(filename: &str, dis_tc: bool) {
  // todo: remove dis_tc
  let mut cmp = compiler::Compiler::new(filename);
  let res = cmp.compile(dis_tc);
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
    "-" => {
      compile_file("", true)
    }
    f @ _ => {
      // disable typechecking for files (58-68).c & others
      let p = f
        .split("samples/")
        .collect::<Vec<_>>()
        .get(1)
        .unwrap()
        .split(".")
        .collect::<Vec<_>>()
        .get(0)
        .unwrap()
        .parse::<i32>()
        .unwrap_or(0);
      let dis_tc = (58..68).contains(&p)
        || (74..=79).contains(&p)
        || (85..=90).contains(&p);
      compile_file(&args[1], dis_tc)
    }
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
