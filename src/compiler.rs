use crate::errors::ViError;
use crate::lexer::{Lexer, Token, TokenType};
use crate::util;

pub fn compile(filename: &str) -> Result<i32, &str> {
  let content = util::read_file(filename);
  if let Err(_) = content {
    return Err("An error occurred while reading file.");
  }
  let content = content.unwrap();
  let mut lexer = Lexer::new(&content);
  println!("  .global _main");
  println!("_main:");
  let mut token: Token = lexer.get_token();
  println!("  mov ${}, %rax", token.to_int());
  while token.get_type() != TokenType::EOF {
    token = lexer.get_token();
    match token.get_type() {
      TokenType::PLUS => {
        token = lexer.get_token();
        println!("  add ${}, %rax", token.to_int());
      }
      TokenType::MINUS => {
        token = lexer.get_token();
        println!("  sub ${}, %rax", token.to_int());
      }
      TokenType::EOF => {
        break;
      }
      TokenType::ERROR => {
        panic!("Error occurred: {}", token.value())
      }
      _ => {
        panic!("Reached unreachable");
      }
    }
  }
  // 2 + 3 - 5
  println!("  ret");
  Ok(0)
}
