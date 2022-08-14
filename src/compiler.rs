use crate::util;

fn get_next_int(line: &String, index: usize) -> (i32, usize) {
  let start = index;
  let mut end = index;
  for (idx, chr) in line[start..].char_indices() {
    if !chr.is_digit(10) {
      end += idx;
      break;
    }
  }
  if end == start {
    end += line.len() - start;
  }
  (
    line[start..end]
      .parse::<i32>()
      .expect("substring should be an integer"),
    end,
  )
}

pub fn compile(filename: &str) -> Result<i32, &str> {
  let content = util::read_file(filename);
  if let Err(_) = content {
    return Err("An error occurred while reading file.");
  }
  let content = content.unwrap();
  println!("  .global _main");
  println!("_main:");
  // 2 + 3 - 5
  let (mut int, mut idx) = get_next_int(&content, 0);
  println!("  mov ${}, %rax", int);
  loop {
    if idx >= content.len() {
      break;
    }
    for (index, chr) in content[idx..].char_indices() {
      idx += index;
      match chr {
        ' ' => continue,
        '+' => {
          (int, idx) = get_next_int(&content, idx + 1);
          println!("  add ${}, %rax", int);
          break;
        }
        '-' => {
          (int, idx) = get_next_int(&content, idx + 1);
          println!("  sub ${}, %rax", int);
          break;
        }
        _ => {
          panic!("Unknown operator!");
        }
      };
    }
  }
  println!("  ret");
  Ok(0)
}
