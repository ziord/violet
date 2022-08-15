#!/bin/zsh
assert() {
  expected="$1"
  input="samples/$2"

  ./target/debug/violet "$input" > tmp/out.asm || exit
  gcc tmp/out.asm -o tmp/out
  ./tmp/out
  actual="$?"

  if [ "$actual" = "$expected" ]; then
    echo "$input => $actual"
  else
    echo "$input => $expected expected, but got $actual"
    exit 1
  fi
}

assert 0 "1.c"
assert 42 "2.c"
assert 21 "3.c"
assert 47 "4.c"
assert 47 "5.c"
assert 15 "6.c"
assert 4 "7.c"
assert 10 "8.c"
assert 10 "9.c"
assert 10 "10.c"

echo OK
