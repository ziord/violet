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

assert 0 '11.c'
assert 1 '12.c'
assert 1 '13.c'
assert 0 '14.c'

assert 1 '15.c'
assert 0 '16.c'
assert 0 '17.c'
assert 1 '18.c'
assert 1 '19.c'
assert 0 '20.c'

assert 1 '21.c'
assert 0 '22.c'
assert 0 '23.c'
assert 1 '24.c'
assert 1 '25.c'
assert 0 '26.c'
assert 3 '27.c'
assert 3 '28.c'
assert 8 '29.c'
assert 6 '30.c'
assert 15 '31.c'
assert 3 '32.c'
assert 8 '33.c'
assert 13 '34.c'
assert 1 '35.c'
assert 2 '36.c'
assert 3 '37.c'
assert 3 '38.c'
assert 5 '39.c'
assert 3 '40.c'
assert 3 '41.c'
assert 2 '42.c'
assert 2 '43.c'
assert 4 '44.c'
assert 3 '45.c'
assert 55 '46.c'
assert 3 '47.c'
assert 10 '48.c'
assert 3 '49.c'
assert 3 '50.c'
assert 5 '51.c'
assert 3 '52.c'
assert 5 '53.c'
assert 7 '54.c'
assert 7 '55.c'
echo OK
