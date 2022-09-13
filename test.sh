#!/bin/zsh
cat <<EOF | gcc -xc -c -o tmp/out2.o -
int ret3() { return 3; }
int ret5() { return 5; }
int add(int x, int y) { return x+y; }
int sub(int x, int y) { return x-y; }
int add6(int a, int b, int c, int d, int e, int f) {
  return a+b+c+d+e+f;
}
EOF

assert() {
  expected="$1"
  input="samples/$2"

  ./target/debug/violet "$input" > tmp/out.asm 2>tmp/error || exit
  gcc tmp/out.asm tmp/out2.o -o tmp/out
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
assert 5 '56.c'
assert 5 '57.c'
assert 3 '58.c'
assert 5 '59.c'
assert 8 '60.c'
assert 2 '61.c'
assert 21 '62.c'
assert 66 '63.c'
assert 136 '64.c'
assert 32 '65.c'
assert 7 '66.c'
assert 1 '67.c'
assert 55 '68.c'
assert 3 '69.c'

assert 3 '70.c'
assert 4 '71.c'
assert 5 '72.c'
assert 4 '73.c'

assert 0 '74.c'
assert 1 '75.c'
assert 2 '76.c'
assert 3 '77.c'
assert 4 '78.c'
assert 5 '79.c'

assert 3 '80.c'
assert 4 '81.c'
assert 5 '82.c'
assert 5 '83.c'
assert 5 '84.c'

assert 0 '85.c'
assert 1 '86.c'
assert 2 '87.c'
assert 3 '88.c'
assert 4 '89.c'
assert 5 '90.c'

assert 8 '91.c'
assert 8 '92.c'
assert 8 '93.c'
assert 32 '94.c'
assert 96 '95.c'
assert 32 '96.c'
assert 8 '97.c'
assert 9 '98.c'
assert 9 '99.c'
assert 8 '100.c'
assert 8 '101.c'
assert 1 '102.c'
assert 0 '103.c'
assert 3 '104.c'
assert 7 '105.c'
assert 7 '106.c'
assert 0 '107.c'
assert 1 '108.c'
assert 2 '109.c'
assert 3 '110.c'

assert 8 '111.c'
assert 32 '112.c'
echo OK
