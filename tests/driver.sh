#!/bin/bash
tmp=$(mktemp -d /tmp/violet-test-XXXXXX)
violet=../violet/target/release/violet
trap 'rm -rf $tmp' INT TERM HUP EXIT
echo > "$tmp"/empty.c

check() {
  if [ $? -eq 0 ]; then
    echo "testing $1 ...passed"
  else
    echo "testing $1 ...failed"
    exit 1
  fi
}

# -o
rm -f "$tmp"/out
${violet} -o "$tmp"/out "$tmp"/empty.c
[ -f "$tmp"/out ]
check -o

# --help
${violet} --help | grep -q violet
check --help

echo OK


