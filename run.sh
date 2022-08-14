#!/bin/zsh
./target/debug/violet "samples/$1" > tmp/out.asm || exit
gcc tmp/out.asm -o tmp/out
./tmp/out
