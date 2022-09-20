CFLAGS=-std=c11 -g -fno-common

TEST_SRCS=$(wildcard tests/*.c)
TESTS=$(TEST_SRCS:.c=)

build:
	cargo build

tests/%:
	$(CC) -o- -E -P -C tests/$*.c | ./target/debug/violet -o tests/$*.asm -
	$(CC) -o $@ tests/$*.asm -xc tests/common

test: $(TESTS)
	for i in $^; do echo $$i; ./$$i || exit 1; echo; done
	tests/driver.sh

test-src:
	cargo test

clean:
	rm -rf target $(TESTS) tests/*.s tests/*.asm
	# rm *.asm *.o tmp*
	echo cleaned.

fmt:
	cargo fmt

.PHONY: test clean fmt build