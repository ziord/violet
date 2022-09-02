run:
	./run.sh 1.c

test:
	cargo test

test-sh:
	./test.sh

clean:
	rm -r target
	rm -r tmp
	rm *.asm *.o tmp*

fmt:
	cargo fmt

.PHONY: test clean fmt