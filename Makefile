
all:
	dune build @all

.PHONY: all test

test:
	dune runtest
