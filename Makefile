all: build

.PHONY: all build test

build:
	dune build

test:
	dune runtest
