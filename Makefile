.PHONY: examples

all:
	dune build

examples:
	dune exec -- bitt examples/mltt.bitt	
	dune exec -- bitt examples/hol.bitt	
	dune exec -- bitt examples/mltt-coquand.bitt

test-big-numbers:
	dune exec -- bitt examples/big-numbers.bitt
