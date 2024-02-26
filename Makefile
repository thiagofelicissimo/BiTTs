.PHONY: examples

all:
	dune build

examples:
	dune exec -- bitt examples/mltt.bitt
	dune exec -- bitt examples/hol.bitt
	dune exec -- bitt examples/mltt-tarski.bitt
	dune exec -- bitt examples/mltt-tarski-heterogeneous.bitt
	dune exec -- bitt examples/mltt-coquand.bitt
	dune exec -- bitt examples/mltt-russell.bitt

test-big-numbers:
	dune exec -- bitt examples/big-numbers.bitt
