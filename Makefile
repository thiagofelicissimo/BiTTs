.PHONY: examples

all:
	dune build

examples:
	dune exec -- bitts examples/mltt.bitt
	dune exec -- bitts examples/hol.bitt
	dune exec -- bitts examples/mltt-tarski.bitt
	dune exec -- bitts examples/mltt-tarski-heterogeneous.bitt
	dune exec -- bitts examples/mltt-coquand.bitt

test-big-numbers:
	dune exec -- bitts examples/big-numbers.bitt
