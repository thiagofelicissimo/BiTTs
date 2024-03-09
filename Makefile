.PHONY: examples

all:
	dune build

examples:
	dune exec -- bitts examples/mltt.bitts
	dune exec -- bitts examples/hol.bitts
	dune exec -- bitts examples/mltt-tarski.bitts
	dune exec -- bitts examples/mltt-tarski-heterogeneous.bitts
	dune exec -- bitts examples/mltt-coquand.bitts
	dune exec -- bitts examples/observational-type-theory.bitts

test-big-numbers:
	dune exec -- bitts examples/big-numbers.bitts
