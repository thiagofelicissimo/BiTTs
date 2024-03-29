.PHONY: examples

all:
	dune build

all-examples:
	dune exec -- bitts examples/mltt.bitts
	dune exec -- bitts examples/hol.bitts
	dune exec -- bitts examples/hol-light.bitts
	dune exec -- bitts examples/mltt-tarski.bitts
	dune exec -- bitts examples/mltt-coquand.bitts
	dune exec -- bitts examples/mltt-tarski-heterogeneous.bitts
	dune exec -- bitts examples/ott.bitts
	dune exec -- bitts examples/ott-2.bitts
	dune exec -- bitts examples/mltt-funext-canonicity.bitts

mltt:
	dune exec -- bitts examples/mltt.bitts

test-big-numbers:
	dune exec -- bitts examples/big-numbers.bitts
