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
	dune exec -- bitts examples/mltt-russell.bitts
	dune exec -- bitts examples/mltt-russell-2.bitts
	dune exec -- bitts examples/ott.bitts
	dune exec -- bitts examples/ott-2.bitts
	dune exec -- bitts examples/mltt-funext-canonicity.bitts
	dune exec -- bitts examples/lambda-mu.bitts
	dune exec -- bitts examples/exceptional.bitts
	dune exec -- bitts examples/exceptional-multiverse.bitts

mltt:
	dune exec -- bitts examples/mltt.bitts

test-big-numbers:
	dune exec -- bitts examples/big-numbers.bitts
