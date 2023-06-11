.PHONY: test

all:
	dune build

quick-intro:
	dune exec -- complf test/quick-intro.complf

test:
	dune exec -- complf test/basic-mltt.complf
	dune exec -- complf test/basic-mltt-all-infer.complf
	dune exec -- complf test/hol.complf
	dune exec -- complf test/mltt-univpoly.complf
	dune exec -- complf test/mltt-cumulative-and-univpoly.complf
	dune exec -- complf test/mltt-coquand-universes-and-univpoly.complf

test-big-numbers:
	dune exec -- complf test/big-numbers.complf
