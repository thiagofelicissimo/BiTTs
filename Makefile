.PHONY: test

all:
	dune build

test:
	dune exec -- complf test/quick_intro.complf

all-tests:
	dune exec -- complf test/mltt.complf
	dune exec -- complf test/mltt-cumul.complf
	dune exec -- complf test/coquand_univ_cumul.complf
	dune exec -- complf test/univ.complf
	dune exec -- complf test/hol.complf

test-big-numbers:
	dune exec -- complf test/big_numbers.complf
