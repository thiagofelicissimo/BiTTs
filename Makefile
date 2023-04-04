.PHONY: test

all:
	dune build

test:
	dune exec -- complf test/quick_intro.complf

test-big-numbers:
	dune exec -- complf test/big_numbers.complf
