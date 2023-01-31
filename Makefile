.PHONY: test

all:
	dune build --profile release

test:
	dune exec --profile release -- complf test/test.complf
