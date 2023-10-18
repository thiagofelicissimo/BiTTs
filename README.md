# Bidirectional Type Theories (BiTTs)

This is an implementation of the generic bidirectional typing algorithm presented in [1].

See examples in `examples/` to see the syntax and the available commands. 

The full definition of our notion of Bidirectional Type Theories, of the bidirectional typing algorithm, and its soundness and completeness proofs are given in [1].

**Disclaimer 0** Do now confuse BiTT with BITT (Brouwerian Intuitionistic
Type Theory) [2].

**Disclaimer 1** The soundness of the algorithm relies on the assumption that the supplied theory is valid (the definition is given in [1]). Checking that this indeed holds is left to the user for the moment. In the future, we plan on implementing an algorithm for trying to verify this automatically.

**Disclaimer 2** This is a prototype implementation, so error handling is still poor.

## Implementation

The kernel of the implementation is composed by the files `term.ml`, `value.ml`, `eval.ml` and `typing.ml`, which together make around 300 lines. The whole implementation amounts to around 650 lines.

The implementation of rewriting uses a form of NbE, which avoids any need to implement functions for shifting indices and for substitution. It is inspired by the following works.

- https://github.com/jozefg/nbe-for-mltt/blob/master/src/lib/nbe.ml
- https://github.com/AndrasKovacs/elaboration-zoo
- https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Colloquia/Sterling/tutorial/lib/Eval.ml
- A simple type-theoretic language: Mini-TT

## References

[1] [Generic bidirectional typing for dependent type theories. Thiago Felicissimo.](https://arxiv.org/abs/2307.08523)

[2] [Computability Beyond Church-Turing via Choice Sequences. Mark Bickford, Liron Cohen, Robert L. Constable, Vincent Rahli](https://dl.acm.org/doi/10.1145/3209108.3209200).
