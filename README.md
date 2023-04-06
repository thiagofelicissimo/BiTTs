# CompLF

This is an implementation of a theory-agnostic bidirectional typing algorithm for the mode-correct moded theories of CompLF.

## What is CompLF?

CompLF is a logical framework suitable for defining computational theories (whose definitional equality is purely generated by rewriting). A key feature of CompLF is the possibility for marking arguments of symbols as erased, which allows for instance to write $\langle t, u \rangle$ instead of $\langle t, u\rangle_{A, x.B}$, making it possible to represent the non-annotated syntaxes that one is used to in type theory. Note that, differently from what happens for instance in Coq, these arguments are *not* reconstructed internally: the real syntax is the one that the user sees (modulo the deBruijn indices). 

Because of erased arguments, typing a term in CompLF is a non-trivial and in general undecidable task. To address this problem, I have designed a theory-agnostic bidirectional typing algorithm for CompLF which can be instantiated by giving modes to a CompLF theory in a "mode-correct" way. Bidirectional typing complements erased arguments very well, as it allows to specify the flow of typing information in a way that makes such arguments redundant, hence eliminating the need to have them in the syntax.

Finally, unlike most frameworks but similarly to Canonical LF, in CompLF there is no meta-level beta-reduction or eta-expansion. Instead, the well-formed terms of CompLF would correspond to the beta-normal eta-long forms (also called *canonical forms*) of a regular type theory. This allows for a more faithful representation of syntax because when defining object theories the non canonical forms don't correspond to any terms of the theory (hence they are normally quotiented out when establishing adequacy). Instead, in CompLF the meaningful terms are exactly the ones that the user can write.
 
## How to use

The file [test/quick_intro.complf](test/quick_intro.complf) gives an introduction to CompLF. You can run `make test` in order to see the output it produces. If you want a more detailed introduction, look at the file [test/intro.complf](test/intro.complf) which explains a bit more some technical parts. 

The full definition of CompLF, its metatheory, the bidirectional typing algorithm, and its soundness and completeness proofs are the subject of an article currently in preparation. A link will be added here as soon as it becomes available.

## Implementation

The kernel of the implementation is composed by the files `term.ml`, `value.ml`, `eval.ml` and `typing.ml`, which together make less the 600 lines. The whole implementation amounts to around 1000 lines.

The implementation of rewriting uses a form of NbE, which avoids any need to implement functions for shifting indices and for substitution. It is inspired by the following works.

- https://github.com/jozefg/nbe-for-mltt/blob/master/src/lib/nbe.ml
- https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Colloquia/Sterling/tutorial/lib/Eval.ml
- A simple type-theoretic language: Mini-TT



