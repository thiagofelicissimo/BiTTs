# Bidirectional Type Theories (BiTTs)

This is an implementation of the generic bidirectional typing algorithm presented in [1].

**Disclaimer 0** Do now confuse BiTT with BITT (Brouwerian Intuitionistic
Type Theory) [2].

**Disclaimer 1** This is still a prototype implementation and some parts of it should still be improved in the future, such as error handling.

## Getting Started

We describe two ways of building the project. We recommend trying the first option before using the docker image, which its probably a bit of an overkill solution given the small number of dependencies required.

### Build from scratch 

First ensure that you have all the dependencies installed. These are listed in the `dune-project` but we also recall them here:
```
ocaml  (>= 4.13.1)
dune   (>= 3.3)
sedlex (>= 2.5)
menhir (>= 20220210)
```

See [here](https://ocaml.org/docs/installing-ocaml) how to install OCaml, and once this is done you can install dune, sedlex and menhir by running `opam update` and `opam install dune menhir sedlex`.

Once all the dependencies are installed it suffices to run `make examples`, which should output some typechecking messages.

### Build with Docker

First ensure that you have [Docker](https://docs.docker.com/get-docker/) installed. Then, in the directory `docker/` run `docker build -t bitts .` and then `docker run -it bitts`, which should then give you access to a terminal. Now it suffices to run `cd BiTTs` and `make examples`, which should output some typechecking messages.

## How to use



This project implements the generic bidirectional typing algorithm proposed in [1]. Therefore, when using it one first specifies a type theory to work in and then writes terms inside this theory, which are typechecked by the implementation.


**Disclaimer 2** The goal of this implementation is therefore to typechecker terms in some given *valid* theory (see the definition in [1]). Supposing that the validity assumption is verified, the theorems of *op. cit.* ensure that, if the implementation says that a term is well-typed, then the term is indeed well-typed (a property called *soundness* in *op. cit.*). The implementation does **not** check that the supplied theory is valid. In the future, we plan on extending the implementation to verify this automatically, but for the time being this is left to the user.

### Specifying theories

As described in [1], theories are specified by four types of entries: sort rules, constructor rules, destructor rules and rewrite rules. We now show how these can be specified in the concrete syntax of the implementation. In the following, we take the definitions of terms, substitutions, context, patterns, etc from *op. cit.*. We also recommend looking at the file `examples/mltt.bitt` for more examples of how to define theories.



#### Sort rules

Sort rules are specified by the keyword `sort` along with an identifier and a metavariable context of arguments. For instance, we can specify the basic judgment forms `Tm` and `Ty` of type theory.
```
sort Ty ()

sort Tm (A : Ty)
```

#### Constructor rules

Constructor rules are specified by the keyword `constructor` along with an identifier, a metavariable context $\Theta_p$ of erased arguments, a metavariable context $\Theta_c$ of non-erased arguments and a sort $T$. In addition, the sort $T$ should be a pattern containing exactly the metavariables of $\Theta_p$, in the same order as specified in $\Theta_p$. For instance, we can define constructors for Π and λ with the following declarations (note that we support names with Unicode).
```
constructor Π () (A : Ty, B{x : Tm(A)} : Ty) : Ty

constructor λ (A : Ty, B{x : Tm(A)} : Ty) 
              (t{x : Tm(A)} : Tm(B{x})) 
              : Tm(Π(A, x. B{x}))
```

#### Destructor rules

Destructor rules are specified by the keyword `destructor` along with an identifier, a metavariable context $\Theta_p$ of erased arguments, a principal argument $\texttt{x} : T$, a metavariable context $\Theta_d$ of non-erased arguments and a sort $U$. In addition, the sort $T$ should be a pattern containing exactly the metavariables of $\Theta_p$, in the same order as specified in $\Theta_p$. For instance, we can define application as the following destructor.
```
destructor ﹫ (A : Ty, B{x : Tm(A)} : Ty) 
              (t : Tm(Π(A, x. B{x})))
              (u : Tm(A))
              : Tm(B{u})             
```


#### Rewrite rules

Rewrite rules are specified by the keyword `rewrite` along with a left-hand side headed by a destructor and whose arguments are patterns, and a right-hand side which contains only the metavariables specified by the left-hand side. For instance, we can add $\beta$-reduction with the following rule.
```
rewrite ﹫(λ(x. t{x}), u) --> t{u}
```

### Typechecking terms

After an underlying theory is specified, we can start typechecking terms inside it by declaring top-level definitions. For instance, supposing that the underlying theory contains Π types and a Tarski-style universe, we can define the polymorphic identity function at U with the following declaration.
```
let idU : Tm(Π(U, a. Π(El(a), _. El(a)))) := λ(a. λ(x. x))
```
In order to check this definition, the typechecker first verifies that the given sort is well-typed and then checks the body of the definition against it. If typechecking succeeds, then the definition becomes available to be used in other terms defined later.


### Evaluating terms and checking for equality

We also provide the commands `eval` for evaluating terms to normal form, and `check` for checking that two terms are definitionally equal. For instance, assuming we have added natural numbers to the theory and defined factorial, we can use them to compute the factorial of 3 and check that it is equal to 6.
```
let fact3 : Tm(ℕ) := ﹫(fact, S(S(S(0))))
eval fact3

let 6 : Tm(ℕ) := S(S(S(S(S(S(0))))))
check fact3 = 6
```

Note that these commands do not check that the given terms are well-typed before evaluating them, which can thus lead the evaluation to loop.


## Provided examples

We provide the following examples of theories in the directory `examples/`:

- `mltt.bitt` : Martin-Lof Type Theory with a type-in-type Tarski-style universe closed under all of the following type formers, Π and Σ types, lists, booleans, and the unit, empty and W types. We also give some examples of terms we can write in this theory, such as the (type-theoretic) "axiom of choice", an alternative definition of natural numbers in terms of W types, and basic functions involving natural numbers and lists.

- `mltt-coquand.bitt` : Martin-Lof Type Theory with a hierarchy of (weak) cumulative Coquand-style universes and universe polymorphism, with Π types and natural numbers. As an example of term we can write in this theory, we give the universe-polymorphic identity function.

- `hol.bitt` : Higher-Order Logic (also known as Simple Type Theory) with implication and universal quantification. We give some example of terms we can write in the theory, including an impredicative definition of conjunction along with its derived introduction and elimination rules.

- `big-numbers.bitt` : Excerpt of `mltt.bitt` used to test the performance of the evaluator, computes factorial of 8 in around half a second in the tested machine.

## Implementation

The kernel of the implementation is composed of the files `term.ml`, `value.ml`, `eval.ml` and `typing.ml`, which together make around 350 lines. The whole implementation amounts to around 750 lines (not counting interfaces).

The implementation of rewriting uses a form of untyped NbE with de Bruijn indices for terms and levels for values, which avoids any need to implement functions for shifting indices and for substitution. It is inspired by the following works.

- https://github.com/jozefg/nbe-for-mltt/blob/master/src/lib/nbe.ml
- https://github.com/AndrasKovacs/elaboration-zoo
- https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Colloquia/Sterling/tutorial/lib/Eval.ml
- A simple type-theoretic language: Mini-TT

## References

[1] [Generic bidirectional typing for dependent type theories. Thiago Felicissimo.](https://arxiv.org/abs/2307.08523)

[2] [Computability Beyond Church-Turing via Choice Sequences. Mark Bickford, Liron Cohen, Robert L. Constable, Vincent Rahli](https://dl.acm.org/doi/10.1145/3209108.3209200).
