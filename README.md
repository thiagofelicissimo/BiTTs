# Bidirectional Type Theories (BiTTs)

This is an implementation of the generic bidirectional typing algorithm presented in [1].

**Disclaimer 0** Do now confuse BiTT with BITT (Brouwerian Intuitionistic Type Theory) [2].

**Disclaimer 1** This is still a prototype implementation and some parts of it should be improved in the future, such as error handling.

## Building the project

First ensure that you have all the dependencies installed. These are listed in the `dune-project` but we also recall them here:
```
ocaml  (>= 4.13.1)
dune   (>= 3.14)
sedlex (>= 2.5)
menhir (>= 3.0)
```

See [here](https://ocaml.org/docs/installing-ocaml) how to install OCaml, and once this is done you can install dune, sedlex and menhir by running `opam update` and `opam install dune menhir sedlex`.

Once all the dependencies are installed it suffices to run `make mltt` (or `make all-examples`), which should output some typechecking messages.

## How to use

This project implements the generic bidirectional typing algorithm proposed in [1]. Therefore, when using it one first specifies a type theory to work in and then writes terms inside this theory, which are typechecked by the implementation.

### Specifying theories

Theories are specified by four types of entries: sort rules, constructor rules, destructor rules and rewrite rules. We now show how these can be specified in the concrete syntax of the implementation. We also recommend looking at the file `examples/mltt.bitts` for more examples of how to define theories.



#### Sort rules

Sort rules are specified by the keyword `sort` along with an identifier and a metavariable context of arguments. For instance, we can specify the basic judgment forms `Tm` and `Ty` of type theory.
```
sort Ty ()

sort Tm (A : Ty)
```

#### Constructor rules

Constructor rules are specified by the keyword `constructor` along with an identifier, a metavariable context $\Xi_1$ of *erased arguments* (meaning that they are omitted from the syntax), a metavariable context $\Xi_2$ of non-erased arguments and a sort $T$. In addition, the sort $T$ should be a (linear) pattern containing exactly the metavariables of $\Xi_1$, in the same order as specified in $\Xi_1$. For instance, we can define constructors for Π and λ with the following declarations (note that we support names with Unicode).
```
constructor Π () (A : Ty, B{x : Tm(A)} : Ty) : Ty

constructor λ (A : Ty, B{x : Tm(A)} : Ty)
              (t{x : Tm(A)} : Tm(B{x}))
              : Tm(Π(A, x. B{x}))
```


The previous description covers non-indexed types. In order to allow for specifying constructors of an indexed type (such as equality), constructor rules also support equality premises, as illustrated in the following two examples. This is needed because the sort of a constructor rule must be a (linear) pattern precisely on the erased arguments (note that we cannot omit the argument `m` in `consV` because it is needed when writing the rewrite rules for the recursor).
```
(* Equality *)
constructor Eq () (A : Ty, x : Tm(A), y : Tm(A)) : Ty

constructor refl (A : Ty, x : Tm(A), y : Tm(A))
                 ()
                 (x = y : Tm(A))
            : Tm(Eq(A, x, y))
...

(* Vectors *)
constructor Vec () (A : Ty, n : Tm(ℕ)) : Ty

constructor nilV  (A : Ty, n : Tm(ℕ))
                  ()
                  (n = 0 : Tm(ℕ))
                : Tm(Vec(A, n))

constructor consV (A : Ty, n : Tm(ℕ))
                  (m : Tm(ℕ), a : Tm(A), l : Tm(Vec(A, m)))
                  (n = S(m) : Tm(ℕ))
                : Tm(Vec(A, n))
...
```


#### Destructor rules

Destructor rules are specified by the keyword `destructor` along with an identifier, a metavariable context $\Xi_1$ of erased arguments, a principal argument $x : T$, a metavariable context $\Xi_2$ of non-erased arguments and a sort $U$. In addition, the sort $T$ should be a pattern containing exactly the metavariables of $\Xi_1$, in the same order as specified in $\Xi_1$. For instance, we can define application as the following destructor.
```
destructor ﹫ (A : Ty, B{x : Tm(A)} : Ty)
              [t : Tm(Π(A, x. B{x}))]
              (u : Tm(A))
              : Tm(B{u})
```


#### Rewrite rules

Rewrite rules are specified by the keyword `equation` along with a left-hand side which should be a (linear) pattern, and a right-hand side. For instance, we can add $\beta$-reduction with the following rule.
```
equation ﹫(λ(x. t{x}), u) --> t{u}
```

#### Conditions required for the algorithm to be correct

The results of [1] ensure that the type-checker implemented is indeed sound for the bidirectional theory specified by the used, when the following  conditions are met:

- (A).(I) Sort, constructor and destructor rules are well-typed.
- (A).(II) The rewrite system is confluent.
- (A).(III) The rewrite system satisfies subject reduction.
- (B) The patterns of constructor and destructor rules should be (i) *destructor-free* (that is, contain no occurrences of destructors) and (ii) *rigid* (that is, if some subterm of the pattern unifies with the left-hand side of a rewrite rule, then the subterm must be headed by a metavariable). Recall that the pattern of a constructor rule is its sort, and the pattern of a destructor rule is the sort of the principal argument.

In order to help the user, the implementation verifies (B) automatically, and reports on any critical pairs, so if there are none then (A).(II) is true because the rewrite system is orthogonal. It also verifies (A).(I), however for the verification to be correct it assumes that all prefixes of the theory satisfy confluence and subject reduction.

We refer to [1] for more details, though unfortunately this reference is at the moment not completely up to date.


### Typechecking terms

After an underlying theory is specified, we can start typechecking terms inside it by declaring top-level definitions. For instance, supposing that the underlying theory contains Π types and a Tarski-style universe, we can define the polymorphic identity function at U with the following declaration.
```
let idU : Tm(Π(U, a. Π(El(a), _. El(a)))) := λ(a. λ(x. x))
```
In order to check this definition, the typechecker first verifies that the given sort is well-typed and then checks the body of the definition against it. If typechecking succeeds, then the definition becomes available to be used in other terms defined later.

As discussed in [1], not all well-typed terms can be directly written. Whenever a destructor meets a constructor, the user needs to add a *sort ascription*. This typically happens when writing redices:
```
let redex : Tm(ℕ) := ﹫(λ(x. x) :: Tm(Π(ℕ, _. ℕ)), 0)
```

One can also use local let expressions in order to make writing long terms easier:
```
let redex' : Tm(ℕ) :=
    let ty : Ty := Π(ℕ, _. ℕ) in
    ﹫(λ(x. x) :: Tm(ty), 0)
```


### Evaluating terms and checking for equality

We also provide the commands `evaluate` for evaluating terms to normal form, and `assert` for asserting that two terms are definitionally equal. For instance, assuming we have added natural numbers to the theory and defined factorial, we can use them to compute the factorial of 3 and check that it is equal to 6.
```
let fact3 : Tm(ℕ) := ﹫(fact, S(S(S(0))))
evaluate fact3

let 6 : Tm(ℕ) := S(S(S(S(S(S(0))))))
assert fact3 = 6
```

Note that these commands do not check that the given terms are well-typed before evaluating them, which can thus lead the evaluation to loop.


## Provided examples

We provide the following examples of theories in the directory `examples/`:

- `mltt.bitts` : Martin-Lof Type Theory with a Tarski-style universe, Π and Σ types, equality, lists, vectors, and the unit, empty and W types. We also give some examples of terms we can write in this theory, such as the (type-theoretic) "axiom of choice", an alternative definition of natural numbers in terms of W types, and basic functions involving natural numbers and lists.

- `hol.bitts` : Higher-Order Logic (also known as Simple Type Theory) with implication and universal quantification. We give some example of terms we can write in the theory, including an impredicative definition of conjunction along with its derived introduction and elimination rules.

- `mltt-tarski.bitts` and `mltt-coquand.bitts` and `mltt-russell.bitts` : Martin-Lof Type Theory with an hierarchy of cumulative Tarski-, Coquand- and Russell- style universes and universe polymorphism, with Π types and natural numbers. As an example of term we can write in this theory, we give the universe-polymorphic identity function.


- `ott.bitts` and `ott-2.bitts` : Two variants of McBride & Altenkirch's Observational Type Theory, with an heterogeneous equality and a Tarski-style universe, or with an homogeneous equality and a type-in-type Coquand-style universe. As an example, we given the definition of natural numbers in terms of W-types and derive its eliminator.

- `exceptional.bitts` : A variant of Pédrot & Tabarau's Exceptional Type Theory.

- `exceptional-multiverse.bitts` : A theory combining a pure type theory with an exceptional one, inspired by Maillard et al's Multiverse Type Theory (MuTT).

- `lambda-mu.bitts` : A variant of the λμ-caculus, an extension of the λ-calculus with control operators and which captures classical logic. As an example, we give a proof of Pierce's law.

- `big-numbers.bitts` : Excerpt of `mltt.bitts` used to test the performance of the evaluator, computes factorial of 8 in around half a second in the tested machine.

## Implementation

The core of the implementation is composed of the files `term.ml`, `value.ml`, `eval.ml` and `typing.ml`.

The implementation of rewriting uses a form of untyped NbE with de Bruijn indices for terms and levels for values, which avoids any need to implement functions for shifting indices and for substitution. It is inspired by the following works.

- https://github.com/jozefg/nbe-for-mltt/blob/master/src/lib/nbe.ml
- https://github.com/AndrasKovacs/elaboration-zoo
- https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Colloquia/Sterling/tutorial/lib/Eval.ml
- A simple type-theoretic language: Mini-TT

## References



[1] [Generic bidirectional typing for dependent type theories. Thiago Felicissimo.](https://arxiv.org/abs/2307.08523) (WARNING: This reference is for now not completely up to date with the implementation)

[2] [Computability Beyond Church-Turing via Choice Sequences. Mark Bickford, Liron Cohen, Robert L. Constable, Vincent Rahli](https://dl.acm.org/doi/10.1145/3209108.3209200).
