# Rooster
![Kernel size](https://img.shields.io/badge/kernel-703%20SLOC-blue)

An automated proof checker based on the Calculus of Constructions.

Written in Rust, proofs also employ a Rust-like syntax.
At the moment, it doesn't have many features, but it does work.

```rust
/* A proof that, for any three statements A, B and C, *
 * if A implies B and B implies C, then A implies C */

let proof_implication_is_transitive:
    @(A, B, C: Prop) {A -> B} -> {B -> C} -> {A -> C}
=
    |A, B, C: Prop, ab: A -> B, bc: B -> C| |x: A| bc(ab(x))
;
```

## Usage
You can run the example file using the following command:

```
cargo run -- test.roo
```

Which will output:

```
implication_is_reflexive = λT:Prop.λx:T.x
    :∀T:Prop.T→T
implication_works = λT:Prop.λP:Prop.λx:T.λy:T→P.y x
    :∀T:Prop.∀P:Prop.T→(T→P)→P
consequent_always_exists = λT:Prop.λQ:Prop.λh:∀P:Prop.(T→P)→Q.h T λx:T.x
    :∀T:Prop.∀$23:Prop.(∀P:Prop.(T→P)→$23)→$23
conjunction_implies_operand = λA:Prop.λB:Prop.λh:∀P:Prop.(A→B→P)→P.h A λx:A.λy:B.x
    :∀A:Prop.∀B:Prop.(∀$55:Prop.(A→B→$55)→$55)→A
disjunction_is_commutative = λA:Prop.λB:Prop.λh:∀P:Prop.(A→P)→(B→P)→P.h ∀$233:Prop.(B→$233)→(A→$233)→$233 λa:A.λQ:Prop.λ_:B→Q.λaq:A→Q.aq a λb:B.λQ:Prop.λbq:B→Q.λ_:A→Q.bq b
    :∀A:Prop.∀B:Prop.(∀$111:Prop.(A→$111)→(B→$111)→$111)→∀$116:Prop.(B→$116)→(A→$116)→$116
proposition_and_its_negation_is_false = λA:Prop.λh:∀Q:Prop.(A→(A→⊥)→Q)→Q.h ⊥ λa:A.λnot_a:A→⊥.not_a a
    :∀A:Prop.(∀$276:Prop.(A→(A→⊥)→$276)→$276)→⊥
disjunction_of_implication_is_commutative = λA:Prop.λB:Prop.disjunction_is_commutative A→B B→A
    :∀A:Prop.∀B:Prop.(∀$465:Prop.((A→B)→$465)→((B→A)→$465)→$465)→∀$474:Prop.((B→A)→$474)→((A→B)→$474)→$474
equivalence_implies_implication = λA:Prop.λB:Prop.conjunction_implies_operand A→B B→A
    :∀A:Prop.∀B:Prop.(∀$494:Prop.((A→B)→(B→A)→$494)→$494)→A→B
```

## Features
Core language:
 - [x] Calculus of Constructions

Syntax extensions:
 - [x] Intuitionistic logic

| Category | Syntax elements |
| --- | --- |
| CoC terms | `A(B)` `\|x: A\| B` `@(x: A) B` `Prop` `Type(n)` `{A}` |
| CoC sentences | `let a: A = B;` |
| Intuitionistic logic | `A -> B` `False` `^A` `A /\ B` `A \/ B` `exists(x: A) B` `A <-> B` |

## Acknowledgements

RCoC uses the amazing [chumsky](https://github.com/zesterer/chumsky)
and [ariadne](https://github.com/zesterer/ariadne) crates by @zesterer
to parse the input and produce meaningful error diagnostics.

The Calculus of Constructions was devised by Thierry Coquand,
and serves as the basis for [Coq](https://github.com/coq/coq)
and other proof assistants.
