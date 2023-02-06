# RCoC
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
cargo run -- test.rcoc
```

Which will output:

```
proof_a = λT:Prop.λx:T.x
    :∀T:Prop.T→T
proof_b = λT:Prop.λP:Prop.λx:T.λy:T→P.y x
    :∀T:Prop.∀P:Prop.T→(T→P)→P
proof_c = λT:Prop.λQ:Prop.λh:∀P:Prop.(T→P)→Q.h T λx:T.x
    :∀T:Prop.∀$23:Prop.(∀P:Prop.(T→P)→$23)→$23
proof_d = λA:Prop.λB:Prop.λh:∀P:Prop.(A→B→P)→P.h A λx:A.λy:B.x
    :∀A:Prop.∀B:Prop.(∀$55:Prop.(A→B→$55)→$55)→A
proof_e = λA:Prop.λB:Prop.λh:∀P:Prop.(A→P)→(B→P)→P.h ∀$233:Prop.(B→$233)→(A→$233)→$233 λa:A.λQ:Prop.λ_:B→Q.λaq:A→Q.aq a λb:B.λQ:Prop.λbq:B→Q.λ_:A→Q.bq b
    :∀A:Prop.∀B:Prop.(∀$111:Prop.(A→$111)→(B→$111)→$111)→∀$116:Prop.(B→$116)→(A→$116)→$116
```

## Features
Core language:
 - [x] Calculus of Constructions

Syntax extensions:
 - [x] `->` operator
 - [x] `/\` operator
 - [x] `\/` operator
 - [x] `exists()` operator

## Acknowledgements

RCoC uses the amazing [chumsky](https://github.com/zesterer/chumsky)
and [ariadne](https://github.com/zesterer/ariadne) crates by @zesterer
to parse the input and produce meaningful error diagnostics.

The Calculus of Constructions was devised by Thierry Coquand,
and serves as the basis for [Coq](https://github.com/coq/coq)
and other proof assistants.
