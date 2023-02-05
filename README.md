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

You can run the example file using the following command:

```
cargo run -- test.rcoc
```

Which will output:

```
proof_a = λT:Prop.λx:T.x
    :∀T:Prop.∀x:T.T
proof_b = λT:Prop.λP:Prop.λx:T.λy:∀$7:T.P.y x
    :∀T:Prop.∀P:Prop.∀$5:T.∀$4:∀$3:T.P.P
```
