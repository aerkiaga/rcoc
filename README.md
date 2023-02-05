# RCoC
An automated proof checker based on the Calculus of Constructions.

Written in Rust, proofs also employ a Rust-like syntax.
At the moment, it doesn't have many features, but it does work.

```rust
/* A proof that, for any statement T, *
 * if T is true then T is true.       */

let proof_that_T_implies_T:
    @(T: Prop, x: T) T
=
    |T: Prop, x: T| {|y: T| y}(x)
;
```

You can run the example file using the following command:

```
cargo run -- test.rcoc
```

Which will output:

```
a = λT:Prop.λx:T.x
    :∀T:Prop.∀x:T.T
```
