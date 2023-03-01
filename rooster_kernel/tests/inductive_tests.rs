mod common;

#[test]
fn nat() {
    common::execute(&[("nat", "Set", "𝐘self:Set.∀T:? Set.∀_:T.∀_:∀_:self.T.T")]);
}

#[test]
fn nat_constructors() {
    common::execute(&[
        ("nat", "Set", "𝐘self:Set.∀T:? Set.∀_:T.∀_:∀_:self.T.T"),
        ("O", "nat", "λT:? nat.λa:T.λb:∀_:nat.T.a"),
        ("S", "∀_:nat.nat", "λx:nat.λT:? nat.λa:T.λb:∀_:nat.T.b x"),
    ]);
}

#[test]
fn add() {
    common::execute(&[
        ("nat", "Set", "𝐘self:Set.∀T:? Set.∀_:T.∀_:∀_:self.T.T"),
        ("O", "nat", "λT:? nat.λa:T.λb:∀_:nat.T.a"),
        ("S", "∀_:nat.nat", "λx:nat.λT:? nat.λa:T.λb:∀_:nat.T.b x"),
        (
            "add",
            "∀_:nat.∀_:nat.nat",
            "𝐘self:(∀_:nat.∀_:nat.nat).λn:nat.λm:nat.n (nat) m (λp:(nat).S (self p m))",
        ),
    ]);
}

#[test]
fn nat_induction() {
    common::execute(&[
        ("nat", "Set", "𝐘self:Set.∀T:? Set.∀_:T.∀_:∀_:self.T.T"),
        ("O", "nat", "λT:? nat.λa:T.λb:∀_:nat.T.a"),
        ("S", "∀_:nat.nat", "λx:nat.λT:? nat.λa:T.λb:∀_:nat.T.b x"),
        (
            "nat_induction",
            "∀P:∀_:nat.Prop.∀_:P O.∀_:∀n:nat.∀_:P n.P (S n).∀n:nat.P n",
            "𝐘self:∀P:∀_:nat.Prop.∀_:P O.∀_:∀n:nat.∀_:P n.P (S n).∀n:nat.P n.λP:∀_:nat.Prop.λpO:P O.λh:∀n:nat.∀_:P n.P (S n).λn:nat.n (P n) pO (λp:nat.h p (self P pO h p))",
        ),
    ]);
}
