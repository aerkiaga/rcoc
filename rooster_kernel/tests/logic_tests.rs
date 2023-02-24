mod common;

#[test]
fn implication_is_reflexive() {
    common::execute(&[(
        "implication_is_reflexive",
        "∀T:Prop.∀_:T.T",
        "λT:Prop.λx:T.x",
    )]);
}

#[test]
fn implication_works() {
    common::execute(&[(
        "implication_works",
        "∀T:Prop.∀P:Prop.∀_:T.∀_:∀_:T.P.P",
        "λT:Prop.λP:Prop.λx:T.λy:∀_:T.P.y x",
    )]);
}

#[test]
fn consequent_always_exists() {
    common::execute(&[(
        "consequent_always_exists",
        "∀T:Prop.∀Q:Prop.∀_:(∀P:Prop.∀_:(∀_:T.P).Q).Q",
        "λT:Prop.λQ:Prop.λh:∀P:Prop.∀_:(∀_:T.P).Q.h T λx:T.x",
    )]);
}

#[test]
fn conjunction_implies_operand() {
    common::execute(&[(
        "conjunction_implies_operand",
        "∀A:Prop.∀B:Prop.∀_:∀P:Prop.∀_:∀_:A.∀_:B.P.P.A",
        "λA:Prop.λB:Prop.λh:∀P:Prop.∀_:∀_:A.∀_:B.P.P.h A λx:A.λy:B.x",
    )]);
}

#[test]
fn disjunction_is_commutative() {
    common::execute(&[(
        "disjunction_is_commutative",
        "∀A:Prop.∀B:Prop.∀_:∀P:Prop.∀_:∀_:A.P.∀_:∀_:B.P.P.∀x:Prop.∀_:∀_:B.x.∀_:∀_:A.x.x",
        "λA:Prop.λB:Prop.λh:∀P:Prop.∀_:∀_:A.P.∀_:∀_:B.P.P.h (∀x:Prop.∀_:∀_:B.x.∀_:∀_:A.x.x) (λa:A.λQ:Prop.λ_:∀_:B.Q.λaq:∀_:A.Q.aq a) (λb:B.λQ:Prop.λbq:∀_:B.Q.λ_:∀_:A.Q.bq b)",
    )]);
}

#[test]
fn proposition_and_its_negation_is_false() {
    common::execute(&[(
        "proposition_and_its_negation_is_false",
        "∀A:Prop.∀_:(∀Q:Prop.∀_:(∀_:A.∀_:(∀_:A.∀x:Prop.x).Q).Q).∀x:Prop.x",
        "λA:Prop.λh:∀Q:Prop.∀_:(∀_:A.∀_:(∀_:A.∀x:Prop.x).Q).Q.h (∀x:Prop.x) λa:A.λnot_a:∀_:A.∀x:Prop.x.not_a a",
    )]);
}

#[test]
fn disjunction_of_implication_is_commutative() {
    common::execute(&[(
        "disjunction_is_commutative",
        "∀A:Prop.∀B:Prop.∀_:∀P:Prop.∀_:∀_:A.P.∀_:∀_:B.P.P.∀S:Prop.∀_:∀_:B.S.∀_:∀_:A.S.S",
        "λA:Prop.λB:Prop.λh:∀P:Prop.∀_:∀_:A.P.∀_:∀_:B.P.P.h (∀x:Prop.∀_:∀_:B.x.∀_:∀_:A.x.x) (λa:A.λQ:Prop.λ_:∀_:B.Q.λaq:∀_:A.Q.aq a) (λb:B.λQ:Prop.λbq:∀_:B.Q.λ_:∀_:A.Q.bq b)",
    ), (
        "disjunction_of_implication_is_commutative",
        "∀A:Prop.∀B:Prop.∀_:(∀P:Prop.∀_:(∀_:(∀_:A.B).P).∀_:(∀_:(∀_:B.A).P).P).∀Q:Prop.∀_:(∀_:(∀_:B.A).Q).∀_:(∀_:(∀_:A.B).Q).Q",
        "λA:Prop.λB:Prop.disjunction_is_commutative (∀_:A.B) (∀_:B.A)",
    )]);
}

#[test]
fn equivalence_implies_implication() {
    common::execute(&[
        (
            "conjunction_implies_operand",
            "∀A:Prop.∀B:Prop.∀_:∀P:Prop.∀_:∀_:A.∀_:B.P.P.A",
            "λA:Prop.λB:Prop.λh:∀P:Prop.∀_:∀_:A.∀_:B.P.P.h A λx:A.λy:B.x",
        ),
        (
            "equivalence_implies_implication",
            "∀A:Prop.∀B:Prop.∀_:(∀P:Prop.∀_:(∀_:(∀_:A.B).∀_:(∀_:B.A).P).P).∀_:A.B",
            "λA:Prop.λB:Prop.conjunction_implies_operand (∀_:A.B) (∀_:B.A)",
        ),
    ]);
}
