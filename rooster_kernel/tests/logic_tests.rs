mod common;

#[test]
fn implication_is_reflexive() {
    common::execute(&[(
        "implication_is_reflexive",
        "∀T:Prop.∀_:T.T",
        "λT:Prop.λx:T.x",
    )]);
}
