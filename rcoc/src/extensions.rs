use crate::ast::*;

/// Translates A->B
/// into ∀x:A.B
///
/// Applied when parsing `... -> ...`
///
pub fn translate_implication(a: Expression, b: Expression) -> Expression {
    let new_span = (a.get_span().0, b.get_span().1);
    Expression::Forall {
        binding: {
            let binding_span = a.get_span();
            Binding {
                identifier: get_tmp_identifier(),
                type_expression: Box::new(a),
                // the span of x:A is just that of A
                span: binding_span,
            }
        },
        value_expression: Box::new(b),
        span: new_span,
    }
}

/// Translates A∧B
/// into ∀x:Prop.∀y:(∀z:A.∀w:B.x).x
///
/// Applied when parsing `... /\ ... `
///
pub fn translate_conjunction(a: Expression, b: Expression) -> Expression {
    let a_span = a.get_span();
    let b_span = b.get_span();
    let new_span = (a_span.0, b_span.1);
    let x = get_tmp_identifier();
    let y = get_tmp_identifier();
    let z = get_tmp_identifier();
    let w = get_tmp_identifier();
    Expression::Forall {
        binding: {
            Binding {
                identifier: x.clone(),
                type_expression: Box::new(Expression::Identifier("Prop".to_string(), (0, 0))),
                span: (0, 0),
            }
        },
        value_expression: Box::new(Expression::Forall {
            binding: {
                Binding {
                    identifier: y,
                    type_expression: Box::new(Expression::Forall {
                        binding: {
                            Binding {
                                identifier: z,
                                type_expression: Box::new(a),
                                span: a_span,
                            }
                        },
                        value_expression: Box::new(Expression::Forall {
                            binding: {
                                Binding {
                                    identifier: w,
                                    type_expression: Box::new(b),
                                    span: b_span,
                                }
                            },
                            value_expression: Box::new(Expression::Identifier(x.clone(), (0, 0))),
                            span: new_span,
                        }),
                        span: new_span,
                    }),
                    span: new_span,
                }
            },
            value_expression: Box::new(Expression::Identifier(x, (0, 0))),
            span: new_span,
        }),
        span: new_span,
    }
}

/// Translates ∃x:A.B
/// into ∀y:Prop.∀z:(∀x:A.(∀w:B.y)).y
///
/// Applied when parsing `exists(...) ...`
///
pub fn translate_exists(a: Binding, b: Expression) -> Expression {
    let b_span = b.get_span();
    let new_span = (a.span.0, b_span.1);
    let y = get_tmp_identifier();
    let z = get_tmp_identifier();
    let w = get_tmp_identifier();
    Expression::Forall {
        binding: Binding {
            identifier: y.clone(),
            type_expression: Box::new(Expression::Identifier("Prop".to_string(), (0, 0))),
            span: (0, 0),
        },
        value_expression: Box::new(Expression::Forall {
            binding: Binding {
                identifier: z,
                type_expression: Box::new(Expression::Forall {
                    binding: Binding {
                        identifier: a.identifier,
                        type_expression: Box::new(*a.type_expression),
                        span: a.span,
                    },
                    value_expression: Box::new(Expression::Forall {
                        binding: Binding {
                            identifier: w,
                            type_expression: Box::new(b),
                            span: b_span,
                        },
                        value_expression: Box::new(Expression::Identifier(y.clone(), (0, 0))),
                        span: b_span,
                    }),
                    span: new_span,
                }),
                span: new_span,
            },
            value_expression: Box::new(Expression::Identifier(y, (0, 0))),
            span: new_span,
        }),
        span: new_span,
    }
}
