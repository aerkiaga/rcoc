use crate::ast::*;
use chumsky::prelude::*;

static mut TMP_VARIABLE_CURRENT_INDEX: Option<std::sync::Arc<std::sync::Mutex<u32>>> = None;

fn get_tmp_identifier() -> String {
    format!("${}", {
        let mut index = unsafe { TMP_VARIABLE_CURRENT_INDEX.as_ref() }
            .unwrap()
            .lock()
            .unwrap();
        *index += 1;
        *index - 1
    })
}

fn parser() -> impl Parser<char, Vec<Statement>, Error = Simple<char>> {
    let single_line_comment = just("//")
        .ignored()
        .then_ignore(take_until(text::newline()));
    let multi_line_comment = just("/*").ignored().then_ignore(take_until(just("*/")));
    let comment = single_line_comment.or(multi_line_comment);
    let token_separator = text::whitespace()
        .then_ignore(comment.separated_by(text::whitespace()).ignored())
        .then_ignore(text::whitespace());
    let identifier = filter(|c| char::is_alphabetic(*c))
        .or(just('_'))
        .then(
            filter(|c| char::is_alphabetic(*c))
                .or(just('_'))
                .repeated()
                .collect::<String>(),
        )
        .try_map(|t, sp: std::ops::Range<usize>| {
            let mut s = String::from(t.0);
            s.push_str(&t.1);
            match &*s {
                "exists" => Err(Simple::custom(sp, "'exists' is a reserved word")),
                _ => Ok((s, (sp.start(), sp.end()))),
            }
        });
    let expression = recursive(
        |nested_expression: Recursive<char, Expression, Simple<char>>| {
            let identifier_list = identifier
                .clone()
                .padded_by(token_separator.clone())
                .separated_by(just(',').ignored().padded_by(token_separator.clone()));
            let multiple_binding = identifier_list
                .then_ignore(just(':').ignored().padded_by(token_separator.clone()))
                .then(nested_expression.clone())
                .map(|t| {
                    t.0.iter()
                        .map(|x| Binding {
                            identifier: x.0.clone(),
                            type_expression: Box::new(t.1.clone()),
                            span: (x.1 .0, t.1.get_span().1),
                        })
                        .collect::<Vec<_>>()
                });
            let binding_list = multiple_binding
                .separated_by(just(',').ignored().padded_by(token_separator.clone()))
                .flatten();
            let parameter_list = nested_expression
                .clone()
                .separated_by(just(',').ignored().padded_by(token_separator.clone()))
                .at_least(1);
            let parameter_lists = parameter_list
                .delimited_by(
                    just('(').ignored().padded_by(token_separator.clone()),
                    just(')').ignored().padded_by(token_separator.clone()),
                )
                .separated_by(token_separator.clone())
                .at_least(1)
                .flatten();
            let identifier_expression = identifier
                .clone()
                .padded_by(token_separator.clone())
                .map(|t| Expression::Identifier(t.0, t.1));
            let lambda_expression = binding_list
                .clone()
                .padded_by(just('|').padded_by(token_separator.clone()))
                .then(nested_expression.clone())
                .foldr(|t, x| {
                    let new_span = (t.span.0, x.get_span().1);
                    Expression::Lambda {
                        binding: t,
                        value_expression: Box::new(x),
                        span: new_span,
                    }
                });
            let forall_expression = just("@(")
                .ignored()
                .padded_by(token_separator.clone())
                .then(binding_list.clone())
                .map(|t| t.1)
                .then_ignore(just(')').padded_by(token_separator.clone()))
                .then(nested_expression.clone())
                .foldr(|t, x| {
                    let new_span = (t.span.0, x.get_span().1);
                    Expression::Forall {
                        binding: t,
                        value_expression: Box::new(x),
                        span: new_span,
                    }
                });
            // alias: ∃x:A.B := ∀y:Prop.∀z:(∀x:A.(∀w:B.y)).y
            let exists_expression = just("exists(")
                .ignored()
                .padded_by(token_separator.clone())
                .then(binding_list.clone())
                .map(|t| t.1)
                .then_ignore(just(')').padded_by(token_separator.clone()))
                .then(nested_expression.clone())
                .foldr(|t, x| {
                    let b_span = x.get_span();
                    let new_span = (t.span.0, b_span.1);
                    let y = get_tmp_identifier();
                    let z = get_tmp_identifier();
                    let w = get_tmp_identifier();
                    Expression::Forall {
                        binding: Binding {
                            identifier: y.clone(),
                            type_expression: Box::new(Expression::Identifier(
                                "Prop".to_string(),
                                (0, 0),
                            )),
                            span: (0, 0),
                        },
                        value_expression: Box::new(Expression::Forall {
                            binding: Binding {
                                identifier: z,
                                type_expression: Box::new(Expression::Forall {
                                    binding: Binding {
                                        identifier: t.identifier,
                                        type_expression: Box::new(*t.type_expression),
                                        span: t.span,
                                    },
                                    value_expression: Box::new(Expression::Forall {
                                        binding: Binding {
                                            identifier: w,
                                            type_expression: Box::new(x),
                                            span: b_span,
                                        },
                                        value_expression: Box::new(Expression::Identifier(
                                            y.clone(),
                                            (0, 0),
                                        )),
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
                });
            let brace_expression = nested_expression.clone().delimited_by(
                just('{').ignored().padded_by(token_separator.clone()),
                just('}').ignored().padded_by(token_separator.clone()),
            );
            let nonlrecursive_expression = choice((
                brace_expression,
                lambda_expression,
                forall_expression,
                exists_expression,
                identifier_expression,
            ));
            let application_expression = nonlrecursive_expression
                .clone()
                .then(parameter_lists)
                .foldl(|x, t| {
                    let new_span = (x.get_span().0, t.get_span().1);
                    Expression::Application {
                        function_expression: Box::new(x),
                        parameter_expression: Box::new(t),
                        span: new_span,
                    }
                })
                .or(nonlrecursive_expression);
            let binary_operator1 = choice((just("->"),)).padded_by(token_separator.clone());
            let binary_expression1 = application_expression
                .clone()
                .then(binary_operator1)
                .repeated()
                .then(application_expression)
                .foldr(|t, x| {
                    let new_span = (t.0.get_span().0, x.get_span().1);
                    match t.1 {
                        // alias: A->B := ∀x:A.B
                        "->" => Expression::Forall {
                            binding: {
                                let new_span = t.0.get_span();
                                Binding {
                                    identifier: get_tmp_identifier(),
                                    type_expression: Box::new(t.0),
                                    // the span of x:A is just that of A
                                    span: new_span,
                                }
                            },
                            value_expression: Box::new(x),
                            span: new_span,
                        },
                        _ => panic!(),
                    }
                });
            binary_expression1
        },
    );
    let let_assignment = just("let")
        .padded_by(token_separator.clone())
        .ignored()
        .then(identifier.clone().padded_by(token_separator.clone()))
        .then_ignore(just(":").padded_by(token_separator.clone()))
        .then(expression.clone().padded_by(token_separator.clone()))
        .then_ignore(just("=").padded_by(token_separator.clone()))
        .then(expression.clone().padded_by(token_separator.clone()))
        .map_with_span(|t, sp| Statement::Definition {
            identifier: t.0 .0 .1 .0,
            type_expression: t.0 .1,
            value_expression: t.1,
            span: (sp.start(), sp.end()),
        });
    let statement = choice((let_assignment,));
    let statement_list = statement
        .then_ignore(just(';').padded_by(token_separator.clone()))
        .repeated();
    statement_list.then_ignore(end())
}

pub fn parse(input: &str) -> Result<Vec<Statement>, Vec<Simple<char>>> {
    unsafe {
        TMP_VARIABLE_CURRENT_INDEX = Some(std::sync::Arc::new(std::sync::Mutex::new(0)));
    }
    let result = parser().parse_recovery(input);
    match result.0 {
        Some(x) => Ok(x),
        None => Err(result.1),
    }
}
