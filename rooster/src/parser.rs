use crate::ast::*;
use crate::extensions;
use chumsky::prelude::*;

fn parser() -> impl Parser<char, Vec<Statement>, Error = Simple<char>> {
    let single_line_comment = just("//")
        .ignored()
        .then_ignore(take_until(text::newline()));
    let multi_line_comment = just("/*").ignored().then_ignore(take_until(just("*/")));
    let comment = single_line_comment.or(multi_line_comment);
    let token_separator = text::whitespace()
        .then_ignore(comment.separated_by(text::whitespace()).ignored())
        .then_ignore(text::whitespace())
        .boxed();
    let identifier = filter(|c| char::is_alphabetic(*c))
        .or(just('_'))
        .then(
            filter(|c| char::is_alphabetic(*c))
                .or(just('_'))
                .repeated()
                .collect::<String>(),
        )
        .map_with_span(|t, sp: std::ops::Range<usize>| {
            let mut s = String::from(t.0);
            s.push_str(&t.1);
            (s, (sp.start(), sp.end()))
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
            let special_identifier = choice((just("False").padded_by(token_separator.clone()),));
            let identifier_expression = special_identifier
                .map_with_span(|s, sp| match s {
                    // alias: ⊥ := ∀x:Prop.x
                    "False" => extensions::translate_false((sp.start(), sp.end())),
                    _ => panic!(),
                })
                .or(identifier
                    .clone()
                    .padded_by(token_separator.clone())
                    .map(|t| Expression::Identifier(t.0, t.1)));
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
                .foldr(|t, x| extensions::translate_exists(t, x));
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
            let unary_operator1 = choice((just("^"),)).padded_by(token_separator.clone());
            let unary_expression1 = unary_operator1
                .repeated()
                .then(application_expression.clone())
                .foldr(|s, x| match s {
                    // alias: ¬A := ∀x:A.∀y:Prop.y
                    // disappointingly the ¬ symbol isn't on many keyboards;
                    // ^ will do the job instead for intuitionistic negation
                    "^" => extensions::translate_negation(x),
                    _ => panic!(),
                });
            let binary_operator1 = choice((just("/\\"),)).padded_by(token_separator.clone());
            let binary_expression1 = unary_expression1
                .clone()
                .then(binary_operator1.then(unary_expression1).repeated())
                .map(|t| {
                    // we parse as if left folding as it's much faster,
                    // then translate to right folding
                    if t.1.len() == 0 {
                        return (vec![], t.0);
                    }
                    let mut outv = vec![(t.0, t.1[0].0)];
                    for n in 0..(t.1.len() - 1) {
                        outv.push((t.1[n].1.clone(), t.1[n + 1].0));
                    }
                    (outv, t.1[t.1.len() - 1].1.clone())
                })
                .foldr(|t, x| match t.1 {
                    // alias: A∧B := ∀x:Prop.∀y:∀z:A.∀w:B.x.x
                    "/\\" => extensions::translate_conjunction(t.0, x),
                    _ => panic!(),
                });
            let binary_operator2 = choice((just("\\/"),)).padded_by(token_separator.clone());
            let binary_expression2 = binary_expression1
                .clone()
                .then(binary_operator2.then(binary_expression1).repeated())
                .map(|t| {
                    // we parse as if left folding as it's much faster,
                    // then translate to right folding
                    if t.1.len() == 0 {
                        return (vec![], t.0);
                    }
                    let mut outv = vec![(t.0, t.1[0].0)];
                    for n in 0..(t.1.len() - 1) {
                        outv.push((t.1[n].1.clone(), t.1[n + 1].0));
                    }
                    (outv, t.1[t.1.len() - 1].1.clone())
                })
                .foldr(|t, x| match t.1 {
                    // alias: A∨B := ∀x:Prop.∀y:(∀z:A.x).∀w:(∀v:B.x).x
                    "\\/" => extensions::translate_disjunction(t.0, x),
                    _ => panic!(),
                });
            let binary_operator3 = choice((just("<->"),)).padded_by(token_separator.clone());
            let binary_expression3 = binary_expression2
                .clone()
                .then(binary_operator3.then(binary_expression2).repeated())
                .map(|t| {
                    // we parse as if left folding as it's much faster,
                    // then translate to right folding
                    if t.1.len() == 0 {
                        return (vec![], t.0);
                    }
                    let mut outv = vec![(t.0, t.1[0].0)];
                    for n in 0..(t.1.len() - 1) {
                        outv.push((t.1[n].1.clone(), t.1[n + 1].0));
                    }
                    (outv, t.1[t.1.len() - 1].1.clone())
                })
                .foldr(|t, x| match t.1 {
                    // alias: A↔B := (A→B)∧(B→A)
                    "<->" => extensions::translate_equivalence(t.0, x),
                    _ => panic!(),
                });
            let binary_operator4 = choice((just("->"),)).padded_by(token_separator.clone());
            let binary_expression4 = binary_expression3
                .clone()
                .then(binary_operator4.then(binary_expression3).repeated())
                .map(|t| {
                    // we parse as if left folding as it's much faster,
                    // then translate to right folding
                    if t.1.len() == 0 {
                        return (vec![], t.0);
                    }
                    let mut outv = vec![(t.0, t.1[0].0)];
                    for n in 0..(t.1.len() - 1) {
                        outv.push((t.1[n].1.clone(), t.1[n + 1].0));
                    }
                    (outv, t.1[t.1.len() - 1].1.clone())
                })
                .foldr(|t, x| match t.1 {
                    // alias: A→B := ∀x:A.B
                    "->" => extensions::translate_implication(t.0, x),
                    _ => panic!(),
                });
            binary_expression4
        },
    )
    .boxed();
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
    statement_list.then_ignore(end()).boxed()
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
