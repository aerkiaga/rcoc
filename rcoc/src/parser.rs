use crate::ast::*;
use chumsky::prelude::*;

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
                .or(one_of(
                    "_'′″‴‵‶‷⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁱⁿ₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₒₓₔₕₖₗₘₙₚₛₜᵢᵣᵤᵥᵦᵧᵨᵩᵪ",
                ))
                .repeated()
                .collect::<String>(),
        )
        .map(|t| {
            let mut s = String::from(t.0);
            s.push_str(&t.1);
            s
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
                            identifier: x.clone(),
                            type_expression: t.1.clone(),
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
            let identifier_expression = identifier
                .clone()
                .padded_by(token_separator.clone())
                .map(|s| Expression::Identifier(s));
            let lambda_expression = binding_list
                .clone()
                .padded_by(just('|').padded_by(token_separator.clone()))
                .then(nested_expression.clone())
                .map(|t| Expression::Lambda {
                    binding_list: t.0,
                    value_expression: Box::new(t.1),
                });
            let forall_expression = just("@(")
                .ignored()
                .padded_by(token_separator.clone())
                .then(binding_list.clone())
                .then_ignore(just(')').padded_by(token_separator.clone()))
                .then(nested_expression.clone())
                .map(|t| Expression::Forall {
                    binding_list: t.0 .1,
                    value_expression: Box::new(t.1),
                });
            let brace_expression = nested_expression.clone().delimited_by(
                just('{').ignored().padded_by(token_separator.clone()),
                just('}').ignored().padded_by(token_separator.clone()),
            );
            let nonlrecursive_expression = choice((
                identifier_expression,
                lambda_expression,
                forall_expression,
                brace_expression,
            ));
            let application_expression = nonlrecursive_expression
                .clone()
                .then(
                    parameter_list
                        .delimited_by(
                            just('(').ignored().padded_by(token_separator.clone()),
                            just(')').ignored().padded_by(token_separator.clone()),
                        )
                        .separated_by(token_separator.clone())
                        .at_least(1)
                        .flatten(),
                )
                .map(|t| Expression::Application {
                    function_expression: Box::new(t.0),
                    parameter_expressions: t.1,
                });
            choice((application_expression, nonlrecursive_expression))
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
        .map(|t| Statement::Definition {
            identifier: t.0 .0 .1,
            type_expression: t.0 .1,
            value_expression: t.1,
        });
    let statement = choice((let_assignment, empty().to(Statement::Empty)));
    let statement_list = statement
        .separated_by(just(';').padded_by(token_separator.clone()))
        .map(|x| {
            x.iter()
                .filter(|p| {
                    if let Statement::Empty = p {
                        false
                    } else {
                        true
                    }
                })
                .map(|p| p.clone())
                .collect::<Vec<_>>()
        });
    statement_list.then_ignore(end())
}

pub fn parse(input: &str) -> Result<Vec<Statement>, Vec<Simple<char>>> {
    let result = parser().parse_recovery(input);
    match result.0 {
        Some(x) => Ok(x),
        None => Err(result.1),
    }
}
