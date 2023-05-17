use rooster_kernel::*;

fn parse_identifier(input: &[char]) -> (String, &[char]) {
    if input.len() < 1 {
        return ("".to_string(), input);
    }
    if input[0] == '_' || input[0].is_alphanumeric() {
        let mut output = String::from(input[0]);
        let (rest_of_identifier, rest_of_input) = parse_identifier(&input[1..]);
        output.push_str(&rest_of_identifier);
        (output, rest_of_input)
    } else {
        ("".to_string(), input)
    }
}

fn parse_application(input: &[char], previous_term: Term) -> (Term, &[char]) {
    let mut current_term = previous_term.clone();
    let mut current_input = input;
    loop {
        if current_input.len() >= 1 && current_input[0] == ' ' {
            let (next_term, rest_of_input) = parse_term(&current_input[1..], false);
            current_input = rest_of_input;
            current_term = Term::Application {
                function_term: Box::new(current_term),
                parameter_term: Box::new(next_term),
                debug_context: TermDebugContext::Ignore,
            };
        } else {
            break;
        }
    }
    (current_term, current_input)
}

fn parse_term(input: &[char], try_application: bool) -> (Term, &[char]) {
    match input[0] {
        'λ' | '∀' | '𝐘' => {
            let (binding_identifier, input2) = parse_identifier(&input[1..]);
            assert!(input2[0] == ':');
            let (binding_type, input3) = parse_term(&input2[1..], true);
            assert!(input3[0] == '.');
            let (value_term, rest_of_input) = parse_term(&input3[1..], true);
            (
                match input[0] {
                    'λ' => Term::Lambda {
                        binding_identifier: binding_identifier,
                        binding_type: Box::new(binding_type),
                        value_term: Box::new(value_term),
                        debug_context: TermDebugContext::Ignore,
                    },
                    '∀' => Term::Forall {
                        binding_identifier: binding_identifier,
                        binding_type: Box::new(binding_type),
                        value_term: Box::new(value_term),
                        debug_context: TermDebugContext::Ignore,
                    },
                    '𝐘' => Term::FixedPoint {
                        binding_identifier: binding_identifier,
                        binding_type: Box::new(binding_type),
                        value_term: Box::new(value_term),
                        debug_context: TermDebugContext::Ignore,
                    },
                    _ => panic!(),
                },
                rest_of_input,
            )
        }
        '℺' => {
            let (type_term, input2) = parse_term(&input[1..], true);
            assert!(input2[0] == '.');
            let (value_term, rest_of_input) = parse_term(&input2[1..], true);
            (
                Term::Constructor {
                    type_term: Box::new(type_term),
                    value_term: Box::new(value_term),
                    debug_context: TermDebugContext::Ignore,
                },
                rest_of_input,
            )
        }
        '(' => {
            let (inner_term, input2) = parse_term(&input[1..], true);
            assert!(input2[0] == ')');
            let rest_of_input = &input2[1..];
            if try_application {
                parse_application(rest_of_input, inner_term)
            } else {
                (inner_term, rest_of_input)
            }
        }
        '?' => {
            let identifier_term = Term::Identifier("?".to_string(), TermDebugContext::Ignore);
            if try_application {
                parse_application(&input[1..], identifier_term)
            } else {
                (identifier_term, &input[1..])
            }
        }
        ch => {
            assert!(ch == '_' || ch.is_alphanumeric());
            let (identifier_name, rest_of_input) = parse_identifier(input);
            let identifier_term = Term::Identifier(identifier_name, TermDebugContext::Ignore);
            if try_application {
                parse_application(rest_of_input, identifier_term)
            } else {
                (identifier_term, rest_of_input)
            }
        }
    }
}

pub fn execute(code: &[(&str, &str, &str)]) {
    let mut state = State::new();
    for statement in code {
        match state.try_define(
            &statement.0.to_string(),
            parse_term(&statement.1.chars().collect::<Vec<_>>(), true).0,
            parse_term(&statement.2.chars().collect::<Vec<_>>(), true).0,
        ) {
            Ok(_) => (),
            Err(e) => panic!("{:?}", e),
        }
    }
}
