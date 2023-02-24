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
    if input.len() >= 1 && input[0] == ' ' {
        let (next_term, rest_of_input) = parse_term(&input[1..]);
        let mut function_term = previous_term;
        let mut parameter_term = next_term.clone();
        if let Term::Application {
            function_term: inner_function_term,
            parameter_term: inner_parameter_term,
            debug_context: _,
        } = next_term
        {
            function_term = Term::Application {
                function_term: Box::new(function_term),
                parameter_term: Box::new(*inner_function_term),
                debug_context: TermDebugContext::Ignore,
            };
            parameter_term = *inner_parameter_term;
        }
        (
            Term::Application {
                function_term: Box::new(function_term),
                parameter_term: Box::new(parameter_term),
                debug_context: TermDebugContext::Ignore,
            },
            rest_of_input,
        )
    } else {
        (previous_term, input)
    }
}

fn parse_term(input: &[char]) -> (Term, &[char]) {
    match input[0] {
        'λ' | '∀' | '𝐘' => {
            let (binding_identifier, input2) = parse_identifier(&input[1..]);
            assert!(input2[0] == ':');
            let (binding_type, input3) = parse_term(&input2[1..]);
            assert!(input3[0] == '.');
            let (value_term, rest_of_input) = parse_term(&input3[1..]);
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
        '(' => {
            let (inner_term, input2) = parse_term(&input[1..]);
            assert!(input2[0] == ')');
            let mut rest_of_input = &input2[1..];
            parse_application(rest_of_input, inner_term)
        }
        ch => {
            assert!(ch == '_' || ch.is_alphanumeric());
            let (identifier_name, rest_of_input) = parse_identifier(input);
            let identifier_term = Term::Identifier(identifier_name, TermDebugContext::Ignore);
            parse_application(rest_of_input, identifier_term)
        }
    }
}

pub fn execute(code: &[(&str, &str, &str)]) {
    let mut state = State::new();
    for statement in code {
        match state.try_define(
            &statement.0.to_string(),
            parse_term(&statement.1.chars().collect::<Vec<_>>()).0,
            parse_term(&statement.2.chars().collect::<Vec<_>>()).0,
        ) {
            Ok(_) => (),
            Err(_) => panic!(),
        }
    }
}
