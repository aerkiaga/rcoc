#![no_main]

use libfuzzer_sys::fuzz_target;
use rooster_kernel::*;

fn generate_term(data: &[u8]) -> (Option<Term>, &[u8]) {
    if data.len() <= 0 {
        return (None, data);
    }
    match data[0] {
        0..=63 =>
            (Some(Term::Identifier(format!("x{}", data[0] % 4), TermDebugContext::Ignore)), &data[1..]),
        64..=127 =>
            (Some(Term::Identifier(["Prop", "Set", "Type(1)"][(data[0] % 3) as usize].to_string(), TermDebugContext::Ignore)), &data[1..]),
        128..=159 => {
            let (function_term_option, data2) = generate_term(&data[1..]);
            let (parameter_term_option, data3) = generate_term(data2);
            let function_term = match function_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            let parameter_term = match parameter_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            (Some(Term::Application{
                function_term: Box::new(function_term),
                parameter_term: Box::new(parameter_term),
                debug_context: TermDebugContext::Ignore,
            }), data3)
        },
        160..=191 => {
            let identifier = format!("x{}", data[0] % 4);
            let (type_term_option, data2) = generate_term(&data[1..]);
            let (value_term_option, data3) = generate_term(data2);
            let type_term = match type_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            let value_term = match value_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            (Some(Term::Lambda{
                binding_identifier: identifier,
                binding_type: Box::new(type_term),
                value_term: Box::new(value_term),
                debug_context: TermDebugContext::Ignore,
            }), data3)
        },
        192..=223 => {
            let identifier = format!("x{}", data[0] % 4);
            let (type_term_option, data2) = generate_term(&data[1..]);
            let (value_term_option, data3) = generate_term(data2);
            let type_term = match type_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            let value_term = match value_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            (Some(Term::Forall{
                binding_identifier: identifier,
                binding_type: Box::new(type_term),
                value_term: Box::new(value_term),
                debug_context: TermDebugContext::Ignore,
            }), data3)
        },
        224..=255 => {
            let identifier = format!("x{}", data[0] % 4);
            let (type_term_option, data2) = generate_term(&data[1..]);
            let (value_term_option, data3) = generate_term(data2);
            let type_term = match type_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            let value_term = match value_term_option {
                Some(x) => x,
                None => return (generate_term(&vec![data[0] - 128]).0, &data[data.len()..]),
            };
            (Some(Term::FixedPoint{
                binding_identifier: identifier,
                binding_type: Box::new(type_term),
                value_term: Box::new(value_term),
                debug_context: TermDebugContext::Ignore,
            }), data3)
        },
    }
}

fn generate_definition<'a, 'b>(data: &'a [u8], state: &'b State) -> Result<((Term, Term), &'a [u8]), KernelError> {
    let (value_term_option, remaining_data) = generate_term(data);
    let value_term = value_term_option.unwrap();
    let type_term = value_term.infer_type(state)?;
    return Ok(((type_term, value_term), remaining_data));
}

fuzz_target!(|data: &[u8]| {
    let mut state = State::new();
    let mut definitions = vec![];
    let mut remaining_data = data;
    let mut index = 0;
    let mut r#false = Term::Forall {
        binding_identifier: "P".to_string(),
        binding_type: Box::new(Term::Identifier("Prop".to_string(), TermDebugContext::Ignore)),
        value_term: Box::new(Term::Identifier("P".to_string(), TermDebugContext::Ignore)),
        debug_context: TermDebugContext::Ignore,
    };
    r#false.full_normalize(&state);
    loop {
        if remaining_data.len() <= 0 {
            break;
        }
        let (definition, new_remaining_data) = match generate_definition(remaining_data, &state) {
            Ok(x) => x,
            Err(_) => return,
        };
        remaining_data = new_remaining_data;
        let identifier = format!("x{}", index);
        let (definition_type, definition_value) = (definition.0.clone(), definition.1.clone());
        let mut normalized_type = definition.0.clone();
        match state.try_define(&identifier, definition.0, definition.1) {
            Ok(_) => (),
            Err(_) => return,
        };
        definitions.push((identifier, definition_type, definition_value));
        normalized_type.full_normalize(&state);
        if normalized_type == r#false {
            println!("{:?}", definitions);
            panic!("CRITICAL ERROR: INCONSISTENT LOGIC");
        }
        index += 1;
    }
});
