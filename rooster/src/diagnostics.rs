use ariadne::*;
use chumsky::error::*;
use rooster_kernel::KernelError;

pub fn emit_parser_diagnostic(error: &Simple<char>, code: &String, source_id: &String) {
    let mut color_generator = ColorGenerator::new();
    let color1 = color_generator.next();
    let error_span = error.span();
    let error_reason = error.reason();
    let error_expected = error
        .expected()
        .filter(|x| match x {
            Some(_) => true,
            None => false,
        })
        .collect::<Vec<_>>();
    let mut expected_str = String::from("Expected ");
    for n in 0..(error_expected.len() - 1) {
        expected_str.push_str(&format!(
            "{}",
            error_expected[n].unwrap().to_string().fg(Color::Green)
        ));
        if n < (error_expected.len() - 2) {
            expected_str.push_str(", ");
        }
    }
    if error_expected.len() > 1 {
        expected_str.push_str(" or ");
    }
    expected_str.push_str(&format!(
        "{}",
        error_expected[error_expected.len() - 1]
            .unwrap()
            .to_string()
            .fg(Color::Green)
    ));
    match error_reason {
        SimpleReason::Unexpected => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message("unexpected token")
                .with_label(
                    Label::new((source_id, error_span))
                        .with_message(expected_str)
                        .with_color(Color::Red),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        SimpleReason::Unclosed { span, delimiter: _ } => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message("unclosed delimiter")
                .with_label(
                    Label::new((source_id, error_span))
                        .with_message(expected_str)
                        .with_color(color1),
                )
                .with_label(
                    Label::new((source_id, span.clone()))
                        .with_message("opening delimiter here")
                        .with_color(Color::Red),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        _ => (),
    };
}

pub fn emit_kernel_diagnostic(error: &KernelError, code: &String, source_id: &String) {
    let mut color_generator = ColorGenerator::new();
    let color1 = color_generator.next();
    let color2 = color_generator.next();
    match error {
        KernelError::UndefinedIdentifier {
            identifier,
            identifier_context,
        } => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message(format!(
                    "identifier {} not previously defined",
                    identifier.fg(Color::Red)
                ))
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(identifier_context.get_span()),
                    ))
                    .with_message("undefined")
                    .with_color(color1),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        KernelError::NonmatchingArgument {
            expected_type,
            observed_type,
            function_context,
            parameter_context,
        } => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message("argument type does not match function signature")
                .with_note(format!(
                    "argument is {}, while function expects {}",
                    format!("{:?}", observed_type).fg(Color::Red),
                    format!("{:?}", expected_type).fg(Color::Green)
                ))
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(function_context.get_span()),
                    ))
                    .with_message("function here")
                    .with_color(color1),
                )
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(parameter_context.get_span()),
                    ))
                    .with_message("argument here")
                    .with_color(color2),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        KernelError::InvalidApplication {
            nonfunction_type,
            nonfunction_context,
            parameter_context,
        } => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message("attempt to apply object that does not accept arguments")
                .with_note(format!(
                    "applied object is of type {}",
                    format!("{:?}", nonfunction_type).fg(Color::Yellow)
                ))
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(nonfunction_context.get_span()),
                    ))
                    .with_message("non-callable")
                    .with_color(color1),
                )
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(parameter_context.get_span()),
                    ))
                    .with_message("argument here")
                    .with_color(color2),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        KernelError::NonmatchingDefinition {
            expected_type,
            observed_type,
            signature_context,
            definition_context,
        } => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message("object type does not match its definition")
                .with_note(format!(
                    "inferred type is {}, while signature states {}",
                    format!("{:?}", observed_type).fg(Color::Red),
                    format!("{:?}", expected_type).fg(Color::Green)
                ))
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(signature_context.get_span()),
                    ))
                    .with_message("type signature")
                    .with_color(color1),
                )
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(definition_context.get_span()),
                    ))
                    .with_message("definition here")
                    .with_color(color2),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        KernelError::InvalidType {
            incorrect_term,
            incorrect_type,
            incorrect_context,
        } => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message(format!(
                    "term's type must be {}, {} or {}",
                    "Set".fg(Color::Green),
                    "Prop".fg(Color::Green),
                    "Type".fg(Color::Green),
                ))
                .with_note(format!(
                    "the given term has type {}",
                    format!("{:?}", incorrect_type).fg(Color::Red),
                ))
                .with_label(
                    Label::new((
                        source_id,
                        (|t: (usize, usize)| t.0..t.1)(incorrect_context.get_span()),
                    ))
                    .with_message("invalid type")
                    .with_color(color1),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        KernelError::MisshapenInductiveDefinition {
            unexpected_subterm,
            subterm_context,
            full_term_context,
        } => {
            println!("MisshapenInductiveDefinition");
        }
        KernelError::NegativeInductiveDefinition {
            negative_subterm,
            subterm_context,
            full_term_context,
        } => {
            println!("NegativeInductiveDefinition");
        }
        KernelError::MisshapenRecursiveDefinition {
            unexpected_subterm,
            subterm_context,
            full_term_context,
        } => {
            println!("MisshapenRecursiveDefinition");
        }
        KernelError::NonprimitiveRecursiveFunction { full_term_context } => {
            println!("NonprimitiveRecursiveFunction");
        }
    }
}
