use ariadne::*;
use chumsky::error::*;

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
        expected_str.push_str(&format!("{}", error_expected[n].unwrap().to_string().fg(color1)));
        if n < (error_expected.len() - 2) {
            expected_str.push_str(", ");
        }
    }
    if error_expected.len() > 1 {
        expected_str.push_str(" or ");
    }
    expected_str.push_str(&format!(
        "{}",
        error_expected[error_expected.len() - 1].unwrap().to_string().fg(color1)
    ));
    match error_reason {
        SimpleReason::Unexpected => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message("unexpected token")
                .with_label(Label::new((source_id, error_span)).with_message(expected_str))
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        SimpleReason::Unclosed { span, delimiter: _ } => {
            Report::build(ReportKind::Error, source_id, 0)
                .with_message("unclosed delimiter")
                .with_label(Label::new((source_id, error_span)).with_message(expected_str))
                .with_label(
                    Label::new((source_id, span.clone())).with_message("opening delimiter here"),
                )
                .finish()
                .print((source_id, Source::from(code)))
                .unwrap();
        }
        _ => (),
    };
}
