mod ast;
mod diagnostics;
mod kernel;
mod parser;

struct ProgramConfiguration {
    file_to_open: Option<String>,
}

fn parse_args(args: &Vec<String>) -> ProgramConfiguration {
    match args.len() {
        1 => ProgramConfiguration { file_to_open: None },
        _ => ProgramConfiguration {
            file_to_open: Some(args[1].clone()),
        },
    }
}

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let program_configuration = parse_args(&args);
    let file_to_open = match program_configuration.file_to_open {
        None => panic!("No input files"),
        Some(f) => f,
    };
    let code = std::fs::read_to_string(&file_to_open).expect("Could not read file");
    let parser_result = parser::parse(&code);
    let ast = match parser_result {
        Ok(x) => x,
        Err(e) => {
            for error in e {
                diagnostics::emit_parser_diagnostic(&error, &code, &file_to_open);
            }
            return;
        }
    };
    match kernel::execute(&ast) {
        Ok(_) => {}
        Err(e) => panic!("{:?}", e),
    };
}
