mod ast;
mod kernel;
mod parser;

const code: &str = "
/*comment*/
//comment
let a:
    @(T: Prop, x: T) T
=
    |T: Prop, x: T| {|y: T| y}(x)
;
";

fn main() {
    let parser_result = parser::parse(code);
    let ast = match parser_result {
        Ok(x) => x,
        Err(e) => panic!("{:?}", e),
    };
    match kernel::execute(&ast) {
        Ok(_) => {},
        Err(e) => panic!("{:?}", e),
    };
}
