#[derive(Clone, Debug)]
pub struct Binding {
    pub identifier: String,
    pub type_expression: Expression,
}

#[derive(Clone, Debug)]
pub enum Expression {
    Identifier(String),
    Application {
        function_expression: Box<Expression>,
        parameter_expressions: Vec<Expression>,
    },
    Lambda {
        binding_list: Vec<Binding>,
        value_expression: Box<Expression>,
    },
    Forall {
        binding_list: Vec<Binding>,
        value_expression: Box<Expression>,
    },
}

#[derive(Clone, Debug)]
pub enum Statement {
    Empty,
    Definition {
        identifier: String,
        type_expression: Expression,
        value_expression: Expression,
    },
}
