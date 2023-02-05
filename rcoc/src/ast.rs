#[derive(Clone, Debug)]
pub struct Binding {
    pub identifier: String,
    pub type_expression: Expression,
}

#[derive(Clone, Debug)]
pub enum Expression {
    Identifier(String, (usize, usize)),
    Application {
        function_expression: Box<Expression>,
        parameter_expressions: Vec<Expression>,
        span: (usize, usize),
    },
    Lambda {
        binding_list: Vec<Binding>,
        value_expression: Box<Expression>,
        span: (usize, usize),
    },
    Forall {
        binding_list: Vec<Binding>,
        value_expression: Box<Expression>,
        span: (usize, usize),
    },
}

impl Expression {
    pub fn get_span(self: &Self) -> (usize, usize) {
        match self {
            Self::Identifier(_, sp) => *sp,
            Self::Application {
                function_expression: _,
                parameter_expressions: _,
                span,
            } => *span,
            Self::Lambda {
                binding_list: _,
                value_expression: _,
                span,
            } => *span,
            Self::Forall {
                binding_list: _,
                value_expression: _,
                span,
            } => *span,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Statement {
    Definition {
        identifier: String,
        type_expression: Expression,
        value_expression: Expression,
        span: (usize, usize),
    },
}
