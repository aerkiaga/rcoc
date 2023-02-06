#[derive(Clone, Debug)]
pub struct Binding {
    pub identifier: String,
    pub type_expression: Box<Expression>,
    pub span: (usize, usize),
}

#[derive(Clone, Debug)]
pub enum Expression {
    Identifier(String, (usize, usize)),
    Application {
        function_expression: Box<Expression>,
        parameter_expression: Box<Expression>,
        span: (usize, usize),
    },
    Lambda {
        binding: Binding,
        value_expression: Box<Expression>,
        span: (usize, usize),
    },
    Forall {
        binding: Binding,
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
                parameter_expression: _,
                span,
            } => *span,
            Self::Lambda {
                binding: _,
                value_expression: _,
                span,
            } => *span,
            Self::Forall {
                binding: _,
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

pub static mut TMP_VARIABLE_CURRENT_INDEX: Option<std::sync::Arc<std::sync::Mutex<u32>>> = None;

pub fn get_tmp_identifier() -> String {
    format!("${}", {
        let mut index = unsafe { TMP_VARIABLE_CURRENT_INDEX.as_ref() }
            .unwrap()
            .lock()
            .unwrap();
        *index += 1;
        *index - 1
    })
}
