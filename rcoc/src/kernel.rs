use crate::ast::*;

#[derive(Clone, Eq, PartialEq)]
enum Term {
    Identifier(String),
    Application {
        function_term: Box<Term>,
        parameter_term: Box<Term>,
    },
    Lambda {
        binding_identifier: String,
        binding_type: Box<Term>,
        value_term: Box<Term>,
    },
    Forall {
        binding_identifier: String,
        binding_type: Box<Term>,
        value_term: Box<Term>,
    },
}

/// A type representing an error encountered by the kernel while executing some input.
#[derive(Debug)]
pub enum KernelError {
    /// A term contains some identifier that hasn't been defined before.
    UndefinedIdentifier,
    /// A term has been applied on some argument of a different type than that it accepts.
    NonmatchingArgument,
    /// A term that accepts no arguments has been applied on some other term.
    InvalidApplication,
    /// A term has been defined, but the stated type doesn't match its actual type.
    NonmatchingDefinition,
}

struct State {
    terms: std::collections::HashMap<String, (Term, Term)>,
}

impl Term {
    fn create_lambda(binding_list: &[Binding], value_expression: &Expression) -> Term {
        assert!(binding_list.len() >= 1);
        Term::Lambda {
            binding_identifier: binding_list[0].identifier.clone(),
            binding_type: Box::new(Self::new(&binding_list[0].type_expression)),
            value_term: Box::new(match binding_list.len() {
                1 => Self::new(value_expression),
                _ => Self::create_lambda(&binding_list[1..], value_expression),
            }),
        }
    }

    fn create_forall(binding_list: &[Binding], value_expression: &Expression) -> Term {
        assert!(binding_list.len() >= 1);
        Term::Forall {
            binding_identifier: binding_list[0].identifier.clone(),
            binding_type: Box::new(Self::new(&binding_list[0].type_expression)),
            value_term: Box::new(match binding_list.len() {
                1 => Self::new(value_expression),
                _ => Self::create_forall(&binding_list[1..], value_expression),
            }),
        }
    }

    fn create_application(function_expression: &Expression, parameter_list: &[Expression]) -> Term {
        assert!(parameter_list.len() >= 1);
        Term::Application {
            function_term: Box::new(match parameter_list.len() {
                1 => Self::new(function_expression),
                _ => Self::create_application(
                    function_expression,
                    &parameter_list[..parameter_list.len() - 1],
                ),
            }),
            parameter_term: Box::new(Self::new(&parameter_list[parameter_list.len() - 1])),
        }
    }

    pub fn new(expression: &Expression) -> Self {
        match expression {
            Expression::Identifier(s) => Term::Identifier(s.clone()),
            Expression::Application {
                function_expression,
                parameter_expressions,
            } => Self::create_application(&function_expression, parameter_expressions.as_slice()),
            Expression::Lambda {
                binding_list,
                value_expression,
            } => Self::create_lambda(binding_list.as_slice(), &value_expression),
            Expression::Forall {
                binding_list,
                value_expression,
            } => Self::create_forall(binding_list.as_slice(), &value_expression),
        }
    }

    fn contains(self: &Self, identifier: &String) -> bool {
        match self {
            Self::Identifier(s) => s == identifier,
            Self::Application {
                function_term,
                parameter_term,
            } => function_term.contains(identifier) || parameter_term.contains(identifier),
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                binding_type.contains(identifier)
                    || binding_identifier != identifier && value_term.contains(identifier)
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                binding_type.contains(identifier)
                    || binding_identifier != identifier && value_term.contains(identifier)
            }
        }
    }

    pub fn replace(self: &mut Self, identifier: &String, value: &Self) {
        match self {
            Self::Identifier(s) => {
                if s == identifier {
                    *self = value.clone();
                }
            }
            Self::Application {
                function_term,
                parameter_term,
            } => {
                function_term.replace(identifier, value);
                parameter_term.replace(identifier, value);
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                binding_type.replace(identifier, value);
                if binding_identifier != identifier {
                    value_term.replace(identifier, value);
                }
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                binding_type.replace(identifier, value);
                if binding_identifier != identifier {
                    value_term.replace(identifier, value);
                }
            }
        }
    }

    /// Applies the β-reduction rule of lambda calculus.
    /// If the term can be β-reduced, one such reduction is performed
    /// and this method returns true. Otherwise, it returns false
    /// and no change is performed.
    ///
    /// (λx.F)P = f[x:=P]
    ///
    pub fn beta_reduce(self: &mut Self) -> bool {
        if let Self::Application {
            function_term,
            parameter_term,
        } = self
        {
            if let Self::Lambda {
                binding_identifier,
                binding_type: _,
                value_term,
            } = &mut **function_term
            {
                value_term.replace(&binding_identifier, parameter_term);
                *self = (**value_term).clone();
                return true;
            }
        }
        match self {
            Self::Identifier(_) => false,
            Self::Application {
                function_term,
                parameter_term,
            } => function_term.beta_reduce() || parameter_term.beta_reduce(),
            Self::Lambda {
                binding_identifier: _,
                binding_type,
                value_term,
            } => binding_type.beta_reduce() || value_term.beta_reduce(),
            Self::Forall {
                binding_identifier: _,
                binding_type,
                value_term,
            } => binding_type.beta_reduce() || value_term.beta_reduce(),
        }
    }

    /// Applies the η-reduction rule of lambda calculus.
    /// If the term can be η-reduced, one such reduction is performed
    /// and this method returns true. Otherwise, it returns false
    /// and no change is performed.
    ///
    /// λx.F x = F only if F[x:=M] = F for all M
    ///
    pub fn eta_reduce(self: &mut Self) -> bool {
        if let Self::Lambda {
            binding_identifier,
            binding_type: _,
            value_term,
        } = self
        {
            if let Self::Application {
                function_term,
                parameter_term,
            } = &**value_term
            {
                if let Self::Identifier(s) = &**parameter_term {
                    if s == binding_identifier && !function_term.contains(s) {
                        *self = *function_term.clone();
                        return true;
                    }
                }
            }
        }
        match self {
            Self::Identifier(_) => false,
            Self::Application {
                function_term,
                parameter_term,
            } => function_term.eta_reduce() || parameter_term.eta_reduce(),
            Self::Lambda {
                binding_identifier: _,
                binding_type,
                value_term,
            } => binding_type.eta_reduce() || value_term.eta_reduce(),
            Self::Forall {
                binding_identifier: _,
                binding_type,
                value_term,
            } => binding_type.eta_reduce() || value_term.eta_reduce(),
        }
    }

    /// Applies both β- and η-reduction until fully normalized.
    /// Preserves variable names.
    ///
    pub fn normalize(self: &mut Self) {
        loop {
            if !(self.beta_reduce() || self.eta_reduce()) {
                break;
            }
        }
    }

    fn alpha_normalize_recursive(self: &mut Self, dictionary: &mut Vec<String>) {
        match self {
            Self::Identifier(s) => {
                for n in 0..dictionary.len() {
                    if s == &dictionary[n] {
                        *s = format!("#{}", n);
                    }
                }
            }
            Self::Application {
                function_term,
                parameter_term,
            } => {
                function_term.alpha_normalize_recursive(dictionary);
                parameter_term.alpha_normalize_recursive(dictionary);
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                binding_type.alpha_normalize_recursive(dictionary);
                dictionary.push(binding_identifier.clone());
                value_term.alpha_normalize_recursive(dictionary);
                dictionary.pop();
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                binding_type.alpha_normalize_recursive(dictionary);
                dictionary.push(binding_identifier.clone());
                value_term.alpha_normalize_recursive(dictionary);
                dictionary.pop();
            }
        }
    }

    /// Applies α-conversion, reassigning variable names systematically.
    /// Two equivalent terms always become identical after applying
    /// `.normalize()` followed by `.alpha_normalize()` on both.
    ///
    pub fn alpha_normalize(self: &mut Self) {
        let mut dictionary = vec![];
        self.alpha_normalize_recursive(&mut dictionary)
    }

    /// Applies `.normalize()` followed by `.alpha_normalize()`.
    /// Two equivalent terms always become identical after applying
    /// this method on both.
    ///
    pub fn full_normalize(self: &mut Self) {
        self.normalize();
        self.alpha_normalize();
    }

    fn infer_type_recursive(
        self: &Self,
        state: &State,
        stack: &mut Vec<(String, Self)>,
    ) -> Result<Self, KernelError> {
        match self {
            Self::Identifier(s) => {
                if s == "Prop" {
                    return Ok(Self::Identifier("Type(1)".to_string()));
                }
                for n in (0..stack.len()).rev() {
                    if s == &stack[n].0 {
                        return Ok(stack[n].1.clone());
                    }
                }
                match state.terms.get(s) {
                    Some(t) => Ok(t.0.clone()),
                    None => Err(KernelError::UndefinedIdentifier),
                }
            }
            Self::Application {
                function_term,
                parameter_term,
            } => {
                let function_type = function_term.infer_type_recursive(state, stack)?;
                match function_type {
                    Self::Forall {
                        binding_identifier,
                        binding_type,
                        value_term,
                    } => {
                        let mut parameter_type =
                            parameter_term.infer_type_recursive(state, stack)?;
                        parameter_type.full_normalize();
                        let mut expected_parameter_type = binding_type.clone();
                        expected_parameter_type.full_normalize();
                        if parameter_type != *expected_parameter_type {
                            return Err(KernelError::NonmatchingArgument);
                        }
                        let mut output_type = value_term.clone();
                        output_type.replace(&binding_identifier, parameter_term);
                        Ok(*output_type)
                    }
                    _ => Err(KernelError::InvalidApplication),
                }
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                stack.push((binding_identifier.clone(), *binding_type.clone()));
                let inner_type = value_term.infer_type_recursive(state, stack)?;
                stack.pop();
                Ok(Self::Forall {
                    binding_identifier: binding_identifier.clone(),
                    binding_type: binding_type.clone(),
                    value_term: Box::new(inner_type),
                })
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                stack.push((binding_identifier.clone(), *binding_type.clone()));
                let inner_type = value_term.infer_type_recursive(state, stack);
                stack.pop();
                inner_type
            }
        }
    }

    /// Infers the type of a term, which is always also a term.
    ///
    pub fn infer_type(self: &Self, state: &State) -> Result<Self, KernelError> {
        let mut stack = vec![];
        self.infer_type_recursive(state, &mut stack)
    }
}

impl std::fmt::Debug for Term {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Term::Identifier(s) => {
                f.write_str(s)?;
            }
            Term::Application {
                function_term,
                parameter_term,
            } => {
                let parenthesize_first = match **function_term {
                    Term::Lambda { .. } | Term::Forall { .. } => true,
                    _ => false,
                };
                if parenthesize_first {
                    f.write_str("(")?;
                }
                function_term.fmt(f)?;
                if parenthesize_first {
                    f.write_str(")")?;
                }
                f.write_str(" ")?;
                let parenthesize_second = match **parameter_term {
                    Term::Application { .. } => true,
                    _ => false,
                };
                if parenthesize_second {
                    f.write_str("(")?;
                }
                parameter_term.fmt(f)?;
                if parenthesize_first {
                    f.write_str(")")?;
                }
            }
            Term::Lambda {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                f.write_str("λ")?;
                f.write_str(binding_identifier)?;
                f.write_str(":")?;
                binding_type.fmt(f)?;
                f.write_str(".")?;
                value_term.fmt(f)?;
            }
            Term::Forall {
                binding_identifier,
                binding_type,
                value_term,
            } => {
                f.write_str("∀")?;
                f.write_str(binding_identifier)?;
                f.write_str(":")?;
                binding_type.fmt(f)?;
                f.write_str(".")?;
                value_term.fmt(f)?;
            }
        }
        Result::Ok(())
    }
}

impl State {
    pub fn new() -> Self {
        State {
            terms: std::collections::HashMap::new(),
        }
    }

    pub fn update(self: &mut Self, statement: &Statement) -> Result<(), KernelError> {
        match statement {
            Statement::Definition {
                identifier,
                type_expression,
                value_expression,
            } => {
                let mut type_term = Term::new(type_expression);
                type_term.infer_type(&self)?;
                type_term.normalize();
                let mut value_term = Term::new(value_expression);
                let mut expected_type = value_term.infer_type(&self)?;
                value_term.normalize();
                expected_type.full_normalize();
                let mut actual_type = type_term.clone();
                actual_type.full_normalize();
                if expected_type != actual_type {
                    return Err(KernelError::NonmatchingDefinition);
                }
                value_term.normalize();
                self.terms
                    .insert(identifier.clone(), (type_term, value_term));
            }
        }
        Ok(())
    }
}

pub fn execute(input: &Vec<Statement>) -> Result<(), KernelError> {
    let mut state = State::new();
    for statement in input {
        state.update(statement)?;
    }
    for term in state.terms {
        println!("{} = {:?}\n    :{:?}", term.0, term.1 .1, term.1 .0);
    }
    Ok(())
}
