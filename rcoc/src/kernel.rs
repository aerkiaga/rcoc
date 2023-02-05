use crate::ast::*;

#[derive(Clone)]
pub enum TermDebugContext {
    CodeSpan((usize, usize)),
    TypeOf(Box<TermDebugContext>),
}

impl TermDebugContext {
    pub fn get_span(self: &Self) -> (usize, usize) {
        match self {
            Self::CodeSpan(s) => *s,
            Self::TypeOf(b) => b.get_span(),
        }
    }
}

#[derive(Clone)]
pub enum Term {
    Identifier(String, TermDebugContext),
    Application {
        function_term: Box<Term>,
        parameter_term: Box<Term>,
        debug_context: TermDebugContext,
    },
    Lambda {
        binding_identifier: String,
        binding_type: Box<Term>,
        value_term: Box<Term>,
        debug_context: TermDebugContext,
    },
    Forall {
        binding_identifier: String,
        binding_type: Box<Term>,
        value_term: Box<Term>,
        debug_context: TermDebugContext,
    },
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Identifier(s, _) => {
                if let Self::Identifier(s2, _) = other {
                    s == s2
                } else {
                    false
                }
            }
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                if let Self::Application {
                    function_term: function_term2,
                    parameter_term: parameter_term2,
                    debug_context: _,
                } = other
                {
                    function_term == function_term2 && parameter_term == parameter_term2
                } else {
                    false
                }
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                if let Self::Lambda {
                    binding_identifier: binding_identifier2,
                    binding_type: binding_type2,
                    value_term: value_term2,
                    debug_context: _,
                } = other
                {
                    binding_identifier == binding_identifier2
                        && binding_type == binding_type2
                        && value_term == value_term2
                } else {
                    false
                }
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                if let Self::Forall {
                    binding_identifier: binding_identifier2,
                    binding_type: binding_type2,
                    value_term: value_term2,
                    debug_context: _,
                } = other
                {
                    binding_identifier == binding_identifier2
                        && binding_type == binding_type2
                        && value_term == value_term2
                } else {
                    false
                }
            }
        }
    }
}

impl Eq for Term {}

/// A type representing an error encountered by the kernel while executing some input.
pub enum KernelError {
    /// A term contains some identifier that hasn't been defined before.
    UndefinedIdentifier {
        identifier: String,
        identifier_context: TermDebugContext,
    },
    /// A term has been applied on some argument of a different type than that it accepts.
    NonmatchingArgument {
        expected_type: Term,
        observed_type: Term,
        function_context: TermDebugContext,
        parameter_context: TermDebugContext,
    },
    /// A term that accepts no arguments has been applied on some other term.
    InvalidApplication {
        nonfunction_type: Term,
        nonfunction_context: TermDebugContext,
        parameter_context: TermDebugContext,
    },
    /// A term has been defined, but the stated type doesn't match its actual type.
    NonmatchingDefinition {
        expected_type: Term,
        observed_type: Term,
        signature_context: TermDebugContext,
        definition_context: TermDebugContext,
    },
}

pub struct State {
    terms: std::collections::HashMap<String, (Term, Term)>,
}

impl Term {
    fn create_lambda(
        binding_list: &[Binding],
        value_expression: &Expression,
        span: (usize, usize),
    ) -> Term {
        assert!(binding_list.len() >= 1);
        Term::Lambda {
            binding_identifier: binding_list[0].identifier.clone(),
            binding_type: Box::new(Self::new(&binding_list[0].type_expression)),
            value_term: Box::new(match binding_list.len() {
                1 => Self::new(value_expression),
                _ => Self::create_lambda(&binding_list[1..], value_expression, span),
            }),
            debug_context: TermDebugContext::CodeSpan(span),
        }
    }

    fn create_forall(
        binding_list: &[Binding],
        value_expression: &Expression,
        span: (usize, usize),
    ) -> Term {
        assert!(binding_list.len() >= 1);
        Term::Forall {
            binding_identifier: binding_list[0].identifier.clone(),
            binding_type: Box::new(Self::new(&binding_list[0].type_expression)),
            value_term: Box::new(match binding_list.len() {
                1 => Self::new(value_expression),
                _ => Self::create_forall(&binding_list[1..], value_expression, span),
            }),
            debug_context: TermDebugContext::CodeSpan(span),
        }
    }

    fn create_application(
        function_expression: &Expression,
        parameter_list: &[Expression],
        span: (usize, usize),
    ) -> Term {
        assert!(parameter_list.len() >= 1);
        Term::Application {
            function_term: Box::new(match parameter_list.len() {
                1 => Self::new(function_expression),
                _ => Self::create_application(
                    function_expression,
                    &parameter_list[..parameter_list.len() - 1],
                    span,
                ),
            }),
            parameter_term: Box::new(Self::new(&parameter_list[parameter_list.len() - 1])),
            debug_context: TermDebugContext::CodeSpan(span),
        }
    }

    pub fn new(expression: &Expression) -> Self {
        match expression {
            Expression::Identifier(s, sp) => {
                Term::Identifier(s.clone(), TermDebugContext::CodeSpan(*sp))
            }
            Expression::Application {
                function_expression,
                parameter_expressions,
                span,
            } => Self::create_application(
                &function_expression,
                parameter_expressions.as_slice(),
                *span,
            ),
            Expression::Lambda {
                binding_list,
                value_expression,
                span,
            } => Self::create_lambda(binding_list.as_slice(), &value_expression, *span),
            Expression::Forall {
                binding_list,
                value_expression,
                span,
            } => Self::create_forall(binding_list.as_slice(), &value_expression, *span),
        }
    }

    fn contains(self: &Self, identifier: &String) -> bool {
        match self {
            Self::Identifier(s, _) => s == identifier,
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => function_term.contains(identifier) || parameter_term.contains(identifier),
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.contains(identifier)
                    || binding_identifier != identifier && value_term.contains(identifier)
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.contains(identifier)
                    || binding_identifier != identifier && value_term.contains(identifier)
            }
        }
    }

    pub fn replace(self: &mut Self, identifier: &String, value: &Self) {
        match self {
            Self::Identifier(s, _) => {
                if s == identifier {
                    *self = value.clone();
                }
            }
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                function_term.replace(identifier, value);
                parameter_term.replace(identifier, value);
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
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
                debug_context: _,
            } => {
                binding_type.replace(identifier, value);
                if binding_identifier != identifier {
                    value_term.replace(identifier, value);
                }
            }
        }
    }

    fn with_new_debug_context(self: &Self, new_debug_context: &TermDebugContext) -> Self {
        match self {
            Self::Identifier(s, _) => Self::Identifier(s.clone(), new_debug_context.clone()),
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => Self::Application {
                function_term: function_term.clone(),
                parameter_term: parameter_term.clone(),
                debug_context: new_debug_context.clone(),
            },
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => Self::Lambda {
                binding_identifier: binding_identifier.clone(),
                binding_type: binding_type.clone(),
                value_term: value_term.clone(),
                debug_context: new_debug_context.clone(),
            },
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => Self::Forall {
                binding_identifier: binding_identifier.clone(),
                binding_type: binding_type.clone(),
                value_term: value_term.clone(),
                debug_context: new_debug_context.clone(),
            },
        }
    }

    /// Applies the β-reduction rule of lambda calculus.
    /// If the term can be β-reduced, one such reduction is performed
    /// and this method returns true. Otherwise, it returns false
    /// and no change is performed.
    ///
    /// (λx.F) P = f[x:=P]
    ///
    pub fn beta_reduce(self: &mut Self) -> bool {
        if let Self::Application {
            function_term,
            parameter_term,
            debug_context,
        } = self
        {
            let new_debug_context = debug_context;
            if let Self::Lambda {
                binding_identifier,
                binding_type: _,
                value_term,
                debug_context: _,
            } = &mut **function_term
            {
                value_term.replace(&binding_identifier, parameter_term);
                *self = (**value_term).with_new_debug_context(new_debug_context);
                return true;
            }
        }
        match self {
            Self::Identifier(_, _) => false,
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => function_term.beta_reduce() || parameter_term.beta_reduce(),
            Self::Lambda {
                binding_identifier: _,
                binding_type,
                value_term,
                debug_context: _,
            } => binding_type.beta_reduce() || value_term.beta_reduce(),
            Self::Forall {
                binding_identifier: _,
                binding_type,
                value_term,
                debug_context: _,
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
            debug_context: _,
        } = self
        {
            // do not use the outer debug context, i.e.
            // refer to just F rather than λx.F x in diagnostics
            if let Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } = &**value_term
            {
                if let Self::Identifier(s, _) = &**parameter_term {
                    if s == binding_identifier && !function_term.contains(s) {
                        *self = *function_term.clone();
                        return true;
                    }
                }
            }
        }
        match self {
            Self::Identifier(_, _) => false,
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => function_term.eta_reduce() || parameter_term.eta_reduce(),
            Self::Lambda {
                binding_identifier: _,
                binding_type,
                value_term,
                debug_context: _,
            } => binding_type.eta_reduce() || value_term.eta_reduce(),
            Self::Forall {
                binding_identifier: _,
                binding_type,
                value_term,
                debug_context: _,
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
            Self::Identifier(s, _) => {
                for n in 0..dictionary.len() {
                    if s == &dictionary[n] {
                        *s = format!("#{}", n);
                    }
                }
            }
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                function_term.alpha_normalize_recursive(dictionary);
                parameter_term.alpha_normalize_recursive(dictionary);
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.alpha_normalize_recursive(dictionary);
                dictionary.push(binding_identifier.clone());
                value_term.alpha_normalize_recursive(dictionary);
                dictionary.pop();
                *binding_identifier = format!("#{}", dictionary.len());
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.alpha_normalize_recursive(dictionary);
                dictionary.push(binding_identifier.clone());
                value_term.alpha_normalize_recursive(dictionary);
                dictionary.pop();
                *binding_identifier = format!("#{}", dictionary.len());
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

    fn get_debug_context<'a>(self: &'a Self) -> &'a TermDebugContext {
        match self {
            Self::Identifier(_, db) => db,
            Self::Application {
                function_term: _,
                parameter_term: _,
                debug_context,
            } => debug_context,
            Self::Lambda {
                binding_identifier: _,
                binding_type: _,
                value_term: _,
                debug_context,
            } => debug_context,
            Self::Forall {
                binding_identifier: _,
                binding_type: _,
                value_term: _,
                debug_context,
            } => debug_context,
        }
    }

    fn infer_type_recursive(
        self: &Self,
        state: &State,
        stack: &mut Vec<(String, Self)>,
    ) -> Result<Self, KernelError> {
        match self {
            Self::Identifier(s, db) => {
                if s == "Prop" {
                    return Ok(Self::Identifier(
                        "Type(1)".to_string(),
                        TermDebugContext::TypeOf(Box::new(db.clone())),
                    ));
                }
                for n in (0..stack.len()).rev() {
                    if s == &stack[n].0 {
                        return Ok(stack[n].1.clone());
                    }
                }
                match state.terms.get(s) {
                    Some(t) => Ok(t.0.clone()),
                    None => Err(KernelError::UndefinedIdentifier {
                        identifier: s.clone(),
                        identifier_context: db.clone(),
                    }),
                }
            }
            Self::Application {
                function_term,
                parameter_term,
                debug_context,
            } => {
                let new_debug_context = TermDebugContext::TypeOf(Box::new(debug_context.clone()));
                let function_type = function_term.infer_type_recursive(state, stack)?;
                match function_type {
                    Self::Forall {
                        binding_identifier,
                        binding_type,
                        value_term,
                        debug_context: _,
                    } => {
                        let mut parameter_type =
                            parameter_term.infer_type_recursive(state, stack)?;
                        parameter_type.full_normalize();
                        let mut expected_parameter_type = binding_type.clone();
                        expected_parameter_type.full_normalize();
                        if parameter_type != *expected_parameter_type {
                            return Err(KernelError::NonmatchingArgument {
                                expected_type: *expected_parameter_type,
                                observed_type: parameter_type,
                                function_context: function_term.get_debug_context().clone(),
                                parameter_context: parameter_term.get_debug_context().clone(),
                            });
                        }
                        let mut output_type = value_term.with_new_debug_context(&new_debug_context);
                        // replace after assigning new debug context,
                        // so that the type of (λx.x) P
                        // is shown simply as the type of P
                        output_type.replace(&binding_identifier, parameter_term);
                        Ok(output_type)
                    }
                    _ => Err(KernelError::InvalidApplication {
                        nonfunction_type: function_type,
                        nonfunction_context: function_term.get_debug_context().clone(),
                        parameter_context: parameter_term.get_debug_context().clone(),
                    }),
                }
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context,
            } => {
                stack.push((binding_identifier.clone(), *binding_type.clone()));
                let inner_type = value_term.infer_type_recursive(state, stack)?;
                stack.pop();
                Ok(Self::Forall {
                    binding_identifier: binding_identifier.clone(),
                    binding_type: binding_type.clone(),
                    value_term: Box::new(inner_type),
                    debug_context: TermDebugContext::TypeOf(Box::new(debug_context.clone())),
                })
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context,
            } => {
                stack.push((binding_identifier.clone(), *binding_type.clone()));
                let mut inner_type = value_term.infer_type_recursive(state, stack)?;
                stack.pop();
                // replace after inferring inner type,
                // so that the type of ∀x:P.Q
                // is not just shown as the type of Q
                // unless Q doesn't contain x
                if value_term.contains(binding_identifier) {
                    inner_type = inner_type.with_new_debug_context(&TermDebugContext::TypeOf(
                        Box::new(debug_context.clone()),
                    ));
                }
                Ok(inner_type)
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
            Term::Identifier(s, _) => {
                f.write_str(s)?;
            }
            Term::Application {
                function_term,
                parameter_term,
                debug_context: _,
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
                debug_context: _,
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
                debug_context: _,
            } => {
                if !value_term.contains(binding_identifier) {
                    // special case: A -> B := ∀x:A.B
                    let parenthesize_first = match **binding_type {
                        Term::Lambda { .. } | Term::Forall { .. } => true,
                        _ => false,
                    };
                    if parenthesize_first {
                        f.write_str("(")?;
                    }
                    binding_type.fmt(f)?;
                    if parenthesize_first {
                        f.write_str(")")?;
                    }
                    f.write_str("→")?;
                    value_term.fmt(f)?;
                } else {
                    // ∀x:A.B where B contains x
                    f.write_str("∀")?;
                    f.write_str(binding_identifier)?;
                    f.write_str(":")?;
                    binding_type.fmt(f)?;
                    f.write_str(".")?;
                    value_term.fmt(f)?;
                }
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
                span: _,
            } => {
                let mut type_term = Term::new(type_expression);
                type_term.infer_type(&self)?;
                type_term.normalize();
                let mut value_term = Term::new(value_expression);
                let mut actual_type = value_term.infer_type(&self)?;
                value_term.normalize();
                actual_type.full_normalize();
                let mut expected_type = type_term.clone();
                expected_type.full_normalize();
                if expected_type != actual_type {
                    return Err(KernelError::NonmatchingDefinition {
                        expected_type: expected_type,
                        observed_type: actual_type,
                        signature_context: type_term.get_debug_context().clone(),
                        definition_context: value_term.get_debug_context().clone(),
                    });
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
