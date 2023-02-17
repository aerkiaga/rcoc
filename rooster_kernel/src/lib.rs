/// A type containing extra information for debugging proofs
///
/// In principle, bugs in code manipulating this type
/// should not affect proof checking, so this code is
/// outside the trusted base.
///
#[derive(Clone)]
pub enum TermDebugContext {
    CodeSpan((usize, usize)),
    TypeOf(Box<TermDebugContext>),
}

impl TermDebugContext {
    /// Get the span of source code containing this term.
    pub fn get_span(self: &Self) -> (usize, usize) {
        match self {
            Self::CodeSpan(s) => *s,
            Self::TypeOf(b) => b.get_span(),
        }
    }
}

/// A (valid or invalid) term in Calculus of Constructions.
#[derive(Clone)]
pub enum Term {
    /// A symbol representing a bound variable,
    /// a different term in the current state,
    /// or the special identifiers `Prop` and `Type(1)`.
    Identifier(String, TermDebugContext),
    /// Application of an object onto another,
    /// i.e. A B, for any terms A and B.
    Application {
        function_term: Box<Term>,
        parameter_term: Box<Term>,
        debug_context: TermDebugContext,
    },
    /// Typed lambda abstraction, i.e. λx:A.B,
    /// for any identifier x and terms A and B.
    Lambda {
        binding_identifier: String,
        binding_type: Box<Term>,
        value_term: Box<Term>,
        debug_context: TermDebugContext,
    },
    /// Typed for all ... expression, i.e. ∀x:A.B,
    /// for any identifier x and terms A and B.
    Forall {
        binding_identifier: String,
        binding_type: Box<Term>,
        value_term: Box<Term>,
        debug_context: TermDebugContext,
    },
}

impl PartialEq for Term {
    /// Two terms are considered equal if and only if
    /// they contain identical syntactic trees, with
    /// every variable named exactly the same across them.
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

/// Context that terms inhabit.
pub struct State {
    terms: std::collections::HashMap<String, (Term, Term)>,
}

impl Term {
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

    /// Renames identifier everywhere within the given term.
    ///
    /// Note that variable shadowing applies, so e.g. renaming
    /// 'x' to 'y' in (λx:A.x B) x would result in (λx:A.x B) y,
    /// and the same in (∀x:A.x B) x would give (∀x:A.x B) y.
    ///
    pub fn rename(self: &mut Self, identifier: &String, new_name: &String) {
        match self {
            Self::Identifier(s, db) => {
                if s == identifier {
                    *self = Self::Identifier(new_name.clone(), db.clone());
                }
            }
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                function_term.rename(identifier, new_name);
                parameter_term.rename(identifier, new_name);
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.rename(identifier, new_name);
                if binding_identifier != identifier {
                    value_term.rename(identifier, new_name);
                }
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.rename(identifier, new_name);
                if binding_identifier != identifier {
                    value_term.rename(identifier, new_name);
                }
            }
        }
    }

    /// Replaces every occurrence of a variable by a new term.
    ///
    /// There are two special cases to consider. Firstly, shadowing,
    /// so that replacing 'x' by V in (λx:A.x B) x gives (λx:A.x B) V,
    /// and the same in (∀x:A.x B) x produces (∀x:A.x B) V.
    /// Secondly, in a case like λy:A.x y B, replacing that 'x' would
    /// produce a wrong result if V happens to contain 'y'. In this case,
    /// the substitution would be applied like this: λy_:A.V y_ B.
    /// Same goes for ∀y:A.x y B.
    /// 
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
                    if value.contains(binding_identifier) {
                        let new_binding_identifier = format!("{}_", binding_identifier);
                        value_term.rename(binding_identifier, &new_binding_identifier);
                        *binding_identifier = new_binding_identifier;
                    }
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
                    if value.contains(binding_identifier) {
                        let new_binding_identifier = format!("{}_", binding_identifier);
                        value_term.rename(binding_identifier, &new_binding_identifier);
                        *binding_identifier = new_binding_identifier;
                    }
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
    /// (λx:T.F) P = f[x:=P]
    ///
    /// Please note that no type checking is performed.
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
    /// λx:T.F x = F only if F[x:=M] = F for all M
    ///
    /// Please note that no type checking is performed.
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
            // refer to just F rather than λx:T.F x in diagnostics
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
    /// Please note that no type checking is performed.
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
    /// Please note that no type checking is performed.
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
                        // so that the type of (λx:T.x) P
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

    /// Infers the type of a term, which is in turn also a term.
    ///
    /// Will return an error if the given term is invalid.
    ///
    pub fn infer_type(self: &Self, state: &State) -> Result<Self, KernelError> {
        let mut stack = vec![];
        self.infer_type_recursive(state, &mut stack)
    }
}

impl std::fmt::Debug for Term {
    /// Formats the given term as Calculus of Contructions.
    ///
    /// Uses symbols λ and ∀, plus two abbreviations:
    /// * ∀x:A.B as A→B if B doesn't contain x.
    /// * ∀x:A.x as ⊥.
    ///
    /// Needless to say, this code is not part of the
    /// trusted base.
    ///
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
                    // special case: A→B := ∀x:A.B
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
                } else if if let Term::Identifier(s, _) = &**value_term {
                    s == binding_identifier
                } else {
                    false
                } {
                    // special case: ⊥ := ∀x:A.x
                    f.write_str("⊥")?;
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
    /// Creates a new context containing no terms.
    pub fn new() -> Self {
        State {
            terms: std::collections::HashMap::new(),
        }
    }

    /// Attempts to define a new variable in the given state.
    ///
    /// This is equivalent to `let x: A = B;`.
    /// Will return an error if either term is invalid
    /// or the type of `B` doesn't match `A`.
    ///
    pub fn try_define(
        self: &mut Self,
        identifier: &String,
        mut type_term: Term,
        mut value_term: Term,
    ) -> Result<(), KernelError> {
        type_term.infer_type(&self)?;
        type_term.normalize();
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
        self.terms
            .insert(identifier.clone(), (type_term, value_term));
        Ok(())
    }
}
