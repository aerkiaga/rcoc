//! This crate contains **Rooster**'s proof kernel code,
//! an implementation of the [Calculus of Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions) (CoC).
//!
//! CoC is a mathematical type theory and programming language
//! developed by adding dependent types, polymorphism and
//! type operators to simply typed lambda calculus. Devised by
//! Thierry Coquand, it is _strongly normalizing_ (i.e. every
//! program in CoC terminates, and thus CoC is not
//! Turing-complete) and follows the Curry-Howard isomorphism,
//! which links together programs and proofs.
//!
//! CoC can be used to write both standard programs and
//! proofs of propositions. It provides _intuitionistic_
//! logic as a foundation to build upon, which is weaker
//! than classical logic.
//!
//! A _term_ in CoC can take the following forms:
//! * x, where 'x' is an identifier.
//! * A B, for terms A and B.
//! * λx:A.B, for identifier 'x' and terms A and B.
//! * ∀x:A.B, for identifier 'x' and terms A and B.
//! * 𝐘x:A.B, for identifier 'x' and terms A and B.
//!
//! _?_, _Set_, _Prop_ and _Type(1)_ are special, pre-defined identifiers.
//!
//! The kernel offers two main operations on terms. The first
//! is _normalizing_, which is equivalent to computation and
//! reduces terms to an equivalent form. The second is
//! _type inference_, which determines the type of a term,
//! but also checks if the term itself is valid. The type of
//! a term is also a term.
//!
//! Finally, the kernel offers the ability to _define_
//! variables within a _state_. A definition like
//! `x = B: A` involves normalizing both A and B,
//! checking that A is valid, and comparing B's type
//! to A. Then, the new term is added to the state.
//!
//! ## Free variables
//! A term is said to freely contain a variable
//! if an occurrence of it is anywhere within the term
//! and it is not bound to any inner scope. For example,
//! x a x contains 'x' as a free variable, while
//! λx.x a x doesn't. However, (λx.x a x) x does contain 'x'
//! (the last occurrence). Same goes for terms involving
//! ∀ or 𝐘 instead of λ.
//!
//! ## Substitution
//! Substitution involves replacing a variable within
//! a term by a second term. All free occurrences of the
//! variable are replaced.
//!
//! There's a special case to consider. If the new term
//! contains free variables that would become bound upon
//! substitution, renaming is performed. For example,
//! consider the term λx:A.y x., where 'y' is to be
//! replaced by a term containing a free occurrence of 'x'.
//! Substituting it into the inner scope would bind 'x',
//! so it would refer to a different variable than it should.
//! This is solved by renaming the inner 'x', like so:
//! λx0:A.y x0. Now, substitution can be performed.
//!
//! To rename a variable like this, a name is chosen that
//! is not a free variable within the abstraction.
//! For example, in λx:A.x x0, 'x' wouldn't be renamed to
//! 'x0', a different name would be chosen.
//!
//! Then, substitution is used to replace the variable.
//! This means that all of the above is applied again.
//!
//! ## Normalization rules
//! The following rules are applied, whenever valid, in any
//! order, until none of them can be applied further. Since
//! CoC is strongly normalizing, every finite term is fully
//! normalized after a finite amount of steps.
//!
//! ### β-reduction
//! Transforms (λx:T.F) P into F[x:=P], i.e. "returns" F,
//! with every occurrence of 'x' replaced with term P.
//!
//! Substitution is used to perform this replacement,
//! with the rules explained above.
//!
//! ### η-reduction
//! Transforms λx:T.F x into F only if 'x' doesn't
//! appear free (i.e. accounting for shadowing) in F.
//!
//! ### δ-reduction
//! Replaces each free variable that's defined in the
//! containing state by its value, using substitution.
//!
//! ### α-conversion
//! This involves renaming identifiers. It can be performed
//! trivially for any expression containing identifiers,
//! so it is not necessary to perform it for normalizing,
//! unless two terms need to be compared (since they need
//! to have the exact same variable names).
//!
//! Renaming identifiers is also done via substitution,
//! so all of the rules of substitution apply here.
//!
//! In this kernel, α-conversion is only aimed at comparing
//! terms. The way it is performed is the following:
//! every variable defined within the term is given a name
//! of the form '#n', where n is some natural number.
//! Two terms that are equivalent up to α-conversion will
//! always become identical after applying this to both.
//!
//! ### Fixed-point reduction
//! An expression of the form 𝐘x:A.B will be replaced by
//! (λx:A.B)(𝐘x:A.B). Note that this operation can succeed
//! every time, _ad infinitum_, so the expression must be
//! normalized before every fixed-point reduction. If the
//! term is valid (which should have been checked), type
//! rules will enforce eventual termination.
//!
//! Fixed-point reduction only operates if B is a term
//! of the form λy:C.D. Otherwise, it does nothing.
//!
//! ## Type inference rules
//! * Variables defined outside the term (in its containing
//! _state_) take the type they were defined with.
//! * _Set_ and _Prop_ have type _Type(1)_.
//! * ? has type ?.
//! * ∀x:A.B takes the type of B, with each free occurrence
//! of 'x' within B taking type A.
//!   - If A equals ?, however, the term takes type Set.
//!     * In this case, occurrences of x must be at
//!       strictly positive positions within B.
//! * λx:A.B takes type ∀x:A.T, with T being the type of B
//! with each free occurrence of 'x' within B taking type A.
//! * A B, where A has type ∀x:T.V, takes type V[x:=B].
//!   - If A doesn't have such type, the term is invalid.
//!   - If B is not of type T, the term is invalid.
//!     * This does not apply if T equals ?.
//! * 𝐘x:A.B takes type B, with each free occurrence
//! of 'x' within B taking type A.
//!   - B can be an expression of the form ∀x1:A1.∀x2:A2. ... C
//!     wherein each An only contains x strictly positively
//!     and C doesn't freely contain x.
//!   - B can also be an expression of the form λx1:A1.λx2:A2. ... C
//!     wherein every occurrence of x in C reduces to
//!     x y1 y2 ... and there is at least some i such that
//!     every yi is captured by an abstraction passed to
//!     xi, which type's type is Set.
//!   - If B doesn't follow the above, the term is invalid.
//!

/// A type containing extra information for debugging proofs.
///
/// In principle, bugs in code manipulating this type
/// should not affect proof checking, so this code is
/// outside the trusted base.
///
#[derive(Clone)]
pub enum TermDebugContext {
    /// No information, don't propagate.
    Ignore,
    /// The term originates from a span of the input source code.
    CodeSpan((usize, usize)),
    /// The term is the type of a term with a given debug context.
    TypeOf(Box<TermDebugContext>),
}

impl TermDebugContext {
    /// Get the span of source code containing this term.
    pub fn get_span(self: &Self) -> (usize, usize) {
        match self {
            Self::Ignore => (0, 0),
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
    /// Inductive Y combinator-like, i.e. 𝐘x:A.B,
    /// for any identifier x and terms A and B.
    FixedPoint {
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
            Self::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                if let Self::FixedPoint {
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
    // Either the type definition or one of its parameters don't evaluate
    // to a term of the form A1→A2→A3→...→B.
    MisshapenInductiveDefinition {
        unexpected_subterm: Term,
        subterm_context: TermDebugContext,
        full_term_context: TermDebugContext,
    },
    // An identifier is at a negative position in the type definition,
    // which is not allowed (e.g. (x→B)→C).
    NegativeInductiveDefinition {
        negative_subterm: Term,
        subterm_context: TermDebugContext,
        full_term_context: TermDebugContext,
    },
    // Either the type definition or a recursive function
    // don't evaluate to a term of the form A1→A2→A3→...→B
    // or λx1:A1.λx2:A2.λx3:A3. ... B.
    MisshapenRecursiveDefinition {
        unexpected_subterm: Term,
        subterm_context: TermDebugContext,
        full_term_context: TermDebugContext,
    },
    // The function doesn't have any single parameter
    // that is clearly decreasing for every recursive invocation.
    NonprimitiveRecursiveFunction {
        full_term_context: TermDebugContext,
    },
}

/// Context that terms inhabit.
pub struct State {
    terms: std::collections::HashMap<String, (Term, Term)>,
}

impl Term {
    fn debug_context(self: &Self) -> &TermDebugContext {
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
            Self::FixedPoint {
                binding_identifier: _,
                binding_type: _,
                value_term: _,
                debug_context,
            } => debug_context,
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
            Self::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => Self::FixedPoint {
                binding_identifier: binding_identifier.clone(),
                binding_type: binding_type.clone(),
                value_term: value_term.clone(),
                debug_context: new_debug_context.clone(),
            },
        }
    }

    // Checks if the given term contains an identifier in free form,
    /// that is, not shadowed by any variable defined within the term.
    pub fn contains(self: &Self, identifier: &String) -> bool {
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
            Self::FixedPoint {
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

    /// Replaces every occurrence of a variable by a new term.
    ///
    /// There are two special cases to consider. Firstly, shadowing,
    /// so that replacing 'x' by V in (λx:A.x B) x gives (λx:A.x B) V,
    /// and the same in (∀x:A.x B) x produces (∀x:A.x B) V.
    /// Secondly, in a case like λy:A.x y, replacing that 'x' would
    /// produce a wrong result if V happens to contain 'y'. In this case,
    /// the substitution would be applied like this: λy0:A.V y0.
    /// Same goes for ∀y:A.x y. In this case, a new name is chosen
    /// that does not occur freely in the inner expression (here x y,
    /// so y0 is a valid name), and then `replace` is called on it.
    ///
    /// Regarding debug context, this function applies an exception:
    /// if the value to be substituted into a given term has a debug
    /// context TermDebugContext::Ignore, the debug context of the
    /// original variable occurrences will be preserved, rather than
    /// copying over the context from the new term.
    ///
    pub fn replace(self: &mut Self, identifier: &String, value: &Self) {
        match self {
            Self::Identifier(s, db) => {
                if s == identifier {
                    if let TermDebugContext::Ignore = value.debug_context() {
                        // ignore new debug context
                        *self = value.with_new_debug_context(db)
                    } else {
                        // copy over new debug context
                        *self = value.clone()
                    }
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
                        let mut suffix: u64 = 0;
                        loop {
                            let new_binding_identifier =
                                format!("{}{}", binding_identifier, suffix);
                            if !value_term.contains(&new_binding_identifier) {
                                value_term.replace(
                                    binding_identifier,
                                    &Self::Identifier(
                                        new_binding_identifier.clone(),
                                        TermDebugContext::Ignore,
                                    ),
                                );
                                *binding_identifier = new_binding_identifier;
                                break;
                            }
                            if suffix == u64::MAX {
                                panic!("Ran out of suffixes for variable renaming");
                            }
                            suffix += 1;
                        }
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
                        let mut suffix: u64 = 0;
                        loop {
                            let new_binding_identifier =
                                format!("{}{}", binding_identifier, suffix);
                            if !value_term.contains(&new_binding_identifier) {
                                value_term.replace(
                                    binding_identifier,
                                    &Self::Identifier(
                                        new_binding_identifier.clone(),
                                        TermDebugContext::Ignore,
                                    ),
                                );
                                *binding_identifier = new_binding_identifier;
                                break;
                            }
                            if suffix == u64::MAX {
                                panic!("Ran out of suffixes for variable renaming");
                            }
                            suffix += 1;
                        }
                    }
                    value_term.replace(identifier, value);
                }
            }
            Self::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.replace(identifier, value);
                if binding_identifier != identifier {
                    if value.contains(binding_identifier) {
                        let mut suffix: u64 = 0;
                        loop {
                            let new_binding_identifier =
                                format!("{}{}", binding_identifier, suffix);
                            if !value_term.contains(&new_binding_identifier) {
                                value_term.replace(
                                    binding_identifier,
                                    &Self::Identifier(
                                        new_binding_identifier.clone(),
                                        TermDebugContext::Ignore,
                                    ),
                                );
                                *binding_identifier = new_binding_identifier;
                                break;
                            }
                            if suffix == u64::MAX {
                                panic!("Ran out of suffixes for variable renaming");
                            }
                            suffix += 1;
                        }
                    }
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
    /// (λx:T.F) P = F[x:=P]
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
            Self::FixedPoint {
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
            Self::FixedPoint {
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

    /// Applies δ-reduction to the greatest extent possible.
    /// Preserves variable names.
    ///
    /// Please note that no type checking is performed.
    ///
    pub fn delta_normalize(self: &mut Self, state: &State) {
        for (name, term) in &state.terms {
            self.replace(name, &term.1);
        }
    }

    fn alpha_normalize_recursive(self: &mut Self, next_suffix: u64) {
        match self {
            Self::Identifier(_, _) => {}
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                function_term.alpha_normalize_recursive(next_suffix);
                parameter_term.alpha_normalize_recursive(next_suffix);
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.alpha_normalize_recursive(next_suffix);
                let new_binding_identifier = format!("#{}", next_suffix);
                value_term.replace(
                    binding_identifier,
                    &Self::Identifier(new_binding_identifier.clone(), TermDebugContext::Ignore),
                );
                *binding_identifier = new_binding_identifier;
                if next_suffix == u64::MAX {
                    panic!("Ran out of suffixes for variable renaming");
                }
                value_term.alpha_normalize_recursive(next_suffix + 1);
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.alpha_normalize_recursive(next_suffix);
                let new_binding_identifier = format!("#{}", next_suffix);
                value_term.replace(
                    binding_identifier,
                    &Self::Identifier(new_binding_identifier.clone(), TermDebugContext::Ignore),
                );
                *binding_identifier = new_binding_identifier;
                if next_suffix == u64::MAX {
                    panic!("Ran out of suffixes for variable renaming");
                }
                value_term.alpha_normalize_recursive(next_suffix + 1);
            }
            Self::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.alpha_normalize_recursive(next_suffix);
                let new_binding_identifier = format!("#{}", next_suffix);
                value_term.replace(
                    binding_identifier,
                    &Self::Identifier(new_binding_identifier.clone(), TermDebugContext::Ignore),
                );
                *binding_identifier = new_binding_identifier;
                if next_suffix == u64::MAX {
                    panic!("Ran out of suffixes for variable renaming");
                }
                value_term.alpha_normalize_recursive(next_suffix + 1);
            }
        }
    }

    /// Applies α-conversion, reassigning variable names systematically.
    ///
    /// Two equivalent terms always become identical after applying
    /// `.delta_normalize()`, `.normalize()` and `.alpha_normalize()` on both.
    ///
    pub fn alpha_normalize(self: &mut Self) {
        self.alpha_normalize_recursive(0)
    }

    /// Applies fixed-point reduction, which transforms an expression
    /// of the form 𝐘x:A.B into (λx:A.B)(𝐘x:A.B).
    ///
    /// If such a reduction is possible, this method will succeed
    /// as many times as it is called. To prevent such behavior,
    /// `.normalize()` should be called before each reduction.
    ///
    pub fn fixed_point_reduce(self: &mut Self, include_inductive: bool) -> bool {
        let self_clone = self.clone();
        if let Self::FixedPoint {
            binding_identifier,
            binding_type,
            value_term,
            debug_context,
        } = self
        {
            let perform = if let Self::Lambda {
                binding_identifier: _,
                binding_type: _,
                value_term: _,
                debug_context: _,
            } = **value_term
            {
                true
            } else {
                false
            };
            if perform || include_inductive {
                *self = Self::Application {
                    function_term: Box::new(Self::Lambda {
                        binding_identifier: binding_identifier.clone(),
                        binding_type: Box::new(*binding_type.clone()),
                        value_term: Box::new(*value_term.clone()),
                        debug_context: debug_context.clone(),
                    }),
                    parameter_term: Box::new(self_clone),
                    debug_context: debug_context.clone(),
                };
                return true;
            }
        }
        match self {
            Self::Identifier(_, _) => false,
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                function_term.fixed_point_reduce(include_inductive)
                    || parameter_term.fixed_point_reduce(include_inductive)
            }
            Self::Lambda {
                binding_identifier: _,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                value_term.fixed_point_reduce(include_inductive)
                    || binding_type.fixed_point_reduce(include_inductive)
            }
            Self::Forall {
                binding_identifier: _,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                value_term.fixed_point_reduce(include_inductive)
                    || binding_type.fixed_point_reduce(include_inductive)
            }
            Self::FixedPoint {
                binding_identifier: _,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                value_term.fixed_point_reduce(include_inductive)
                    || binding_type.fixed_point_reduce(include_inductive)
            }
        }
    }

    /// Applies `.delta_normalize()`, followed by alternating
    /// `.normalize()` and `.fixed_point_reduce()`, and finally
    /// `.alpha_normalize()`.
    ///
    /// Two equivalent terms always become identical after applying
    /// this method on both.
    ///
    /// Please note that no type checking is performed.
    ///
    pub fn full_normalize(self: &mut Self, state: &State) {
        self.delta_normalize(state);
        loop {
            self.normalize();
            if !self.fixed_point_reduce(false) {
                break;
            }
        }
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
            Self::FixedPoint {
                binding_identifier: _,
                binding_type: _,
                value_term: _,
                debug_context,
            } => debug_context,
        }
    }

    fn check_strict_positivity(self: &Self, identifier: &String) -> Result<(), KernelError> {
        let mut current_term = self;
        loop {
            current_term = match current_term {
                Self::Identifier(_, _) => return Ok(()),
                Self::Forall {
                    binding_identifier: _,
                    binding_type,
                    value_term,
                    debug_context: _,
                } => {
                    let mut inner_current_term = binding_type;
                    loop {
                        inner_current_term = match &**inner_current_term {
                            Self::Identifier(_, _) => break,
                            Self::Forall {
                                binding_identifier: _,
                                binding_type: inner_binding_type,
                                value_term: inner_value_term,
                                debug_context: _,
                            } => {
                                if inner_binding_type.contains(identifier) {
                                    return Err(KernelError::NegativeInductiveDefinition {
                                        negative_subterm: *inner_binding_type.clone(),
                                        subterm_context: inner_binding_type
                                            .get_debug_context()
                                            .clone(),
                                        full_term_context: self.get_debug_context().clone(),
                                    });
                                }
                                &inner_value_term
                            }
                            _ => {
                                return Err(KernelError::MisshapenInductiveDefinition {
                                    unexpected_subterm: *inner_current_term.clone(),
                                    subterm_context: inner_current_term.get_debug_context().clone(),
                                    full_term_context: current_term.get_debug_context().clone(),
                                })
                            }
                        }
                    }
                    value_term
                }
                _ => {
                    return Err(KernelError::MisshapenInductiveDefinition {
                        unexpected_subterm: current_term.clone(),
                        subterm_context: current_term.get_debug_context().clone(),
                        full_term_context: self.get_debug_context().clone(),
                    })
                }
            }
        }
    }

    fn check_strictly_decreasing_helper(
        self: &Self,
        index: usize,
        parameter: &String,
        allowed_parameters: &Vec<&String>,
        recursive: &String,
    ) -> bool {
        match self {
            Self::Identifier(s, _) => s != recursive,
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                let mut current_term = self;
                let mut parameter_list = vec![];
                loop {
                    if let Self::Application {
                        function_term: current_function_term,
                        parameter_term: current_parameter_term,
                        debug_context: _,
                    } = current_term
                    {
                        parameter_list.push(current_parameter_term);
                        current_term = current_function_term;
                    } else {
                        break;
                    }
                }
                parameter_list.reverse();
                if let Self::Identifier(s, _) = current_term {
                    if s == recursive {
                        // recursive A1 A2 A3 A4 ...
                        let target_parameter = parameter_list[index];
                        if let Self::Identifier(s2, _) = &**target_parameter {
                            for candidate in allowed_parameters {
                                if &s2 == candidate {
                                    return true;
                                }
                            }
                        }
                        return false;
                    }
                }
                function_term.check_strictly_decreasing_helper(
                    index,
                    parameter,
                    allowed_parameters,
                    recursive,
                ) && parameter_term.check_strictly_decreasing_helper(
                    index,
                    parameter,
                    allowed_parameters,
                    recursive,
                )
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.check_strictly_decreasing_helper(
                    index,
                    parameter,
                    allowed_parameters,
                    recursive,
                ) && if binding_identifier == parameter {
                    value_term.check_strictly_decreasing_helper(
                        index,
                        &"".to_string(),
                        allowed_parameters,
                        recursive,
                    )
                } else if binding_identifier == recursive {
                    true
                } else {
                    for n in 0..allowed_parameters.len() {
                        if binding_identifier == allowed_parameters[n] {
                            let mut new_allowed_parameters = allowed_parameters.clone();
                            new_allowed_parameters.remove(n);
                            return value_term.check_strictly_decreasing_helper(
                                index,
                                &"".to_string(),
                                &new_allowed_parameters,
                                recursive,
                            );
                        }
                    }
                    value_term.check_strictly_decreasing_helper(
                        index,
                        &"".to_string(),
                        allowed_parameters,
                        recursive,
                    )
                }
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.check_strictly_decreasing_helper(
                    index,
                    parameter,
                    allowed_parameters,
                    recursive,
                ) && if binding_identifier == parameter {
                    value_term.check_strictly_decreasing(index, &"".to_string(), recursive)
                } else if binding_identifier == recursive {
                    true
                } else {
                    for n in 0..allowed_parameters.len() {
                        if binding_identifier == allowed_parameters[n] {
                            let mut new_allowed_parameters = allowed_parameters.clone();
                            new_allowed_parameters.remove(n);
                            return value_term.check_strictly_decreasing_helper(
                                index,
                                &"".to_string(),
                                &new_allowed_parameters,
                                recursive,
                            );
                        }
                    }
                    value_term.check_strictly_decreasing_helper(
                        index,
                        &"".to_string(),
                        allowed_parameters,
                        recursive,
                    )
                }
            }
            Self::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.check_strictly_decreasing_helper(
                    index,
                    parameter,
                    allowed_parameters,
                    recursive,
                ) && if binding_identifier == parameter {
                    value_term.check_strictly_decreasing(index, &"".to_string(), recursive)
                } else if binding_identifier == recursive {
                    true
                } else {
                    for n in 0..allowed_parameters.len() {
                        if binding_identifier == allowed_parameters[n] {
                            let mut new_allowed_parameters = allowed_parameters.clone();
                            new_allowed_parameters.remove(n);
                            return value_term.check_strictly_decreasing_helper(
                                index,
                                &"".to_string(),
                                &new_allowed_parameters,
                                recursive,
                            );
                        }
                    }
                    value_term.check_strictly_decreasing_helper(
                        index,
                        &"".to_string(),
                        allowed_parameters,
                        recursive,
                    )
                }
            }
        }
    }

    fn check_strictly_decreasing(
        self: &Self,
        index: usize,
        parameter: &String,
        recursive: &String,
    ) -> bool {
        match self {
            Self::Identifier(s, _) => s != recursive,
            Self::Application {
                function_term,
                parameter_term,
                debug_context: _,
            } => {
                let mut current_term = self;
                let mut parameter_list = vec![];
                loop {
                    if let Self::Application {
                        function_term: current_function_term,
                        parameter_term: current_parameter_term,
                        debug_context: _,
                    } = current_term
                    {
                        parameter_list.push(&**current_parameter_term);
                        current_term = current_function_term;
                    } else {
                        break;
                    }
                }
                if let Self::Identifier(s, _) = current_term {
                    if s == parameter {
                        // parameter A1 A2 A3 A4 ...
                        for sub_parameter in &parameter_list {
                            let mut current_term2 = *sub_parameter;
                            let mut parameter_list2 = vec![];
                            // Ai := λy1:B1.λy2:B2. ... current_term2
                            loop {
                                if let Self::Lambda {
                                    binding_identifier: binding_identifier2,
                                    binding_type: binding_type2,
                                    value_term: value_term2,
                                    debug_context: _,
                                } = current_term2
                                {
                                    if !binding_type2
                                        .check_strictly_decreasing(index, parameter, recursive)
                                    {
                                        return false;
                                    }
                                    parameter_list2.push(binding_identifier2);
                                    current_term2 = &**value_term2;
                                } else {
                                    break;
                                }
                            }
                            // any occurrences of recursive in current_term2
                            // must contain one of parameter_list2 identifiers
                            // as its index-th argument
                            if !current_term2.check_strictly_decreasing_helper(
                                index,
                                parameter,
                                &parameter_list2,
                                recursive,
                            ) {
                                return false;
                            }
                        }
                        return true;
                    }
                }
                function_term.check_strictly_decreasing(index, parameter, recursive)
                    && parameter_term.check_strictly_decreasing(index, parameter, recursive)
            }
            Self::Lambda {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.check_strictly_decreasing(index, parameter, recursive)
                    && if binding_identifier == parameter {
                        value_term.check_strictly_decreasing(index, &"".to_string(), recursive)
                    } else if binding_identifier == recursive {
                        true
                    } else {
                        value_term.check_strictly_decreasing(index, parameter, recursive)
                    }
            }
            Self::Forall {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.check_strictly_decreasing(index, parameter, recursive)
                    && if binding_identifier == parameter {
                        value_term.check_strictly_decreasing(index, &"".to_string(), recursive)
                    } else if binding_identifier == recursive {
                        true
                    } else {
                        value_term.check_strictly_decreasing(index, parameter, recursive)
                    }
            }
            Self::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.check_strictly_decreasing(index, parameter, recursive)
                    && if binding_identifier == parameter {
                        value_term.check_strictly_decreasing(index, &"".to_string(), recursive)
                    } else if binding_identifier == recursive {
                        true
                    } else {
                        value_term.check_strictly_decreasing(index, parameter, recursive)
                    }
            }
        }
    }

    fn infer_type_recursive(
        self: &Self,
        state: &State,
        stack: &mut Vec<(String, Self)>,
    ) -> Result<Self, KernelError> {
        match self {
            Self::Identifier(s, db) => {
                if s == "Set" || s == "Prop" {
                    return Ok(Self::Identifier(
                        "Type(1)".to_string(),
                        TermDebugContext::TypeOf(Box::new(db.clone())),
                    ));
                }
                if s == "?" {
                    return Ok(Self::Identifier(
                        "?".to_string(),
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
                let mut function_type = function_term.infer_type_recursive(state, stack)?;
                if let Self::FixedPoint {
                    binding_identifier,
                    binding_type: _,
                    value_term,
                    debug_context: _,
                } = &function_type
                {
                    let mut new_function_type = *value_term.clone();
                    new_function_type.replace(&binding_identifier, &function_type);
                    function_type = new_function_type;
                }
                match function_type {
                    Self::Forall {
                        binding_identifier,
                        binding_type,
                        value_term,
                        debug_context,
                    } => {
                        let mut parameter_type =
                            parameter_term.infer_type_recursive(state, stack)?;
                        parameter_type.full_normalize(state);
                        let mut expected_parameter_type = binding_type.clone();
                        expected_parameter_type.full_normalize(state);
                        if parameter_type != *expected_parameter_type {
                            let ignore = if let Self::Application {
                                function_term: function_term2,
                                parameter_term: _,
                                debug_context: _,
                            } = &*expected_parameter_type
                            {
                                **function_term2
                                    == Self::Identifier("?".to_string(), debug_context.clone())
                            } else {
                                *expected_parameter_type
                                    == Self::Identifier("?".to_string(), debug_context.clone())
                            };
                            if !ignore {
                                return Err(KernelError::NonmatchingArgument {
                                    expected_type: *expected_parameter_type,
                                    observed_type: parameter_type,
                                    function_context: function_term.get_debug_context().clone(),
                                    parameter_context: parameter_term.get_debug_context().clone(),
                                });
                            }
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
                if let Self::Application {
                    function_term,
                    parameter_term,
                    debug_context: _,
                } = &**binding_type
                {
                    if **function_term == Self::Identifier("?".to_string(), debug_context.clone()) {
                        return Ok(*parameter_term.clone());
                    }
                }
                binding_type.infer_type_recursive(state, stack)?;
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
                binding_type.infer_type_recursive(state, stack)?;
                let mut normalized_binding_type = binding_type.clone();
                // TODO: see below
                normalized_binding_type.full_normalize(state);
                stack.push((binding_identifier.clone(), *normalized_binding_type.clone()));
                if let Self::Identifier(s, _) = *normalized_binding_type {
                    if s == "?" {
                        // ∀x:?.M is a special case.
                        // M is required to contain x only
                        // at strictly positive positions,
                        // and the entire term is of type Set.
                        let mut value_term_clone = value_term.clone();
                        // TODO: this will fail if value_term_clone
                        // contains variables that are bound in an outer
                        // scope but also within the state
                        value_term_clone.full_normalize(state);
                        value_term_clone.check_strict_positivity(binding_identifier)?;
                        stack.pop();
                        return Ok(Self::Identifier(
                            "Set".to_string(),
                            TermDebugContext::TypeOf(Box::new(debug_context.clone())),
                        ));
                    }
                }
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
            Self::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                binding_type.infer_type_recursive(state, stack)?;
                let mut normalized_binding_type = binding_type.clone();
                // TODO: see above
                normalized_binding_type.full_normalize(state);
                stack.push((binding_identifier.clone(), *normalized_binding_type.clone()));
                let inner_type = value_term.infer_type_recursive(state, stack)?;
                let normalized_value_term = value_term.clone();
                //normalized_value_term.full_normalize(state);
                match *normalized_value_term {
                    Self::Lambda {
                        binding_identifier: _,
                        binding_type: _,
                        value_term: _,
                        debug_context: _,
                    } => {
                        // λx1:A1.λx2:A2. ... C
                        // at least one Ai is of type Set
                        // and its xi is applied on a closure
                        // λz1:B1.λz2:B2. ... λyi:Ai.D
                        // such that yi is the ith argument
                        // to any binding_identifier within D
                        let mut current_term = normalized_value_term;
                        let mut parameter_list = vec![];
                        loop {
                            if let Self::Lambda {
                                binding_identifier: current_binding_identifier,
                                binding_type: current_binding_type,
                                value_term: current_value_term,
                                debug_context: _,
                            } = *current_term
                            {
                                parameter_list.push((
                                    current_binding_identifier.clone(),
                                    current_binding_type.clone(),
                                ));
                                current_term = current_value_term;
                            } else {
                                break;
                            }
                        }
                        let mut valid = false;
                        for n in 0..parameter_list.len() {
                            let parameter_type = &parameter_list[n].1;
                            let parameter_type_type =
                                parameter_type.infer_type_recursive(state, stack)?;
                            if let Self::Identifier(s, _) = parameter_type_type {
                                if s == "Set" {
                                    if current_term.check_strictly_decreasing(
                                        n,
                                        &parameter_list[n].0,
                                        binding_identifier,
                                    ) {
                                        for _m in 0..n {
                                            stack.pop();
                                        }
                                        valid = true;
                                        break;
                                    }
                                }
                            }
                            stack.push((parameter_list[n].0.clone(), *parameter_list[n].1.clone()));
                        }
                        if !valid {
                            return Err(KernelError::NonprimitiveRecursiveFunction {
                                full_term_context: self.get_debug_context().clone(),
                            });
                        }
                    }
                    Self::Forall {
                        binding_identifier: _,
                        binding_type: _,
                        value_term: _,
                        debug_context: _,
                    } => {
                        // ∀x1:A1.∀x2:A2. ... C
                        // every Ai can only contain binding_identifier
                        // at strictly positive positions.
                        let mut current_term = normalized_value_term;
                        loop {
                            if let Self::Forall {
                                binding_identifier: _,
                                binding_type: current_binding_type,
                                value_term: current_value_term,
                                debug_context: _,
                            } = *current_term
                            {
                                current_binding_type.check_strict_positivity(binding_identifier)?;
                                current_term = current_value_term;
                            } else {
                                break;
                            }
                        }
                    }
                    _ => {
                        return Err(KernelError::MisshapenRecursiveDefinition {
                            unexpected_subterm: *normalized_value_term.clone(),
                            subterm_context: normalized_value_term.get_debug_context().clone(),
                            full_term_context: self.get_debug_context().clone(),
                        })
                    }
                }
                stack.pop();
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
        // Clear stack afterwards
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
            Term::FixedPoint {
                binding_identifier,
                binding_type,
                value_term,
                debug_context: _,
            } => {
                f.write_str("𝐘")?;
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
        type_term: Term,
        value_term: Term,
    ) -> Result<(), KernelError> {
        let mut type_term_normalized = type_term.clone();
        type_term_normalized.delta_normalize(self);
        type_term_normalized.infer_type(&self)?;
        type_term_normalized.normalize();
        let mut value_term_normalized = value_term.clone();
        value_term_normalized.delta_normalize(self);
        let mut actual_type = value_term_normalized.infer_type(&self)?;
        value_term_normalized.normalize();
        actual_type.full_normalize(self);
        let mut expected_type = type_term_normalized.clone();
        expected_type.full_normalize(self);
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
