use crate::ast::*;
use rooster_kernel::*;

pub fn new_term(expression: &Expression) -> Term {
    match expression {
        Expression::Identifier(s, sp) => {
            Term::Identifier(s.clone(), TermDebugContext::CodeSpan(*sp))
        }
        Expression::Application {
            function_expression,
            parameter_expression,
            span,
        } => Term::Application {
            function_term: Box::new(new_term(function_expression)),
            parameter_term: Box::new(new_term(parameter_expression)),
            debug_context: TermDebugContext::CodeSpan(*span),
        },
        Expression::Lambda {
            binding,
            value_expression,
            span,
        } => Term::Lambda {
            binding_identifier: binding.identifier.clone(),
            binding_type: Box::new(new_term(&binding.type_expression)),
            value_term: Box::new(new_term(value_expression)),
            debug_context: TermDebugContext::CodeSpan(*span),
        },
        Expression::Forall {
            binding,
            value_expression,
            span,
        } => Term::Forall {
            binding_identifier: binding.identifier.clone(),
            binding_type: Box::new(new_term(&binding.type_expression)),
            value_term: Box::new(new_term(value_expression)),
            debug_context: TermDebugContext::CodeSpan(*span),
        },
        Expression::FixedPoint {
            binding,
            value_expression,
            span,
        } => Term::FixedPoint {
            binding_identifier: binding.identifier.clone(),
            binding_type: Box::new(new_term(&binding.type_expression)),
            value_term: Box::new(new_term(value_expression)),
            debug_context: TermDebugContext::CodeSpan(*span),
        },
    }
}

pub fn update_state(state: &mut State, statement: &Statement) -> Result<(), KernelError> {
    match statement {
        Statement::Definition {
            identifier,
            type_expression,
            value_expression,
            span: _,
        } => {
            let mut type_term = new_term(type_expression);
            let mut value_term = new_term(value_expression);
            state.try_define(identifier, type_term.clone(), value_term.clone())?;
            value_term.normalize();
            type_term.normalize();
            println!(
                "{} = {:?}\n    :{:?}",
                identifier.clone(),
                value_term,
                type_term
            );
        }
    }
    Ok(())
}

pub fn execute(input: &Vec<Statement>) -> Result<(), KernelError> {
    let mut state = State::new();
    for statement in input {
        update_state(&mut state, statement)?;
    }
    Ok(())
}
