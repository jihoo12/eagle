//! Errors emitted by the trusted kernel.

use crate::Term;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    UnboundVariable(usize),
    ExpectedFunction,
    ExpectedPair,
    ExpectedType,
    TypeMismatch {
        expected: Term,
        found: Term,
    },
    CannotInferLambda,
    /// A configured evaluator or quotation budget was exhausted.
    OutOfFuel,
    InvalidInductive(&'static str),
}
