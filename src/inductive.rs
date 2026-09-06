//! Inductive declaration syntax and structural validation.

use crate::{KernelError, Term};

/// A binder in an inductive declaration.  Parameters are fixed for every
/// constructor/result; indices may vary and are the inputs to elimination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binder {
    pub name: String,
    pub ty: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorDecl {
    pub name: String,
    pub fields: Vec<Binder>,
    /// The result's index arguments, one for each `InductiveDecl::indices`.
    pub result_indices: Vec<Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveDecl {
    pub name: String,
    pub params: Vec<Binder>,
    pub indices: Vec<Binder>,
    pub universe: u32,
    pub constructors: Vec<ConstructorDecl>,
}

impl InductiveDecl {
    /// Structural validation owned by the trusted declaration boundary.  Full
    /// positivity and constructor type checking belong to the next kernel step.
    pub fn validate_shape(&self) -> Result<(), KernelError> {
        if self.constructors.is_empty() {
            return Err(KernelError::InvalidInductive(
                "an inductive needs a constructor",
            ));
        }
        if self
            .params
            .iter()
            .chain(&self.indices)
            .any(|b| b.name.is_empty())
        {
            return Err(KernelError::InvalidInductive("binders need names"));
        }
        if self.name.is_empty() {
            return Err(KernelError::InvalidInductive("inductive names need names"));
        }
        if self
            .constructors
            .iter()
            .any(|constructor| constructor.name.is_empty())
        {
            return Err(KernelError::InvalidInductive("constructors need names"));
        }
        if self
            .constructors
            .iter()
            .enumerate()
            .any(|(index, constructor)| {
                self.constructors[index + 1..]
                    .iter()
                    .any(|other| other.name == constructor.name)
            })
        {
            return Err(KernelError::InvalidInductive(
                "constructor names must be distinct",
            ));
        }
        if self
            .constructors
            .iter()
            .any(|c| c.result_indices.len() != self.indices.len())
        {
            return Err(KernelError::InvalidInductive(
                "constructor result has the wrong number of indices",
            ));
        }
        Ok(())
    }
}
