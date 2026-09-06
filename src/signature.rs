//! Persistent global declaration registry.
//!
//! This is the trusted admission boundary for closed definitions and the
//! structural registry for inductive declarations.  Global references and
//! inductive eliminators are deliberately not admitted into core terms until
//! their evaluation rules are implemented.

use std::rc::Rc;

use crate::{check, infer, ConstructorDecl, Expr, InductiveDecl, KernelError, Term};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Definition {
    /// A declaration without a body.  It is opaque to future evaluation.
    Opaque { name: String, ty: Term },
    /// A checked definition whose body may eventually be unfolded by NbE.
    Transparent { name: String, ty: Term, body: Term },
}

impl Definition {
    pub fn name(&self) -> &str {
        match self {
            Self::Opaque { name, .. } | Self::Transparent { name, .. } => name,
        }
    }

    pub fn ty(&self) -> &Term {
        match self {
            Self::Opaque { ty, .. } | Self::Transparent { ty, .. } => ty,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration {
    Definition(Definition),
    Inductive(InductiveDecl),
}

impl Declaration {
    pub fn name(&self) -> &str {
        match self {
            Self::Definition(definition) => definition.name(),
            Self::Inductive(inductive) => &inductive.name,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Signature {
    head: Option<Rc<Entry>>,
    len: usize,
}

#[derive(Debug)]
struct Entry {
    declaration: Declaration,
    previous: Option<Rc<Entry>>,
}

impl Signature {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn get(&self, name: &str) -> Option<&Declaration> {
        let mut entry = self.head.as_deref();
        while let Some(current) = entry {
            if current.declaration.name() == name {
                return Some(&current.declaration);
            }
            entry = current.previous.as_deref();
        }
        None
    }

    /// Find a constructor and the inductive declaration that owns it.
    pub fn constructor(&self, name: &str) -> Option<(&InductiveDecl, &ConstructorDecl)> {
        let mut entry = self.head.as_deref();
        while let Some(current) = entry {
            let constructor = match &current.declaration {
                Declaration::Inductive(inductive) => inductive
                    .constructors
                    .iter()
                    .find(|constructor| constructor.name == name)
                    .map(|constructor| (inductive, constructor)),
                Declaration::Definition(_) => None,
            };
            if let Some(constructor) = constructor {
                return Some(constructor);
            }
            entry = current.previous.as_deref();
        }
        None
    }

    /// Look up an inductive declaration by its type constructor name.
    pub fn inductive(&self, name: &str) -> Option<&InductiveDecl> {
        match self.get(name) {
            Some(Declaration::Inductive(inductive)) => Some(inductive),
            Some(Declaration::Definition(_)) | None => None,
        }
    }

    fn contains_name(&self, name: &str) -> bool {
        let mut entry = self.head.as_deref();
        while let Some(current) = entry {
            if current.declaration.name() == name {
                return true;
            }
            let has_constructor = match &current.declaration {
                Declaration::Inductive(inductive) => inductive
                    .constructors
                    .iter()
                    .any(|constructor| constructor.name == name),
                Declaration::Definition(_) => false,
            };
            if has_constructor {
                return true;
            }
            entry = current.previous.as_deref();
        }
        false
    }

    /// Validate `declaration` and return a new signature that shares this
    /// signature as its tail.  The original signature is unchanged.
    pub fn insert(&self, declaration: Declaration) -> Result<Self, KernelError> {
        validate_declaration(&declaration)?;
        if self.contains_name(declaration.name()) {
            return Err(KernelError::DuplicateDeclaration(
                declaration.name().to_owned(),
            ));
        }
        if let Declaration::Inductive(inductive) = &declaration {
            for constructor in &inductive.constructors {
                if self.contains_name(&constructor.name)
                    || constructor.name == inductive.name
                    || inductive
                        .constructors
                        .iter()
                        .filter(|other| other.name == constructor.name)
                        .nth(1)
                        .is_some()
                {
                    return Err(KernelError::DuplicateDeclaration(constructor.name.clone()));
                }
            }
        }
        Ok(Self {
            head: Some(Rc::new(Entry {
                declaration,
                previous: self.head.clone(),
            })),
            len: self.len + 1,
        })
    }
}

fn validate_name(name: &str) -> Result<(), KernelError> {
    if name.is_empty() {
        Err(KernelError::InvalidDeclaration(
            "declaration names must not be empty".into(),
        ))
    } else {
        Ok(())
    }
}

fn validate_type(ty: &Term) -> Result<(), KernelError> {
    match infer(ty)?.as_ref() {
        Expr::Universe(_) => Ok(()),
        _ => Err(KernelError::InvalidDeclaration(
            "a declaration type must itself be a type".into(),
        )),
    }
}

fn validate_declaration(declaration: &Declaration) -> Result<(), KernelError> {
    validate_name(declaration.name())?;
    match declaration {
        Declaration::Definition(Definition::Opaque { ty, .. }) => validate_type(ty),
        Declaration::Definition(Definition::Transparent { ty, body, .. }) => {
            validate_type(ty)?;
            check(body, ty)
        }
        Declaration::Inductive(inductive) => {
            inductive.validate_shape()?;
            check_strict_positivity(inductive)?;
            // The executable constructor fragment currently has closed fields.
            // Keeping this restriction at admission avoids accepting a
            // dependent telescope whose constructor type cannot yet be formed.
            if !inductive.params.is_empty() || !inductive.indices.is_empty() {
                return Err(KernelError::InvalidDeclaration(
                    "inductive parameters and indices are not implemented yet".into(),
                ));
            }
            for constructor in &inductive.constructors {
                for field in &constructor.fields {
                    validate_type(&field.ty)?;
                }
            }
            Ok(())
        }
    }
}

/// Conservative strict-positivity check for the recursive name in constructor
/// fields.  An occurrence left of a Pi arrow is negative; occurrences in a
/// codomain, Sigma component, pair, or ordinary application retain polarity.
/// The executable fragment still rejects recursive declarations afterward,
/// because it does not yet have inductive applications/eliminators; running
/// this check first ensures an eventual extension cannot accidentally admit a
/// known-negative occurrence.
fn check_strict_positivity(inductive: &InductiveDecl) -> Result<(), KernelError> {
    for constructor in &inductive.constructors {
        for field in &constructor.fields {
            check_positive_term(&field.ty, &inductive.name, true)?;
        }
    }
    Ok(())
}

fn check_positive_term(
    term: &Term,
    inductive_name: &str,
    positive: bool,
) -> Result<(), KernelError> {
    match term.as_ref() {
        Expr::Global(name) if name == inductive_name && !positive => Err(
            KernelError::NonPositiveOccurrence(inductive_name.to_owned()),
        ),
        Expr::Pi { domain, codomain } => {
            check_positive_term(domain, inductive_name, !positive)?;
            check_positive_term(codomain, inductive_name, positive)
        }
        Expr::Sigma { first, second }
        | Expr::App {
            function: first,
            argument: second,
        }
        | Expr::Pair { first, second } => {
            check_positive_term(first, inductive_name, positive)?;
            check_positive_term(second, inductive_name, positive)
        }
        Expr::Lam(body) | Expr::Fst(body) | Expr::Snd(body) | Expr::Succ(body) => {
            check_positive_term(body, inductive_name, positive)
        }
        Expr::Var(_) | Expr::Global(_) | Expr::Universe(_) | Expr::Nat | Expr::Zero => Ok(()),
    }
}
