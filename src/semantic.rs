//! Semantic values, neutrals, closures, and persistent environments for NbE.

use std::fmt;
use std::rc::Rc;

use crate::{zero, Expr, Term};

pub type Value = Rc<Val>;

#[derive(Clone)]
pub enum Val {
    Universe(u32),
    Pi(Value, Closure),
    Sigma(Value, Closure),
    Lam(Closure),
    Nat,
    Zero,
    Succ(Value),
    Pair(Value, Value),
    Neutral(Neutral),
}

impl fmt::Debug for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Universe(n) => write!(f, "Type({n})"),
            Self::Pi(..) => write!(f, "Pi(..)"),
            Self::Sigma(..) => write!(f, "Sigma(..)"),
            Self::Lam(..) => write!(f, "Lam(..)"),
            Self::Nat => write!(f, "Nat"),
            Self::Zero => write!(f, "zero"),
            Self::Succ(v) => f.debug_tuple("succ").field(v).finish(),
            Self::Pair(a, b) => f.debug_tuple("pair").field(a).field(b).finish(),
            Self::Neutral(n) => n.fmt(f),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Closure {
    pub(crate) env: Env,
    pub(crate) body: Term,
}

/// A persistent environment. `extend` allocates one node and shares its tail;
/// closure capture is therefore an O(1) clone of the environment handle.
#[derive(Clone, Debug, Default)]
pub(crate) struct Env {
    pub(crate) head: Option<Rc<EnvNode>>,
    pub(crate) len: usize,
}
#[derive(Debug)]
pub(crate) struct EnvNode {
    pub(crate) value: Value,
    pub(crate) previous: Option<Rc<EnvNode>>,
}
impl Env {
    pub(crate) fn extend(&self, value: Value) -> Self {
        Self {
            head: Some(Rc::new(EnvNode {
                value,
                previous: self.head.clone(),
            })),
            len: self.len + 1,
        }
    }
    /// De Bruijn index lookup: zero denotes the most recent binder.
    pub(crate) fn get(&self, index: usize) -> Option<Value> {
        let mut node = self.head.as_ref()?;
        for _ in 0..index {
            node = node.previous.as_ref()?;
        }
        Some(node.value.clone())
    }
}

#[derive(Clone, Debug)]
pub enum Neutral {
    Var(usize),
    App(Rc<Neutral>, Value),
    Fst(Rc<Neutral>),
    Snd(Rc<Neutral>),
}

// `Rc` only avoids recursive destruction when a shared tail remains.  These
// destructors drain uniquely-owned chains explicitly, keeping normal teardown
// of stress-sized syntax, values, and environments off the native stack.
impl Drop for EnvNode {
    fn drop(&mut self) {
        let mut next = self.previous.take();
        while let Some(node) = next {
            match Rc::try_unwrap(node) {
                Ok(mut node) => next = node.previous.take(),
                Err(_) => break,
            }
        }
    }
}

pub(crate) fn take_expr_children(expr: &mut Expr, work: &mut Vec<Term>) {
    let empty = || Rc::new(Expr::Zero);
    match expr {
        Expr::Pi { domain, codomain }
        | Expr::Sigma {
            first: domain,
            second: codomain,
        } => {
            work.push(std::mem::replace(domain, empty()));
            work.push(std::mem::replace(codomain, empty()));
        }
        Expr::Lam(body) | Expr::Fst(body) | Expr::Snd(body) | Expr::Succ(body) => {
            work.push(std::mem::replace(body, empty()))
        }
        Expr::App { function, argument }
        | Expr::Pair {
            first: function,
            second: argument,
        } => {
            work.push(std::mem::replace(function, empty()));
            work.push(std::mem::replace(argument, empty()));
        }
        Expr::Var(_) | Expr::Universe(_) | Expr::Nat | Expr::Zero => {}
    }
}
impl Drop for Expr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_expr_children(self, &mut work);
        while let Some(node) = work.pop() {
            if let Ok(mut node) = Rc::try_unwrap(node) {
                take_expr_children(&mut node, &mut work);
            }
        }
    }
}
fn take_val_children(value: &mut Val, work: &mut Vec<Value>) {
    match value {
        Val::Pi(domain, closure) | Val::Sigma(domain, closure) => {
            work.push(std::mem::replace(domain, Rc::new(Val::Zero)));
            closure.env = Env::default();
            let body = std::mem::replace(&mut closure.body, zero());
            drop(body);
        }
        Val::Lam(closure) => {
            closure.env = Env::default();
            let body = std::mem::replace(&mut closure.body, zero());
            drop(body);
        }
        Val::Succ(inner) => work.push(std::mem::replace(inner, Rc::new(Val::Zero))),
        Val::Pair(a, b) => {
            work.push(std::mem::replace(a, Rc::new(Val::Zero)));
            work.push(std::mem::replace(b, Rc::new(Val::Zero)));
        }
        Val::Universe(_) | Val::Nat | Val::Zero | Val::Neutral(_) => {}
    }
}
impl Drop for Val {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_val_children(self, &mut work);
        while let Some(node) = work.pop() {
            if let Ok(mut node) = Rc::try_unwrap(node) {
                take_val_children(&mut node, &mut work);
            }
        }
    }
}
fn take_neutral_head(neutral: &mut Neutral) -> Option<Rc<Neutral>> {
    match neutral {
        Neutral::Var(_) => None,
        Neutral::App(head, argument) => {
            drop(std::mem::replace(argument, Rc::new(Val::Zero)));
            Some(std::mem::replace(head, Rc::new(Neutral::Var(0))))
        }
        Neutral::Fst(head) | Neutral::Snd(head) => {
            Some(std::mem::replace(head, Rc::new(Neutral::Var(0))))
        }
    }
}
impl Drop for Neutral {
    fn drop(&mut self) {
        let mut next = take_neutral_head(self);
        while let Some(node) = next {
            match Rc::try_unwrap(node) {
                Ok(mut node) => next = take_neutral_head(&mut node),
                Err(_) => break,
            }
        }
    }
}
