//! Elaborated MLTT syntax.
//!
//! Variables are de Bruijn indices: index zero names the nearest enclosing
//! term binder.  Interval syntax will live in its own module and namespace.

use std::rc::Rc;

pub type Term = Rc<Expr>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(usize),
    /// A resolved global name. Name resolution is an untrusted front-end task.
    Global(String),
    Universe(u32),
    Pi {
        domain: Term,
        codomain: Term,
    },
    Lam(Term),
    App {
        function: Term,
        argument: Term,
    },
    Sigma {
        first: Term,
        second: Term,
    },
    Pair {
        first: Term,
        second: Term,
    },
    Fst(Term),
    Snd(Term),
    Nat,
    Zero,
    Succ(Term),
}

pub fn var(index: usize) -> Term {
    Rc::new(Expr::Var(index))
}
pub fn global(name: impl Into<String>) -> Term {
    Rc::new(Expr::Global(name.into()))
}
pub fn universe(level: u32) -> Term {
    Rc::new(Expr::Universe(level))
}
pub fn pi(domain: Term, codomain: Term) -> Term {
    Rc::new(Expr::Pi { domain, codomain })
}
pub fn lam(body: Term) -> Term {
    Rc::new(Expr::Lam(body))
}
pub fn app(function: Term, argument: Term) -> Term {
    Rc::new(Expr::App { function, argument })
}
pub fn sigma(first: Term, second: Term) -> Term {
    Rc::new(Expr::Sigma { first, second })
}
pub fn pair(first: Term, second: Term) -> Term {
    Rc::new(Expr::Pair { first, second })
}
pub fn nat() -> Term {
    Rc::new(Expr::Nat)
}
pub fn zero() -> Term {
    Rc::new(Expr::Zero)
}
pub fn succ(term: Term) -> Term {
    Rc::new(Expr::Succ(term))
}
