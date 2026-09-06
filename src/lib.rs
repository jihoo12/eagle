#![forbid(unsafe_code)]
//! Eagle's deliberately small MLTT kernel.
//!
//! Syntax uses de Bruijn *indices*; semantic neutrals use de Bruijn *levels*.
//! Both syntax and semantic values are `Rc` allocated. See
//! `docs/core-language.md` for the current core-language contract and
//! `docs/cubical-extension.md` for the separate dimension-context plan.

use std::rc::Rc;

use semantic::Env;

mod error;
mod inductive;
mod semantic;
mod signature;
mod syntax;

pub use error::KernelError;
pub use inductive::{Binder, ConstructorDecl, InductiveDecl};
pub use semantic::{Closure, Neutral, Val, Value};
pub use signature::{Declaration, Definition, Signature};
pub use syntax::{app, global, lam, nat, pair, pi, sigma, succ, universe, var, zero, Expr, Term};

/// Evaluation uses a heap-allocated CEK-style work stack and explicit fuel.
/// Well-typed MLTT terms normalize; fuel makes the remaining CPU policy explicit.
#[derive(Clone, Copy, Debug)]
pub struct EvalConfig {
    pub fuel: usize,
}
impl Default for EvalConfig {
    fn default() -> Self {
        Self { fuel: 100_000 }
    }
}

struct Evaluator<'signature> {
    remaining: usize,
    signature: Option<&'signature Signature>,
}
enum EvalFrame {
    AppArgument { argument: Term, env: Env },
    Apply(Value),
    Pi { codomain: Term, env: Env },
    Sigma { second: Term, env: Env },
    PairSecond { second: Term, env: Env },
    MakePair(Value),
    Fst,
    Snd,
    Succ,
}
impl Evaluator<'_> {
    fn tick(&mut self) -> Result<(), KernelError> {
        if self.remaining == 0 {
            Err(KernelError::OutOfFuel)
        } else {
            self.remaining -= 1;
            Ok(())
        }
    }
    fn eval(&mut self, term: &Term, env: &Env) -> Result<Value, KernelError> {
        // A CEK-like heap work stack keeps arbitrary term nesting off the native stack.
        let mut current = Some((term.clone(), env.clone()));
        let mut value = None;
        let mut frames = Vec::new();
        loop {
            if let Some((term, env)) = current.take() {
                self.tick()?;
                match term.as_ref() {
                    Expr::Var(i) => {
                        value = Some(env.get(*i).ok_or(KernelError::UnboundVariable(*i))?)
                    }
                    Expr::Global(name) => match self
                        .signature
                        .and_then(|signature| signature.get(name))
                    {
                        Some(Declaration::Definition(Definition::Transparent { body, .. })) => {
                            current = Some((body.clone(), env));
                        }
                        Some(Declaration::Definition(Definition::Opaque { .. }))
                        | Some(Declaration::Inductive(_)) => {
                            value = Some(Rc::new(Val::Neutral(Neutral::Global(name.clone()))));
                        }
                        None if self
                            .signature
                            .and_then(|signature| signature.constructor(name))
                            .is_some() =>
                        {
                            value = Some(Rc::new(Val::Neutral(Neutral::Global(name.clone()))));
                        }
                        None => return Err(KernelError::UnknownGlobal(name.clone())),
                    },
                    Expr::Universe(i) => value = Some(Rc::new(Val::Universe(*i))),
                    Expr::Lam(body) => {
                        value = Some(Rc::new(Val::Lam(Closure {
                            env,
                            body: body.clone(),
                        })))
                    }
                    Expr::Nat => value = Some(Rc::new(Val::Nat)),
                    Expr::Zero => value = Some(Rc::new(Val::Zero)),
                    Expr::Pi { domain, codomain } => {
                        frames.push(EvalFrame::Pi {
                            codomain: codomain.clone(),
                            env: env.clone(),
                        });
                        current = Some((domain.clone(), env));
                    }
                    Expr::Sigma { first, second } => {
                        frames.push(EvalFrame::Sigma {
                            second: second.clone(),
                            env: env.clone(),
                        });
                        current = Some((first.clone(), env));
                    }
                    Expr::App { function, argument } => {
                        frames.push(EvalFrame::AppArgument {
                            argument: argument.clone(),
                            env: env.clone(),
                        });
                        current = Some((function.clone(), env));
                    }
                    Expr::Pair { first, second } => {
                        frames.push(EvalFrame::PairSecond {
                            second: second.clone(),
                            env: env.clone(),
                        });
                        current = Some((first.clone(), env));
                    }
                    Expr::Fst(pair) => {
                        frames.push(EvalFrame::Fst);
                        current = Some((pair.clone(), env));
                    }
                    Expr::Snd(pair) => {
                        frames.push(EvalFrame::Snd);
                        current = Some((pair.clone(), env));
                    }
                    Expr::Succ(inner) => {
                        frames.push(EvalFrame::Succ);
                        current = Some((inner.clone(), env));
                    }
                }
                continue;
            }
            let result = value.take().expect("machine has a value after a term");
            match frames.pop() {
                None => return Ok(result),
                Some(EvalFrame::AppArgument { argument, env }) => {
                    frames.push(EvalFrame::Apply(result));
                    current = Some((argument, env));
                }
                Some(EvalFrame::Apply(function)) => match function.as_ref() {
                    Val::Lam(closure) => {
                        current = Some((closure.body.clone(), closure.env.extend(result)))
                    }
                    Val::Neutral(neutral) => {
                        value = Some(Rc::new(Val::Neutral(Neutral::App(
                            Rc::new(neutral.clone()),
                            result,
                        ))))
                    }
                    _ => return Err(KernelError::ExpectedFunction),
                },
                Some(EvalFrame::Pi { codomain, env }) => {
                    value = Some(Rc::new(Val::Pi(
                        result,
                        Closure {
                            env,
                            body: codomain,
                        },
                    )))
                }
                Some(EvalFrame::Sigma { second, env }) => {
                    value = Some(Rc::new(Val::Sigma(result, Closure { env, body: second })))
                }
                Some(EvalFrame::PairSecond { second, env }) => {
                    frames.push(EvalFrame::MakePair(result));
                    current = Some((second, env));
                }
                Some(EvalFrame::MakePair(first)) => value = Some(Rc::new(Val::Pair(first, result))),
                Some(EvalFrame::Fst) => value = Some(self.fst(result)?),
                Some(EvalFrame::Snd) => value = Some(self.snd(result)?),
                Some(EvalFrame::Succ) => value = Some(Rc::new(Val::Succ(result))),
            }
        }
    }
    fn close(&mut self, c: &Closure, arg: Value) -> Result<Value, KernelError> {
        self.eval(&c.body, &c.env.extend(arg))
    }
    fn fst(&mut self, value: Value) -> Result<Value, KernelError> {
        match value.as_ref() {
            Val::Pair(a, _) => Ok(a.clone()),
            Val::Neutral(n) => Ok(Rc::new(Val::Neutral(Neutral::Fst(Rc::new(n.clone()))))),
            _ => Err(KernelError::ExpectedPair),
        }
    }
    fn snd(&mut self, value: Value) -> Result<Value, KernelError> {
        match value.as_ref() {
            Val::Pair(_, b) => Ok(b.clone()),
            Val::Neutral(n) => Ok(Rc::new(Val::Neutral(Neutral::Snd(Rc::new(n.clone()))))),
            _ => Err(KernelError::ExpectedPair),
        }
    }
}

pub fn eval(term: &Term, config: EvalConfig) -> Result<Value, KernelError> {
    Evaluator {
        remaining: config.fuel,
        signature: None,
    }
    .eval(term, &Env::default())
}

/// Evaluate a closed core term with resolved global names from `signature`.
/// Transparent definitions unfold; opaque definitions and inductive names stay
/// neutral until their core computation rules are available.
pub fn eval_in_signature(
    term: &Term,
    signature: &Signature,
    config: EvalConfig,
) -> Result<Value, KernelError> {
    Evaluator {
        remaining: config.fuel,
        signature: Some(signature),
    }
    .eval(term, &Env::default())
}

enum QuoteTask {
    Value(Value, usize),
    Neutral(Rc<Neutral>, usize),
}
enum QuoteFrame {
    PiBody { closure: Closure, level: usize },
    SigmaBody { closure: Closure, level: usize },
    MakePi(Term),
    MakeSigma(Term),
    MakeLam,
    PairSecond { second: Value, level: usize },
    MakePair(Term),
    MakeSucc,
    NeutralAppArgument { argument: Value, level: usize },
    MakeApp(Term),
    MakeFst,
    MakeSnd,
}

/// Reification is an explicit heap machine, parallel to `Evaluator`; it never
/// uses one Rust frame per value/neutral constructor.
fn quote_task(initial: QuoteTask, config: EvalConfig) -> Result<Term, KernelError> {
    let mut task = Some(initial);
    let mut result = None;
    let mut frames = Vec::new();
    let mut ev = Evaluator {
        remaining: config.fuel,
        signature: None,
    };
    loop {
        if let Some(task_now) = task.take() {
            match task_now {
                QuoteTask::Value(value, level) => match value.as_ref() {
                    Val::Universe(i) => result = Some(universe(*i)),
                    Val::Nat => result = Some(nat()),
                    Val::Zero => result = Some(zero()),
                    Val::Succ(inner) => {
                        frames.push(QuoteFrame::MakeSucc);
                        task = Some(QuoteTask::Value(inner.clone(), level));
                    }
                    Val::Pi(domain, closure) => {
                        frames.push(QuoteFrame::PiBody {
                            closure: closure.clone(),
                            level,
                        });
                        task = Some(QuoteTask::Value(domain.clone(), level));
                    }
                    Val::Sigma(first, closure) => {
                        frames.push(QuoteFrame::SigmaBody {
                            closure: closure.clone(),
                            level,
                        });
                        task = Some(QuoteTask::Value(first.clone(), level));
                    }
                    Val::Lam(closure) => {
                        let x = Rc::new(Val::Neutral(Neutral::Var(level)));
                        frames.push(QuoteFrame::MakeLam);
                        task = Some(QuoteTask::Value(ev.close(closure, x)?, level + 1));
                    }
                    Val::Pair(first, second) => {
                        frames.push(QuoteFrame::PairSecond {
                            second: second.clone(),
                            level,
                        });
                        task = Some(QuoteTask::Value(first.clone(), level));
                    }
                    Val::Neutral(neutral) => {
                        task = Some(QuoteTask::Neutral(Rc::new(neutral.clone()), level))
                    }
                },
                QuoteTask::Neutral(neutral, level) => match neutral.as_ref() {
                    Neutral::Var(l) => {
                        result = Some(var(level
                            .checked_sub(*l + 1)
                            .ok_or(KernelError::UnboundVariable(*l))?))
                    }
                    Neutral::Global(name) => result = Some(global(name.clone())),
                    Neutral::App(function, argument) => {
                        frames.push(QuoteFrame::NeutralAppArgument {
                            argument: argument.clone(),
                            level,
                        });
                        task = Some(QuoteTask::Neutral(function.clone(), level));
                    }
                    Neutral::Fst(pair) => {
                        frames.push(QuoteFrame::MakeFst);
                        task = Some(QuoteTask::Neutral(pair.clone(), level));
                    }
                    Neutral::Snd(pair) => {
                        frames.push(QuoteFrame::MakeSnd);
                        task = Some(QuoteTask::Neutral(pair.clone(), level));
                    }
                },
            }
            continue;
        }
        let term = result
            .take()
            .expect("quote machine has a term after a task");
        match frames.pop() {
            None => return Ok(term),
            Some(QuoteFrame::PiBody { closure, level }) => {
                let x = Rc::new(Val::Neutral(Neutral::Var(level)));
                frames.push(QuoteFrame::MakePi(term));
                task = Some(QuoteTask::Value(ev.close(&closure, x)?, level + 1));
            }
            Some(QuoteFrame::SigmaBody { closure, level }) => {
                let x = Rc::new(Val::Neutral(Neutral::Var(level)));
                frames.push(QuoteFrame::MakeSigma(term));
                task = Some(QuoteTask::Value(ev.close(&closure, x)?, level + 1));
            }
            Some(QuoteFrame::MakePi(domain)) => result = Some(pi(domain, term)),
            Some(QuoteFrame::MakeSigma(first)) => result = Some(sigma(first, term)),
            Some(QuoteFrame::MakeLam) => result = Some(lam(term)),
            Some(QuoteFrame::PairSecond { second, level }) => {
                frames.push(QuoteFrame::MakePair(term));
                task = Some(QuoteTask::Value(second, level));
            }
            Some(QuoteFrame::MakePair(first)) => result = Some(pair(first, term)),
            Some(QuoteFrame::MakeSucc) => result = Some(succ(term)),
            Some(QuoteFrame::NeutralAppArgument { argument, level }) => {
                frames.push(QuoteFrame::MakeApp(term));
                task = Some(QuoteTask::Value(argument, level));
            }
            Some(QuoteFrame::MakeApp(function)) => result = Some(app(function, term)),
            Some(QuoteFrame::MakeFst) => result = Some(Rc::new(Expr::Fst(term))),
            Some(QuoteFrame::MakeSnd) => result = Some(Rc::new(Expr::Snd(term))),
        }
    }
}
fn quote(value: &Value, level: usize, config: EvalConfig) -> Result<Term, KernelError> {
    quote_task(QuoteTask::Value(value.clone(), level), config)
}
#[allow(dead_code)]
fn quote_neutral(neutral: &Neutral, level: usize, config: EvalConfig) -> Result<Term, KernelError> {
    quote_task(QuoteTask::Neutral(Rc::new(neutral.clone()), level), config)
}

/// Normalization by evaluation for closed terms.
pub fn normalize(term: &Term) -> Result<Term, KernelError> {
    normalize_with_config(term, EvalConfig::default())
}
/// Normalize a closed term using `config` for evaluation and reification.
///
/// Fuel is a per-machine budget: evaluation and quotation each receive the
/// configured limit. Exhaustion is reported as `KernelError::OutOfFuel`.
pub fn normalize_with_config(term: &Term, config: EvalConfig) -> Result<Term, KernelError> {
    quote(&eval(term, config)?, 0, config)
}

/// Normalize a closed term with resolved globals from `signature`.
///
/// This initial global fragment reifies transparent bodies that are already
/// closed and constructor/opaque heads as neutrals.  Quotations that need to
/// apply a closure carrying globals are added with eliminators.
pub fn normalize_in_signature(
    term: &Term,
    signature: &Signature,
    config: EvalConfig,
) -> Result<Term, KernelError> {
    quote(&eval_in_signature(term, signature, config)?, 0, config)
}

#[derive(Clone, Default)]
struct Context<'signature> {
    types: Env,
    values: Env,
    config: EvalConfig,
    signature: Option<&'signature Signature>,
}
impl Context<'_> {
    fn extend(&self, ty: Value) -> Self {
        Self {
            types: self.types.extend(ty),
            values: self
                .values
                .extend(Rc::new(Val::Neutral(Neutral::Var(self.values.len)))),
            config: self.config,
            signature: self.signature,
        }
    }
    fn eval(&self, term: &Term) -> Result<Value, KernelError> {
        Evaluator {
            remaining: self.config.fuel,
            signature: self.signature,
        }
        .eval(term, &self.values)
    }
}

fn universe_level(value: &Value) -> Result<u32, KernelError> {
    if let Val::Universe(i) = value.as_ref() {
        Ok(*i)
    } else {
        Err(KernelError::ExpectedType)
    }
}
fn same(a: &Value, b: &Value, level: usize, config: EvalConfig) -> Result<bool, KernelError> {
    Ok(quote(a, level, config)? == quote(b, level, config)?)
}
/// MLTT universes are cumulative: a term inhabiting `Type_i` also inhabits
/// `Type_j` whenever `i <= j`. Other conversion remains NbE structural equality.
fn assignable(
    expected: &Value,
    found: &Value,
    level: usize,
    config: EvalConfig,
) -> Result<bool, KernelError> {
    match (expected.as_ref(), found.as_ref()) {
        (Val::Universe(expected_level), Val::Universe(found_level)) => {
            Ok(found_level <= expected_level)
        }
        _ => same(expected, found, level, config),
    }
}
fn mismatch(
    expected: &Value,
    found: &Value,
    level: usize,
    config: EvalConfig,
) -> Result<KernelError, KernelError> {
    Ok(KernelError::TypeMismatch {
        expected: quote(expected, level, config)?,
        found: quote(found, level, config)?,
    })
}

fn infer_in(ctx: &Context<'_>, term: &Term) -> Result<Value, KernelError> {
    // A dependent-type spine has one body binder per layer.  Process the entire
    // Pi/Sigma run on the heap rather than nesting Rust calls per binder.
    let mut cursor = term.clone();
    let mut active = ctx.clone();
    let mut levels = Vec::new();
    loop {
        let (domain, body) = match cursor.as_ref() {
            Expr::Pi { domain, codomain } => (domain.clone(), codomain.clone()),
            Expr::Sigma { first, second } => (first.clone(), second.clone()),
            _ => break,
        };
        let level = universe_level(&infer_in(&active, &domain)?)?;
        let domain_value = active.eval(&domain)?;
        active = active.extend(domain_value);
        levels.push(level);
        cursor = body;
    }
    if !levels.is_empty() {
        let mut level = universe_level(&infer_in(&active, &cursor)?)?;
        for outer in levels {
            level = level.max(outer);
        }
        return Ok(Rc::new(Val::Universe(level)));
    }
    match term.as_ref() {
        Expr::Var(i) => ctx.types.get(*i).ok_or(KernelError::UnboundVariable(*i)),
        Expr::Global(name) => match ctx.signature.and_then(|signature| signature.get(name)) {
            Some(Declaration::Definition(definition)) => ctx.eval(definition.ty()),
            Some(Declaration::Inductive(inductive)) => {
                Ok(Rc::new(Val::Universe(inductive.universe)))
            }
            None => match ctx.signature {
                Some(signature) if signature.constructor(name).is_some() => {
                    ctx.eval(&constructor_type(signature, name)?)
                }
                _ => Err(KernelError::UnknownGlobal(name.clone())),
            },
        },
        Expr::Universe(i) => Ok(Rc::new(Val::Universe(i + 1))),
        Expr::Pi { domain, codomain } => {
            let d_ty = infer_in(ctx, domain)?;
            let dl = universe_level(&d_ty)?;
            let domain_v = ctx.eval(domain)?;
            let c_ty = infer_in(&ctx.extend(domain_v), codomain)?;
            let cl = universe_level(&c_ty)?;
            Ok(Rc::new(Val::Universe(dl.max(cl))))
        }
        Expr::Sigma { first, second } => {
            let f_ty = infer_in(ctx, first)?;
            let fl = universe_level(&f_ty)?;
            let first_v = ctx.eval(first)?;
            let s_ty = infer_in(&ctx.extend(first_v), second)?;
            let sl = universe_level(&s_ty)?;
            Ok(Rc::new(Val::Universe(fl.max(sl))))
        }
        Expr::Lam(_) => Err(KernelError::CannotInferLambda),
        Expr::App { function, argument } => match infer_in(ctx, function)?.as_ref() {
            Val::Pi(domain, codomain) => {
                check_in(ctx, argument, domain)?;
                let arg = ctx.eval(argument)?;
                Evaluator {
                    remaining: ctx.config.fuel,
                    signature: ctx.signature,
                }
                .close(codomain, arg)
            }
            _ => Err(KernelError::ExpectedFunction),
        },
        Expr::Pair { .. } => Err(KernelError::CannotInferLambda),
        Expr::Fst(p) => match infer_in(ctx, p)?.as_ref() {
            Val::Sigma(first, _) => Ok(first.clone()),
            _ => Err(KernelError::ExpectedPair),
        },
        Expr::Snd(p) => match infer_in(ctx, p)?.as_ref() {
            Val::Sigma(_, second) => {
                let p = ctx.eval(p)?;
                let first = Evaluator {
                    remaining: ctx.config.fuel,
                    signature: ctx.signature,
                }
                .fst(p)?;
                Evaluator {
                    remaining: ctx.config.fuel,
                    signature: ctx.signature,
                }
                .close(second, first)
            }
            _ => Err(KernelError::ExpectedPair),
        },
        Expr::Nat => Ok(Rc::new(Val::Universe(0))),
        Expr::Zero => Ok(Rc::new(Val::Nat)),
        Expr::Succ(n) => {
            let mut base = n.clone();
            while let Expr::Succ(next) = base.as_ref() {
                base = next.clone();
            }
            check_in(ctx, &base, &Rc::new(Val::Nat))?;
            Ok(Rc::new(Val::Nat))
        }
    }
}

/// Construct the type of a zero-parameter, zero-index constructor from its
/// field telescope.  The current declaration boundary accepts only closed
/// field types, so this produces a closed Pi telescope.  Dependent fields,
/// parameters, and indices are admitted together in the next declaration
/// checker extension rather than being partially and unsafely approximated.
fn constructor_type(signature: &Signature, name: &str) -> Result<Term, KernelError> {
    let (inductive, constructor) = signature
        .constructor(name)
        .ok_or_else(|| KernelError::UnknownGlobal(name.to_owned()))?;
    if !inductive.params.is_empty() || !inductive.indices.is_empty() {
        return Err(KernelError::UnsupportedGlobal(name.to_owned()));
    }
    let mut ty = global(inductive.name.clone());
    for field in constructor.fields.iter().rev() {
        ty = pi(field.ty.clone(), ty);
    }
    Ok(ty)
}

fn check_in(ctx: &Context<'_>, term: &Term, expected: &Value) -> Result<(), KernelError> {
    match (term.as_ref(), expected.as_ref()) {
        (Expr::Lam(body), Val::Pi(domain, codomain)) => {
            let extended = ctx.extend(domain.clone());
            let x = extended
                .values
                .get(0)
                .expect("extended context has its binder");
            check_in(
                &extended,
                body,
                &Evaluator {
                    remaining: ctx.config.fuel,
                    signature: ctx.signature,
                }
                .close(codomain, x)?,
            )
        }
        (Expr::Pair { first, second }, Val::Sigma(first_ty, second_ty)) => {
            check_in(ctx, first, first_ty)?;
            let first_v = ctx.eval(first)?;
            check_in(
                ctx,
                second,
                &Evaluator {
                    remaining: ctx.config.fuel,
                    signature: ctx.signature,
                }
                .close(second_ty, first_v)?,
            )
        }
        _ => {
            let found = infer_in(ctx, term)?;
            if assignable(expected, &found, ctx.values.len, ctx.config)? {
                Ok(())
            } else {
                Err(mismatch(expected, &found, ctx.values.len, ctx.config)?)
            }
        }
    }
}

/// Infer a closed term's type, returned in normal form.
pub fn infer(term: &Term) -> Result<Term, KernelError> {
    infer_with_config(term, EvalConfig::default())
}
/// Infer a closed term's type with a caller-selected resource budget.
pub fn infer_with_config(term: &Term, config: EvalConfig) -> Result<Term, KernelError> {
    let ctx = Context {
        config,
        ..Context::default()
    };
    quote(&infer_in(&ctx, term)?, 0, config)
}
/// Check a closed term against a closed type.
pub fn check(term: &Term, ty: &Term) -> Result<(), KernelError> {
    check_with_config(term, ty, EvalConfig::default())
}
/// Check a closed term against a closed type with a caller-selected budget.
pub fn check_with_config(term: &Term, ty: &Term, config: EvalConfig) -> Result<(), KernelError> {
    let ctx = Context {
        config,
        ..Context::default()
    };
    let expected = ctx.eval(ty)?;
    check_in(&ctx, term, &expected)
}

/// Infer a closed term's type using declarations from `signature`.
pub fn infer_in_signature(
    term: &Term,
    signature: &Signature,
    config: EvalConfig,
) -> Result<Term, KernelError> {
    let ctx = Context {
        config,
        signature: Some(signature),
        ..Context::default()
    };
    quote(&infer_in(&ctx, term)?, 0, config)
}

/// Check a closed term against a closed type using declarations from
/// `signature`.
pub fn check_in_signature(
    term: &Term,
    ty: &Term,
    signature: &Signature,
    config: EvalConfig,
) -> Result<(), KernelError> {
    let ctx = Context {
        config,
        signature: Some(signature),
        ..Context::default()
    };
    let expected = ctx.eval(ty)?;
    check_in(&ctx, term, &expected)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rc_sharing_is_the_term_representation() {
        let n = nat();
        let p = pi(n.clone(), n.clone());
        assert_eq!(Rc::strong_count(&n), 3);
        assert_eq!(infer(&p).unwrap(), universe(0));
    }
    #[test]
    fn universe_cumulativity_starts_correctly() {
        assert_eq!(infer(&universe(2)).unwrap(), universe(3));
    }
    #[test]
    fn universes_are_cumulative() {
        // Nat : Type0, and cumulative conversion admits Type0 <= Type1.
        check(&nat(), &universe(1)).unwrap();
        assert!(check(&universe(1), &universe(2)).is_ok());
    }
    #[test]
    fn pi_and_nbe_beta_reduce() {
        let id_ty = pi(nat(), nat());
        let id = lam(var(0));
        let applied = app(id.clone(), succ(zero()));
        check(&id, &id_ty).unwrap();
        assert_eq!(normalize(&applied).unwrap(), succ(zero()));
    }
    #[test]
    fn conversion_has_beta_but_no_unrequested_eta_rule() {
        // \f. \x. f x is eta-equivalent to \f. f in some presentations, but
        // the current core intentionally specifies beta conversion only.
        let eta_expansion = lam(lam(app(var(1), var(0))));
        let ty = pi(pi(nat(), nat()), pi(nat(), nat()));
        check(&eta_expansion, &ty).unwrap();
        assert_eq!(normalize(&eta_expansion).unwrap(), eta_expansion);
    }
    #[test]
    fn sigma_pair_and_projections() {
        let ty = sigma(nat(), nat());
        let value = pair(zero(), succ(zero()));
        check(&value, &ty).unwrap();
        assert_eq!(
            normalize(&Rc::new(Expr::Fst(value.clone()))).unwrap(),
            zero()
        );
        assert_eq!(normalize(&Rc::new(Expr::Snd(value))).unwrap(), succ(zero()));
    }
    #[test]
    fn evaluation_has_explicit_stack_cpu_budget() {
        assert!(matches!(
            eval(&zero(), EvalConfig { fuel: 0 }),
            Err(KernelError::OutOfFuel)
        ));
        assert!(eval(&succ(zero()), EvalConfig { fuel: 2 }).is_ok());
    }
    #[test]
    fn persistent_environments_extend_in_constant_work_and_share_tails() {
        let base = Env::default().extend(Rc::new(Val::Zero));
        let child = base.extend(Rc::new(Val::Succ(Rc::new(Val::Zero))));
        let base_head = base.head.as_ref().unwrap();
        assert!(Rc::ptr_eq(
            base_head,
            child.head.as_ref().unwrap().previous.as_ref().unwrap()
        ));
        assert_eq!(Rc::strong_count(base_head), 2);

        // This is a structural, not timing-sensitive, regression test: every
        // extension has exactly one new node and shares the preceding 100,000.
        let mut env = Env::default();
        for _ in 0..100_000 {
            env = env.extend(Rc::new(Val::Zero));
        }
        assert_eq!(env.len, 100_000);
        // Scope exit drops all 100,000 nodes normally via EnvNode's iterative Drop.
    }
    #[test]
    fn deep_unary_naturals_do_not_use_native_recursion_in_hot_paths() {
        const DEPTH: usize = 50_000;
        let mut term = zero();
        for _ in 0..DEPTH {
            term = succ(term);
        }
        let value = eval(&term, EvalConfig { fuel: DEPTH + 1 }).unwrap();
        let normal = quote(&value, 0, EvalConfig::default()).unwrap();
        assert_eq!(infer(&term).unwrap(), nat());
        check(&term, &nat()).unwrap();
        drop(normal);
        drop(value);
        drop(term);
    }
    #[test]
    fn deep_application_spine_evaluates_quotes_and_drops_normally() {
        const DEPTH: usize = 50_000;
        let identity = lam(var(0));
        let mut term = zero();
        // Right-associated applications exercise argument continuations too.
        for _ in 0..DEPTH {
            term = app(identity.clone(), term);
        }
        let value = eval(
            &term,
            EvalConfig {
                fuel: DEPTH * 3 + 1,
            },
        )
        .unwrap();
        assert_eq!(quote(&value, 0, EvalConfig::default()).unwrap(), zero());
        drop(value);
        drop(term);
    }
    #[test]
    fn deep_pi_spine_infers_checks_and_drops_normally() {
        const DEPTH: usize = 50_000;
        let mut term = nat();
        for _ in 0..DEPTH {
            term = pi(nat(), term);
        }
        assert_eq!(infer(&term).unwrap(), universe(0));
        check(&term, &universe(0)).unwrap();
        drop(term);
    }
    #[test]
    fn quote_reifies_a_deep_pi_value_tree() {
        const DEPTH: usize = 50_000;
        let mut term = nat();
        for _ in 0..DEPTH {
            term = pi(nat(), term);
        }
        let normal = normalize(&term).unwrap();
        assert!(matches!(normal.as_ref(), Expr::Pi { .. }));
        drop(normal);
        drop(term);
    }
    #[test]
    fn quote_reifies_a_deep_pair_value_tree() {
        const DEPTH: usize = 50_000;
        let mut term = zero();
        for _ in 0..DEPTH {
            term = pair(zero(), term);
        }
        let value = eval(
            &term,
            EvalConfig {
                fuel: DEPTH * 2 + 1,
            },
        )
        .unwrap();
        let normal = quote(&value, 0, EvalConfig::default()).unwrap();
        assert!(matches!(normal.as_ref(), Expr::Pair { .. }));
        drop(normal);
        drop(value);
        drop(term);
    }
    #[test]
    fn quote_reifies_a_deep_neutral_application_spine() {
        const DEPTH: usize = 50_000;
        let mut neutral = Rc::new(Neutral::Var(0));
        for _ in 0..DEPTH {
            neutral = Rc::new(Neutral::App(neutral, Rc::new(Val::Zero)));
        }
        let term = quote_neutral(&neutral, 1, EvalConfig::default()).unwrap();
        assert!(matches!(term.as_ref(), Expr::App { .. }));
        drop(term);
        drop(neutral);
    }
    #[test]
    fn inductive_parameters_and_indices_are_distinct() {
        let vec = InductiveDecl {
            name: "Vec".into(),
            params: vec![Binder {
                name: "A".into(),
                ty: universe(0),
            }],
            indices: vec![Binder {
                name: "n".into(),
                ty: nat(),
            }],
            universe: 0,
            constructors: vec![ConstructorDecl {
                name: "nil".into(),
                fields: vec![],
                result_indices: vec![zero()],
            }],
        };
        vec.validate_shape().unwrap();
        let bad = InductiveDecl {
            constructors: vec![ConstructorDecl {
                name: "broken".into(),
                fields: vec![],
                result_indices: vec![],
            }],
            ..vec
        };
        assert!(matches!(
            bad.validate_shape(),
            Err(KernelError::InvalidInductive(_))
        ));
    }

    #[test]
    fn public_kernel_operations_honor_the_callers_fuel_budget() {
        let term = succ(zero());
        let no_fuel = EvalConfig { fuel: 0 };
        assert!(matches!(
            normalize_with_config(&term, no_fuel),
            Err(KernelError::OutOfFuel)
        ));
        assert!(matches!(
            infer_with_config(&pi(nat(), nat()), no_fuel),
            Err(KernelError::OutOfFuel)
        ));
        assert!(matches!(
            check_with_config(&term, &nat(), no_fuel),
            Err(KernelError::OutOfFuel)
        ));
    }

    #[test]
    fn malformed_terms_report_their_typing_error_not_resource_exhaustion() {
        assert!(matches!(
            infer(&var(0)),
            Err(KernelError::UnboundVariable(0))
        ));
        assert!(matches!(check(&zero(), &nat()), Ok(())));
        assert!(matches!(
            check(&zero(), &pi(nat(), nat())),
            Err(KernelError::TypeMismatch { .. })
        ));
        assert!(matches!(
            normalize(&app(zero(), zero())),
            Err(KernelError::ExpectedFunction)
        ));
        assert!(matches!(
            normalize(&app(pi(nat(), nat()), zero())),
            Err(KernelError::ExpectedFunction)
        ));
    }

    #[test]
    fn signature_validates_definitions_and_persists_prior_versions() {
        let signature = Signature::default();
        let checked = signature
            .insert(Declaration::Definition(Definition::Transparent {
                name: "one".into(),
                ty: nat(),
                body: succ(zero()),
            }))
            .unwrap();
        assert!(signature.is_empty());
        assert_eq!(checked.len(), 1);
        assert!(matches!(
            checked.get("one"),
            Some(Declaration::Definition(_))
        ));
        assert!(matches!(
            checked.insert(Declaration::Definition(Definition::Opaque {
                name: "one".into(),
                ty: nat(),
            })),
            Err(KernelError::DuplicateDeclaration(name)) if name == "one"
        ));
    }

    #[test]
    fn signature_rejects_ill_typed_definition_bodies_and_constructor_name_clashes() {
        let signature = Signature::default();
        assert!(matches!(
            signature.insert(Declaration::Definition(Definition::Transparent {
                name: "bad".into(),
                ty: nat(),
                body: universe(0),
            })),
            Err(KernelError::TypeMismatch { .. })
        ));

        let bool_decl = InductiveDecl {
            name: "Bool".into(),
            params: vec![],
            indices: vec![],
            universe: 0,
            constructors: vec![
                ConstructorDecl {
                    name: "true".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorDecl {
                    name: "false".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
            ],
        };
        let signature = signature.insert(Declaration::Inductive(bool_decl)).unwrap();
        assert!(matches!(
            signature.insert(Declaration::Definition(Definition::Opaque {
                name: "true".into(),
                ty: nat(),
            })),
            Err(KernelError::DuplicateDeclaration(name)) if name == "true"
        ));
    }

    #[test]
    fn signature_aware_evaluation_unfolds_transparent_and_preserves_opaque_globals() {
        let signature = Signature::default()
            .insert(Declaration::Definition(Definition::Transparent {
                name: "one".into(),
                ty: nat(),
                body: succ(zero()),
            }))
            .unwrap()
            .insert(Declaration::Definition(Definition::Opaque {
                name: "external_nat".into(),
                ty: nat(),
            }))
            .unwrap();

        let one = eval_in_signature(&global("one"), &signature, EvalConfig::default()).unwrap();
        assert_eq!(quote(&one, 0, EvalConfig::default()).unwrap(), succ(zero()));
        assert_eq!(
            infer_in_signature(&global("one"), &signature, EvalConfig::default()).unwrap(),
            nat()
        );
        check_in_signature(
            &global("external_nat"),
            &nat(),
            &signature,
            EvalConfig::default(),
        )
        .unwrap();

        let opaque =
            eval_in_signature(&global("external_nat"), &signature, EvalConfig::default()).unwrap();
        assert_eq!(
            quote(&opaque, 0, EvalConfig::default()).unwrap(),
            global("external_nat")
        );
        assert!(matches!(
            eval(&global("missing"), EvalConfig::default()),
            Err(KernelError::UnknownGlobal(name)) if name == "missing"
        ));
    }

    #[test]
    fn closed_inductive_types_and_constructor_spines_are_checked() {
        let bool_decl = InductiveDecl {
            name: "Bool".into(),
            params: vec![],
            indices: vec![],
            universe: 0,
            constructors: vec![
                ConstructorDecl {
                    name: "true".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorDecl {
                    name: "false".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
            ],
        };
        let signature = Signature::default()
            .insert(Declaration::Inductive(bool_decl))
            .unwrap();
        assert_eq!(
            infer_in_signature(&global("Bool"), &signature, EvalConfig::default()).unwrap(),
            universe(0)
        );
        assert_eq!(
            infer_in_signature(&global("true"), &signature, EvalConfig::default()).unwrap(),
            global("Bool")
        );
        check_in_signature(
            &global("false"),
            &global("Bool"),
            &signature,
            EvalConfig::default(),
        )
        .unwrap();

        let boxed = InductiveDecl {
            name: "BoxNat".into(),
            params: vec![],
            indices: vec![],
            universe: 0,
            constructors: vec![ConstructorDecl {
                name: "box".into(),
                fields: vec![Binder {
                    name: "value".into(),
                    ty: nat(),
                }],
                result_indices: vec![],
            }],
        };
        let signature = signature.insert(Declaration::Inductive(boxed)).unwrap();
        let value = app(global("box"), succ(zero()));
        assert_eq!(
            infer_in_signature(&value, &signature, EvalConfig::default()).unwrap(),
            global("BoxNat")
        );
        assert_eq!(
            normalize_in_signature(&value, &signature, EvalConfig::default()).unwrap(),
            value
        );
    }

    #[test]
    fn signature_rejects_inductive_features_outside_the_implemented_fragment() {
        let parameterized = InductiveDecl {
            name: "List".into(),
            params: vec![Binder {
                name: "A".into(),
                ty: universe(0),
            }],
            indices: vec![],
            universe: 0,
            constructors: vec![ConstructorDecl {
                name: "nil".into(),
                fields: vec![],
                result_indices: vec![],
            }],
        };
        assert!(matches!(
            Signature::default().insert(Declaration::Inductive(parameterized)),
            Err(KernelError::InvalidDeclaration(_))
        ));
    }

    #[test]
    fn inductive_admission_rejects_ambiguous_names_before_registry_insertion() {
        let duplicate = InductiveDecl {
            name: "Choice".into(),
            params: vec![],
            indices: vec![],
            universe: 0,
            constructors: vec![
                ConstructorDecl {
                    name: "pick".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorDecl {
                    name: "pick".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
            ],
        };
        assert!(matches!(
            Signature::default().insert(Declaration::Inductive(duplicate)),
            Err(KernelError::InvalidInductive(
                "constructor names must be distinct"
            ))
        ));
    }

    #[test]
    fn strict_positivity_rejects_a_recursive_name_to_the_left_of_an_arrow() {
        let bad = InductiveDecl {
            name: "Bad".into(),
            params: vec![],
            indices: vec![],
            universe: 0,
            constructors: vec![ConstructorDecl {
                name: "mk_bad".into(),
                fields: vec![Binder {
                    name: "consume".into(),
                    ty: pi(global("Bad"), nat()),
                }],
                result_indices: vec![],
            }],
        };
        assert!(matches!(
            Signature::default().insert(Declaration::Inductive(bad)),
            Err(KernelError::NonPositiveOccurrence(name)) if name == "Bad"
        ));
    }
}
