# Trusted computing base

Eagle's trusted computing base (TCB) is the code that can determine whether a
core term or declaration is accepted.  The boundary is deliberately recorded
before cubical features expand it.

## Trusted today

| Module | Responsibility |
| --- | --- |
| `src/syntax.rs` | Well-scoped core representation and its iterative teardown. |
| `src/semantic.rs` | Semantic values, closures, environments, neutrals, and iterative teardown. |
| `src/lib.rs` | Evaluation, quotation, conversion, bidirectional type checking, and public kernel entry points. |
| `src/inductive.rs` | Structural inductive-declaration syntax and validation. |
| `src/signature.rs` | Persistent global registry and admission checks for the current inductive fragment. |
| `src/error.rs` | Kernel error representation. |

The crate forbids `unsafe` code.  Resource budgets are part of the kernel
interface: exhausting a budget produces `KernelError::OutOfFuel`, never a
successful or failed typing judgment.

## Explicitly not trusted

There is not yet a parser, elaborator, tactic engine, module loader, REPL, or
editor integration.  When added, each must emit core syntax and ask the
kernel to check it; a front-end success value alone must never establish that
a theorem is accepted.

## Audit obligations for later milestones

- Dimension syntax and cofibrations must remain separate from term variables.
- Every new semantic constructor must define evaluation, quotation,
  restriction, conversion behavior, and resource behavior together.
- Extending inductives from shape validation to positivity and elimination
  adds those algorithms to this table.
- Keep the regression corpus, stack-depth tests, formatting, Clippy, and unit
  tests mandatory in CI.
