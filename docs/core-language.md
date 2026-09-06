# Eagle core language contract

This document specifies the small MLTT core accepted by the current kernel.
It is a contract for future refactors: changing a rule here requires a test
and an intentional compatibility decision.  Cubical syntax is intentionally
absent until the dimension namespace in `cubical-extension.md` is implemented.

## Contexts and notation

Terms use de Bruijn **indices**.  In `Γ, A`, index `0` names the newly bound
variable and index `n + 1` names the variable at index `n` in `Γ`.  Semantic
neutrals instead use de Bruijn **levels**, so quotation at level `l` turns a
neutral level `k` into syntactic index `l - k - 1`.

`Type i` is written in the implementation as `Universe(i)`.  Universes are
cumulative: a term of `Type i` may be checked against `Type j` when `i <= j`.

## Grammar

```text
t, A ::= #n                         variable
       | Type i                      universe
       | (x : A) -> B                dependent function type (Pi)
       | \x. t                       lambda
       | t u                         application
       | (x : A) * B                 dependent pair type (Sigma)
       | (t, u)                      pair
       | fst t | snd t               projections
       | Nat | zero | succ t         natural numbers
```

The Rust representation is `Expr` in `src/syntax.rs`; all subterms are
immutable shared `Rc` values.  `src/lib.rs` re-exports its public constructor
helpers, preserving the crate's compact embedding API.

## Typing and computation obligations

| Form | Typing invariant | Definitional computation |
| --- | --- | --- |
| `#n` | `Γ(n)` must exist. | Evaluates to the environment entry. |
| `Type i` | `Γ |- Type i : Type (i + 1)`. | Is already normal. |
| `Pi A B` | `Γ |- A : Type i`, `Γ,A |- B : Type j`. | Is a type in `Type max(i,j)`. |
| `\x. t` | Checked, not inferred: expected type must be `Pi A B`; check body in `Γ,A`. | `(\x. t) u` beta-reduces. |
| `t u` | Infer `t : Pi A B`, then check `u : A`. | A lambda head beta-reduces; a neutral head gains an application spine. |
| `Sigma A B` | As for `Pi`. | Is a type in `Type max(i,j)`. |
| `(t, u)` | Checked, not inferred: expected type is `Sigma A B`; `u : B[t/x]`. | `fst (t,u)` reduces to `t`; `snd (t,u)` reduces to `u`. |
| `fst t`, `snd t` | Infer `t : Sigma A B`. | Concrete pairs project; neutral pairs remain neutral projections. |
| `Nat` | `Γ |- Nat : Type 0`. | Is already normal. |
| `zero` | `Γ |- zero : Nat`. | Is already normal. |
| `succ t` | `Γ |- t : Nat`. | Is a value after evaluating `t`. |

At this stage there is no primitive eliminator for `Nat`, no eta conversion,
and no equality/path type.  A later milestone must add each feature to this
table before making it public.

## Conversion and diagnostics

Conversion is normalization by evaluation (NbE): evaluate in a semantic
environment, then quote to core syntax and compare the resulting normal forms.
The only non-structural conversion rule is universe cumulativity.  Consequently
the checker reports `TypeMismatch` with quoted expected and found types; it
does not expose semantic values to callers.

`KernelError::OutOfFuel` is a resource outcome, not a type error.  The legacy
`normalize`, `infer`, and `check` APIs use `EvalConfig::default()`.  Callers
that need a predictable resource bound use `normalize_with_config`,
`infer_with_config`, and `check_with_config`.  A configured fuel limit applies
to each evaluator or quotation machine created by the operation.

## Implementation invariants

- Environments are persistent cons lists.  Extending an environment allocates
  one node and shares its tail; closures capture the environment handle.
- Evaluation and quotation use explicit heap work stacks.  Core nesting must
  not consume one native Rust frame per syntax/value constructor.
- Drop implementations drain uniquely owned recursive structures iteratively.
  New recursive core representations need the same teardown review.
- `InductiveDecl::validate_shape` validates only structural declaration shape.
  Positivity and constructor typing remain future trusted-kernel work.
