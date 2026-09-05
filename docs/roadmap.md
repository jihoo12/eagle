# Roadmap: Eagle, a Cartesian Cubical Type Theory proof assistant

## Purpose and scope

Eagle should become a small, auditable proof assistant whose trusted core
implements a computational presentation of **Cartesian Cubical Type Theory
(CCTT)**.  The first usable target is a command-line checker for source files
with dependent functions and pairs, natural numbers, inductive families,
paths, univalence (through Glue), and higher-dimensional composition.

This is deliberately not a plan to make every layer dependently typed at once.
The kernel stays small and semantic; the surface language, elaborator,
pretty-printer, REPL, and editor integration are untrusted clients of it.

The immediate code base already supplies a useful foundation:

| Present component | Location | Role in the plan |
| --- | --- | --- |
| De Bruijn core syntax for MLTT | `src/lib.rs` | Remains the elaborated core language. |
| NbE evaluator and quotation | `src/lib.rs` | Becomes cubical evaluation and conversion. |
| Bidirectional checker | `src/lib.rs` | Gains dimension and face contexts. |
| Persistent term environment | `src/lib.rs` | Pattern for the dimension environment. |
| Initial cubical boundary | `docs/cubical-extension.md` | Architectural constraint for the cubical extension. |
| Initial inductive declaration data | `src/lib.rs` | Starting point for a checked global signature. |

## Non-negotiable design decisions

1. **Separate namespaces.** Term variables and interval variables must never
   share de Bruijn indices.  Preserve `Expr::Var` for terms; introduce `Dim`
   for dimensions as described in `cubical-extension.md`.
2. **Normalization by evaluation is conversion.** Do not add an independent,
   syntactic equality engine.  Extend evaluation, restriction, and quotation
   together, then use their normal forms for definitional equality.
3. **The kernel checks an explicit core language.** Name resolution,
   implicit arguments, holes, tactics, and parsing do not enter the trusted
   computing base.
4. **Every cubical constructor has computation rules before it is exposed.**
   In particular, endpoint and face reductions must be tested before adding
   surface syntax for a feature.
5. **Keep resource behavior intentional.** The current explicit evaluator and
   quotation stacks avoid native-stack overflow.  New syntax, substitutions,
   restriction, diagnostics, and declaration checking must retain that
   property and have budget/limit policies.

## Milestone 0 — Stabilize the existing MLTT kernel

**Goal:** create a dependable baseline before changing the semantic domain.

- Split `src/lib.rs` by responsibility without changing behavior:
  `syntax`, `semantic`, `eval`, `quote`, `check`, `inductive`, and `error`.
  Keep the public API small and add re-exports while the split is underway.
- Define a documented core-language grammar and the invariant for each AST
  constructor: its binders, universe level, and expected evaluation behavior.
- Make evaluator fuel configurable at all public entry points, including
  normalization and conversion; distinguish resource exhaustion from an
  ill-typed term in diagnostics.
- Add golden/unit tests for beta/eta behavior, cumulativity boundaries,
  dependent `Sigma` projection, neutral spines, and malformed terms.
- Run formatting, Clippy, unit tests, and deep-stack regressions in CI.

**Exit criteria:** all present behavior is regression-tested; the core can be
refactored without changing its observable API or introducing recursion in hot
paths.

## Milestone 1 — Global signature and ordinary inductive families

**Goal:** replace shape-only declarations with a checked, persistent global
signature, before mixing inductives with cubical composition.

- Introduce a `Signature` containing constants, opaque/transparent
  definitions, inductive declarations, constructors, and eliminators.
- Type-check declaration parameters, indices, constructor fields, and result
  indices in the correct telescopic contexts.  Reject duplicate names and
  dangling references.
- Implement strict positivity over the elaborated core.  Start with a small,
  explicit supported fragment; reject unsupported recursive occurrences rather
  than accepting them optimistically.
- Add core terms/values/neutrals for global constants, constructor
  applications, and eliminator/case applications.  Evaluation reduces only a
  fully known constructor redex; blocked eliminations remain neutral.
- Provide `Nat` through the same declaration/elimination machinery, then
  migrate the built-in syntax only if this reduces special cases.
- Test `Bool`, `Nat`, `List A`, and indexed `Vec A n`, including failed
  positivity and index-mismatch cases.

**Exit criteria:** a checked declaration cannot make evaluation get stuck on a
well-typed constructor redex, and invalid recursive definitions are rejected
at the signature boundary.

## Milestone 2 — Dimension algebra and cofibrations

**Goal:** add the Cartesian interval infrastructure independently of higher
  composition.

- Define `Dim = Zero | One | Var(usize)` and a persistent `DimEnv`.  Dimension
  substitution/restriction must be total and preserve endpoint normalization.
- Add dimension binders and line/family syntax to the core, with a distinct
  de Bruijn shifting/substitution implementation from term substitution.
- Represent the initial cofibration fragment as finite conjunctions of
  equations `r = s`; normalize equations, decide consistency, and implement
  entailment needed to choose an active face.  Keep this API abstract so a
  later disjunctive face lattice does not infect the checker.
- Change the checking context to term types, term values, dimensions, and
  faces.  Applying a term closure extends only the term environment; applying
  a dimension abstraction extends only the dimension environment.
- Add restriction to all semantic values and neutrals, and verify identity,
  composition, and endpoint laws with property tests.

**Exit criteria:** the kernel can type and normalize dimension-indexed lines;
restrictions compose correctly and no term-variable operation can capture a
dimension variable (or vice versa).

## Milestone 3 — Paths and cubical normalization

**Goal:** make equality computational through paths, without claiming
univalence yet.

- Add `Path`/path-abstraction and path-application forms.  A path applied at
  `0` or `1` must reduce to its endpoints definitionally.
- Extend semantic values, neutrals, quotation, equality, and diagnostics in
  the same change.  Quote with both the term level and dimension level.
- Implement path eta only where justified by the chosen CCTT presentation;
  document every definitional equality instead of relying on accidental
  normalization behavior.
- Add examples proving reflexivity, symmetry, transitivity, congruence, and
  function extensionality through paths.  Include open/neutral path tests,
  not only closed endpoint examples.

**Exit criteria:** endpoint reduction and path conversion are stable under
term substitution and dimension restriction, with normal forms independent of
the order in which faces are simplified.

## Milestone 4 — `coe`, homogeneous composition, and systems

**Goal:** implement the Kan operations that make type families transportable.

- Add core syntax for `Coe { line, from, to, value }`, `HCom { ty, cap,
  tubes }`, and an explicit system/tube representation.  A system must carry
  its faces and boundary terms in a shape that makes coverage and agreement
  checkable.
- Type-check `coe` as transport along a line of types and `hcom` under the
  appropriate extent/face assumptions.  Check tube compatibility on every
  pairwise overlap; do not leave boundary equality to the evaluator.
- Implement the defining reductions first: constant-family transport,
  `coe r r a`, endpoint/active-face composition, and restriction through all
  arguments.  Blocked cases become semantic neutrals.
- Treat generated compositions as first-class semantic values so evaluation
  does not repeatedly expand large tubes.  Define quotation for these blocked
  forms before using them in conversion.
- Add focused test matrices: endpoints, each active face, overlapping faces,
  open dimension variables, nested transports, and fuel-limited workloads.

**Exit criteria:** transport and composition satisfy their declared boundary
laws definitionally, and every well-typed system has compatible faces.

## Milestone 5 — Glue, equivalences, and univalence

**Goal:** obtain a computational univalence principle rather than an axiom.

- Specify the exact Glue formulation and rules adopted by Eagle; cite the
  primary CCTT source in a design document and translate each rule into a
  checker/evaluator obligation.
- Add `Equiv`, `Glue`, `glue`, and `unglue` core forms together with their
  semantic counterparts and restriction behavior.
- Check equivalence data and Glue-system compatibility under their
  cofibrations.  Implement reduction when a Glue face is active and neutral
  forms otherwise.
- Define `ua : Equiv A B -> Path Type A B` in the trusted core/library and
  verify the computational transport rule users expect from univalence.
- Add small formal developments: equivalence of a type with itself, transport
  along `ua`, and a nontrivial structure-preserving equivalence.

**Exit criteria:** univalence is derived from checked computational primitives;
there is no unchecked equality axiom or postulated conversion rule.

## Milestone 6 — Higher inductive types and cubical inductives

**Goal:** support a carefully scoped class of HITs only after their Kan
interaction is sound.

- Start with a signature format that can express point constructors and path
  constructors.  State supported dimensional arities and reject the rest.
- Extend positivity and boundary checking to constructors with faces.  Ensure
  eliminators respect constructor boundaries and composition.
- Implement a minimal first HIT (for example the circle) with a recursor and
  prove its beta rules, including the path constructor boundary.
- Decide, document, and test the policy for general schema-defined cubical
  inductive types versus a small built-in collection.  This is a major trusted
  kernel boundary, so prefer a smaller verified fragment initially.

**Exit criteria:** the first HIT computes at points and boundaries, and its
eliminator cannot be formed with incoherent motives or methods.

## Milestone 7 — Surface language and elaboration

**Goal:** let people write proofs without exposing de Bruijn terms, while
keeping all elaboration untrusted.

- Create a lossless parser with spans and recoverable syntax errors.  Use
  named variables, declarations, modules, universe notation, explicit and
  implicit binders, path syntax, and readable cubical system syntax.
- Elaborate names to the core AST, resolving modules and globals through the
  signature.  Implement bidirectional elaboration, metavariables, unification
  constrained by the kernel's conversion test, and user holes.
- Build a scope-aware pretty-printer that round-trips parsed declarations and
  presents normal forms without raw de Bruijn indices.
- Keep an elaboration trace and source spans attached to errors so kernel
  errors become actionable messages (expected/found types, enclosing term,
  relevant face assumptions).
- Add file-level integration tests with accepted and rejected examples.

**Exit criteria:** a user can check a multi-declaration file and receive
source-located diagnostics; elaboration emits only core terms accepted by the
kernel.

## Milestone 8 — Proof workflow and product shell

**Goal:** make the checker pleasant enough to use daily.

- Turn `src/main.rs` into a CLI with `check`, `normalize`, `repl`, and
  `--print-core` commands.  Keep `lib.rs` usable as an embedding API.
- Add an interactive goal view, hole commands, basic refinement tactics, and
  a proof-state format that is derived from elaboration state rather than
  trusted by the kernel.
- Add module caching keyed by source and dependency hashes; cache checked core
  artifacts, never unchecked success claims.
- Add an editor protocol or language-server layer only after diagnostics and
  incremental parsing are stable.
- Publish a tutorial that leads from ordinary dependent types to paths,
  transport, univalence, and the first HIT.

**Exit criteria:** `eagle check examples/*.eagle` can validate a small standard
library and tutorial corpus with clear failures and reproducible output.

## Cross-cutting verification strategy

- **Executable metatheory tests:** for every constructor, test typing,
  evaluation, quotation, restriction, and conversion together.  Include open
  terms and dimensions because closed tests hide neutral-form bugs.
- **Property tests:** generate well-scoped core syntax and dimension
  substitutions; check restriction identity/composition and normalization
  idempotence.  Shrink failures to printable source examples.
- **Differential/reference checks:** maintain a tiny, slow specification
  evaluator for selected closed examples and compare it against the production
  NbE implementation.
- **Regression corpus:** each fixed soundness, capture, boundary, or
  performance bug gets a minimal test file and a short explanation.
- **Resource tests:** preserve the existing deep-spine tests and add deep
  cubical systems, nested restrictions, and declaration signatures.  Fuzzing
  and untrusted parsing must never panic the process.
- **Trusted-base audit:** maintain `docs/trusted-base.md`, listing every module
  that can affect acceptance and every intentionally untrusted layer.

## Suggested repository layout after Milestone 1

```text
src/
  core/        # syntax, dimensions, semantic values, eval, quote, checking
  signature/   # declarations, positivity, globals, inductives
  surface/     # parser, AST with spans, pretty-printing
  elaborate/   # name resolution, metavariables, bidirectional elaboration
  cli/         # commands and REPL (untrusted front end)
  lib.rs       # small embedding API and core re-exports
  main.rs      # CLI entry point
docs/
  roadmap.md
  cubical-extension.md
  theory.md    # chosen CCTT rules and references
  trusted-base.md
examples/
tests/
```

## Sequencing rules and anti-goals

Do not begin Glue, HITs, tactic automation, or a language server before the
preceding kernel milestone has its exit criteria and regression suite.  Do not
encode dimensions as `Nat` or ordinary terms, add quotient-style axioms to
simulate univalence, or make the parser/evaluator silently repair malformed
systems.  Early progress should favor a narrow, correct cubical calculus over
a broad feature list with unclear computation rules.

## First implementation slice

The next focused slice should be Milestone 0 followed by the first half of
Milestone 2: move the current core into modules, introduce `Dim`, `DimEnv`,
and closed dimension substitution/restriction tests, but do not yet expose
`Path`, `Coe`, or `HCom`.  This validates the central architectural decision
with low semantic risk and gives every later cubical feature the same reliable
foundation.
