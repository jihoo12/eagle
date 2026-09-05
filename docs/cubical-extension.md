# Cubical extension boundary

Term variables and interval variables will use **separate de Bruijn namespaces**.
`Expr::Var` and the current `Env` remain the ordinary term namespace.  The
future syntax will add `Dim::Var(usize)` plus term forms such as
`Coe { line, from, to, value }` and `HCom { ty, cap, tubes }`; dimensions will
not be encoded as ordinary MLTT terms.

`Closure` will gain `dims: DimEnv`, a persistent environment parallel to the
current `Env`.  `DimEnv` is an Rc cons-list of interval endpoints/neutral
dimension variables, so capturing either namespace remains O(1).  Applying a
term closure extends only `Env`; evaluating a line/family under a dimension
binder extends only `DimEnv`.  Thus existing term binders and their de Bruijn
indices do not change.

The checker context will become `{ term_types, term_values, dims, faces }`.
`faces` records cofibration assumptions (initially conjunctions of dimension
equalities), and is consulted for restriction/face normalization.  The term
type context keeps its current persistent representation.

Semantic values will gain interval-aware forms such as `Val::Coe`, `Val::HCom`,
and `Val::Glue`; neutrals will gain corresponding blocked forms (for example
`Neutral::Coe { line, from, to, value }`).  A neutral application whose head is
blocked by a dimension remains an ordinary `Neutral::App` spine around that
blocked head.  Quotation will reify these forms with both the term level and
dimension level.  This is why the current closure/environment split is kept
explicit rather than merging all future variables into `Expr::Var`.
