# Inductive registry: current executable fragment

`Signature` is Eagle's persistent trusted declaration registry.  Every call to
`insert` returns a new signature sharing the prior registry; previous versions
remain valid.  It currently accepts:

- checked opaque and transparent definitions;
- closed, non-parameterized, non-indexed inductive type declarations;
- constructors whose field types are closed core types.

For an inductive declaration `I : Type u` with constructor fields
`A1, ..., An`, the constructor global has the synthesized type:

```text
A1 -> ... -> An -> I
```

Constructors and opaque definitions evaluate to neutral global heads.  An
application of a constructor therefore remains a neutral application spine;
this is the correct blocked normal form until eliminators are implemented.
Transparent definitions unfold during signature-aware evaluation.

## Admission policy

The registry rejects empty or duplicate constructor names, duplicate declaration
names, clashes with constructor names, ill-typed definition bodies, and field
types that are not types.  It
also rejects inductive parameters and indices today.  This is intentional:
dependent constructor telescopes, recursive occurrences, indexed result
checking, positivity, and eliminators form one soundness-critical feature and
must arrive together.  The current closed-field fragment contains no recursive
occurrence, so strict positivity holds vacuously.

As a forward-safety check, declaration admission already scans constructor
field syntax for the inductive's own name and rejects an occurrence to the
left of a `Pi` arrow.  This is conservative groundwork, not a claim that
positive recursive declarations are executable: those remain rejected until
the next extension supplies inductive application and eliminator rules.

## Next extension

Before admitting `List A`, `Vec A n`, or recursive fields, extend syntax with
explicit inductive applications and constructor values; validate parameter and
index telescopes under local contexts; add structural positivity; then define
eliminators that reduce on constructor values.  Do not loosen the current
admission restriction independently of those rules.
