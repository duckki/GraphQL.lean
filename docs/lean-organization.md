# Lean Module Organization

This repo separates definition surfaces from proof modules. The goal is to keep
the core GraphQL model easy to read while letting proof files grow by topic.

## Top-Level Files

Top-level `GraphQL/*.lean` files should contain definitions only:

- syntax types,
- structures,
- inductive predicates,
- executable functions,
- public propositions and predicates,
- notation or small definition-facing helpers.

Do not add ordinary `theorem` or `lemma` declarations to top-level files.
Theorems should live under a subdirectory named for the definition area they
support.

Examples:

- Definitions for validation belong in `GraphQL/Validation.lean`.
- Proofs about validation belong under `GraphQL/Validation/`.
- Definitions for execution belong in `GraphQL/Execution.lean`.
- Proofs about execution belong under `GraphQL/Execution/`.

## Termination Proof Exception

Termination material for recursive definitions may remain in the same file as
the definition when Lean requires it to be attached to the recursive block.

Standalone termination helper theorems are the only allowed top-level theorem
exception. Put them at the bottom of the file, below this exact style of banner:

```lean
/-! ============================================================
Termination theorems only
============================================================ -/
```

No non-termination theorem should appear below that banner.

## Proof Module Names

Proof modules should be named by topic. Avoid generic file names such as:

- `Theorems.lean`
- `Lemmas.lean`
- `Facts.lean`
- `Utils.lean`

Prefer names that say what the proofs are about:

- `GraphQL/Execution/FieldCollection.lean`
- `GraphQL/Validation/SelectionValidity.lean`
- `GraphQL/Validation/FieldMerge.lean`
- `GraphQL/SchemaWellFormedness/PossibleTypes.lean`
- `GraphQL/NormalForm/GroundTypeNormalization/FieldSemantics.lean`

If a file name starts to need "misc", "helper", or "common", split by the
nearest domain concept instead.

## Import Shape

Definition modules should not import proof modules. This keeps the core model
usable without pulling in large proof dependencies.

Proof modules may import:

- the definition module they prove facts about,
- earlier proof modules for prerequisite facts,
- downstream definition modules only when the theorem topic explicitly bridges
  those areas.

The root import surface `GraphQL.lean` may import both definition modules and
proof modules, in reading order.

## Normal Form Proofs

Ground-type normalization proofs should stay under
`GraphQL/NormalForm/GroundTypeNormalization/` and be split by the proof role:

- directive-freeness preservation,
- schema and possible-type facts,
- validation transport,
- field-merge transport,
- lookup validity,
- semantic readiness,
- executable field collection,
- field execution semantics,
- abstract return semantics,
- selection-set semantic preservation,
- operation/store semantic lifts,
- normality and non-redundancy.

The top-level `GraphQL/NormalForm.lean` file should keep only the normal-form
definitions, predicates, normalizer functions, and public correctness
propositions.

## Refactor Rule

When moving a theorem, preserve its declaration name unless there is a specific
reason to rename it. Module moves should not make downstream proof scripts pay
for both a relocation and a rename at the same time.
