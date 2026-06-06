# Repo Agent Memory

This repo is a Lean formalization workspace for a scoped plain GraphQL fragment.

## Current Priority

Spec conformance is the current priority, following
`docs/spec-conformance-plan.md`.

Current explicit skips:

- mutation,
- subscription,
- named fragment definitions and fragment spreads,
- custom directives beyond modeled `@skip` and `@include`,
- coercion, assuming values are already coerced and type-conformant,
- introspection and meta-fields,
- execution errors and response `errors` / `extensions`,
- response-shape analysis,
- minimization,
- federation.

The immediate proof goal is to formalize schema, operation validation,
store-backed execution, and ground normal form enough to support later semantic
operation transformation algorithms.

## Current Status

`GraphQL.DataModel` is the proof-facing data model. It defines typed object
identities, field facts keyed by already-coerced arguments, store-backed
resolvers, and operation equivalence over store-backed execution.

`NormalForm.groundNormalFormCorrect` uses
`DataModel.operationsEquivalentOnData`. The ground-type normalizer has no fuel
parameter; it terminates by structural descent on selection-set size while
merging fields and grounding abstract returns. Public normal-form predicates
belong in top-level `GraphQL/NormalForm.lean`; proof work belongs under
`GraphQL/NormalForm/`, with
`GraphQL/NormalForm/GroundTypeNormalization.lean` as the first directive-free
ground-type proof module.

The store-resolution bridge in `GraphQL.DataModel.Store` includes
`lookupType_name_eq`, `typeIncludesObject_eq_of_lookupObjectType`,
`ObjectRecord.lookupField?_some_conformsToLookupField`,
`Store.resolveValue_conformsToLookupField`,
`Store.resolveValue_ne_scalar_of_compositeLookupField`,
`possibleTypes_eq_nil_of_isLeafType`,
`fieldReturnType?_some_lookupField`, and
`scalar_not_conformsToType_of_possibleTypes_nonempty`.

The latest successful checks before cleanup were:

```sh
lake build
lake lint
```

## Where To Look

- `docs/spec-conformance-plan.md`: current goals, skips, status, and proof plan.
- `docs/ground-type-normal-form-correctness-plan.md`: detailed directive-free
  ground-type normal form correctness theorem plan.
- `docs/overview.md`: module map and architecture overview.
- `docs/references.md`: GraphCoQL reference notes and proof-strategy context.
- `GraphQL/DataModel.lean`: typed store model and correctness predicates.
- `GraphQL/DataModel/Store.lean`: store-resolution well-typedness bridge lemmas.
- `GraphQL/NormalForm.lean`: ground normal form scaffold.
- `GraphQL/Execution.lean`: resolver-based execution used by the data model.
- `GraphQL/Validation.lean`: current operation validity assumptions.

## Development Notes

Keep raw syntax permissive and put invariants in validation or well-formedness
predicates. Prefer small, proof-friendly definitions over feature expansion.
When adding scope, update `docs/spec-conformance-plan.md` first.

Review workflow: do not commit before review. Prepare one reviewable slice at a
time, run the relevant checks, summarize the diff, and wait for the user to ask
for the commit. After committing, stop again for review before continuing to the
next proof or implementation slice, unless the user explicitly asks to continue
past that review boundary.
