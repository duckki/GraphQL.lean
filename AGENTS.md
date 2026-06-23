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
- request errors, detailed execution error maps, response `extensions`, error
  paths, and error locations,
- response-shape analysis,
- minimization,
- federation.

The immediate proof goal is to formalize schema, operation validation,
store-backed execution, and ground normal form enough to support later semantic
operation transformation algorithms.

## Current Status

`GraphQL.DataModel` is the proof-facing data model. It defines a typed graph
store with path-independent node ids. Runtime object values are parameterized by
opaque resolver-owned refs; store-backed execution is the spec executor
instantiated with data-model refs and resolvers. Execution returns a response
envelope with `data` plus a `Nat` execution-error count, and null bubbling
through non-null wrappers is modeled with `Execution.Result`. Store conformance
ties execution to the graph root, validates field-label arguments, rejects
duplicate node ids and semantic duplicate property/edge keys, enforces
list-index discipline, and requires edge target types to be available in the
store. Store-backed operation equivalence runs over full responses from this
resolver-instantiated execution model.

`NormalForm.groundNormalFormCorrect` uses
`DataModel.operationsEquivalent`. The ground-type normalizer has no fuel
parameter; it terminates by structural descent on selection-set size while
merging fields and grounding abstract returns. Public normal-form predicates
belong in top-level `GraphQL/NormalForm.lean`; proof work belongs under
`GraphQL/NormalForm/`, with directive-free ground-type proof modules under
`GraphQL/NormalForm/GroundTypeNormalization/`.

The store-resolution bridge in `GraphQL.DataModel.Store` includes
`lookupType_name_eq`, `typeIncludesObject_eq_of_lookupObjectType`,
`ObjectNode.lookupProperty?_some_conformsToLookupField`,
`Store.lookupNode?_some_mem`, `Store.lookupNode?_some_id`,
`Store.lookupNode?_some_of_mem_unique`,
`Store.firstNodeWithType?_some_mem`, `Store.firstNodeWithType?_some_typeName`,
`Store.resolveValue_ne_scalar_of_compositeLookupField`,
`possibleTypes_eq_nil_of_isLeafType`,
`fieldReturnType?_some_lookupField`, and
`scalar_not_conformsToType_of_possibleTypes_nonempty`.

The latest successful checks were:

```sh
lake build
lake lint
```

## Where To Look

- `docs/spec-conformance-plan.md`: current goals, skips, status, and proof status.
- `docs/lean-organization.md`: module organization rules for keeping
  top-level Lean files definition-only and theorem files topic-specific.
- `docs/ground-type-normal-form-proof.md`: summary of the completed
  directive-free ground-type normal form correctness proof.
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

Keep top-level `GraphQL/*.lean` files definition-only. Put ordinary theorems in
topic-specific subdirectory modules, following `docs/lean-organization.md`.

Review workflow: do not commit before review. Prepare one reviewable slice at a
time, run the relevant checks, summarize the diff, and wait for the user to ask
for the commit. After committing, stop again for review before continuing to the
next proof or implementation slice, unless the user explicitly asks to continue
past that review boundary.
