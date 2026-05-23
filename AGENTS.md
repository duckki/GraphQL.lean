# Repo Agent Memory

This repo is a Lean formalization workspace for GraphQL, with federation planned
later.

## Current Priority

Spec conformance is the current priority, but only for the scoped plain GraphQL
fragment described in `docs/spec-conformance-plan.md`.

Current explicit skips:

- mutation,
- subscription,
- custom directives beyond modeled `@skip` and `@include`,
- coercion, assuming values are already coerced and type-conformant,
- introspection and meta-fields,
- execution errors and response `errors` / `extensions`,
- minimization,
- federation.

The immediate proof goal is to formalize the data model enough to prove
response-shape analysis and ground normal form correctness.

## Current Status

`GraphQL.DataModel` has been added as the proof-facing data model. It defines
typed object identities, field facts keyed by already-coerced arguments,
store-backed resolvers, typed response trees, response-shape conformance checks,
and correctness predicates for operation equivalence and ground normal form.

`GraphQL.DataModel.TypedExecution` now provides typed execution over the store
model while preserving runtime object type names in response objects. Untyped
data-model execution is tied directly to `GraphQL.Execution` through
store-backed resolvers. Data-model operation equivalence has reflexivity,
symmetry, and transitivity theorems. Typed execution has erasure theorems ending
at `DataModel.TypedExecution.executeOperation_erase`.

`DataModel.groundNormalFormCorrect` now uses
`DataModel.semanticOperationsEquivalentOnDataWithFuel` with the source
operation's `Execution.executeSemanticQueryFuel` for both the original and
normalized operations. This is intentional: normalizing can shrink syntax, and
the bounded executor should not count that fuel-budget change as a semantic
change.

`GraphQL.ResponseShape` now resets child-shape possible runtime types to the
field return type through `ResponseShape.Condition.forChildType`. Keep this
behavior when working on response-shape soundness.

Ground normal form correctness is proved for direct single-leaf selections with
or without modeled directives, inline-fragment single-leaf selections without
directives, object-type typed inline fragments with modeled directives, and two
direct no-directive leaf fields with distinct response names. The next proof
boundary is to generalize the distinct direct leaf-field case to lists before
tackling same-response-name field merging.

Directive-specific data-model proofs live in `GraphQL/DataModel/Directives.lean`.
That module currently proves single-leaf response-shape soundness for modeled
`@skip` and `@include` directive lists whose shape condition parses, both on
direct fields, untyped inline fragments, and typed inline fragments. It also
proves normal-form response-shape preservation for direct directive-bearing
single fields and object-type typed inline fragments.

The latest successful checks were:

```sh
lake build
lake lint
```

## Where To Look

- `docs/spec-conformance-plan.md`: current goals, skips, status, and proof plan.
- `docs/overview.md`: module map and architecture overview.
- `docs/references.md`: GraphCoQL reference notes and proof-strategy context.
- `GraphQL/DataModel.lean`: typed store model and correctness predicates.
- `GraphQL/DataModel/Directives.lean`: `@skip`/`@include` response-shape proofs.
- `GraphQL/DataModel/SelectionSet.lean`: multi-selection response-shape proofs.
- `GraphQL/ResponseShape.lean`: response-shape construction and inclusion.
- `GraphQL/NormalForm.lean`: ground normal form scaffold.
- `GraphQL/Execution.lean`: resolver-based execution used by the data model.
- `GraphQL/Validation.lean`: current operation validity assumptions.

## Development Notes

Keep raw syntax permissive and put invariants in validation or well-formedness
predicates. Prefer small, proof-friendly definitions over feature expansion.
When adding scope, update `docs/spec-conformance-plan.md` first.
