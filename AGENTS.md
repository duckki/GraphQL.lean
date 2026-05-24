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
directives, object-type typed inline fragments with modeled directives, two or
three direct no-directive leaf fields with distinct response names, and any
direct no-directive leaf-field list with distinct response names through
`DataModel.LeafField`. `DataModel.LeafField` also proves those lists are already
normal semantic selection sets and factors their typed execution through
`collectFields_toSelectionSet`, `executeSelectionSet_toSelectionSet`, and
`executeSemanticQuery_toSelectionSet`. It also has response-shape construction
and conformance counterparts through `toShapeFields`,
`collectSelectionSetShapeFields_toSelectionSet`,
`ofSemanticOperation_toSelectionSet`,
`typedFieldsConformToShapeFields`, and
`responseShapeCorrectForTypedExecutionAtRoot_distinctLeafFieldsNoDirectives`.
It also proves list-level normal-form response-shape preservation through
`normalFormPreservesResponseShape_distinctLeafFieldsNoDirectives`. Same-response-name
field merging has started: identical duplicate direct leaf fields are covered by
`NormalForm.normalizeSemanticOperation_twoSameLeafNoDirectives`,
`DataModel.groundNormalFormCorrect_twoSameLeafNoDirectives`,
`DataModel.normalFormPreservesResponseShape_twoSameLeafNoDirectives`, and
`DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameLeafNoDirectives`.
The first composite merge case,
`NormalForm.normalizeSemanticOperation_twoSameCompositeDistinctLeafNoDirectives`,
also has ground semantic preservation in
`DataModel.groundNormalFormCorrect_twoSameCompositeDistinctLeafNoDirectives` and
normal-form response-shape preservation in
`DataModel.normalFormPreservesResponseShape_twoSameCompositeDistinctLeafNoDirectives`.
Typed response-shape soundness for the named composite-output version is covered by
`DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeDistinctLeafNoDirectives`.
The one-level list-valued composite-output version is covered by
`DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeListDistinctLeafNoDirectives`,
using `typedResponseConformsToShapeBool_completeValue_namedComposite_listOneFuel`.
The same response-shape soundness cases now also cover non-null wrappers through
`DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullDistinctLeafNoDirectives`
and
`DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullListDistinctLeafNoDirectives`,
with the proof bodies factored through the `_ofObjectOutput` and `_ofListOutput`
generic theorems. The next proof boundary is lifting the child selection set from
the two-leaf case to the `LeafField` list abstraction. Initial reusable helpers
for that lift are `LeafField.mergeFields_parentVariant_childShapeFields_append`,
`LeafField.mergeWithFuel_parentVariant_childShapeFields_append`, and
`LeafField.typedResponseConformsToShape_completeValue_objectSelectionSet`.
The fuel-polymorphic versions
`LeafField.typedFieldsConformToShapeFieldsWithFuel`,
`LeafField.typedResponseConformsToShape_completeValue_objectSelectionSetWithFuel`,
and `LeafField.typedVariantConformsToShape_parentObjectSelectionSetWithFuel`
are available for the generalized composite merge proof. The current generalized
object-output proof is
`DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofObjectOutput`;
it handles two same-response-name composite parent selections whose child
selection sets are arbitrary direct `LeafField` lists with disjoint response
names. It uses `LeafField.toSelectionSet_append`,
`LeafField.childShape_toSelectionSet`,
`LeafField.typedResponseConformsToShape_completeValue_objectSelectionSetAnyFuel`,
and `LeafField.typedVariantConformsToShape_parentObjectSelectionSetAnyFuel`.
The next boundary is adding the thin named/non-null object-output wrappers and
then lifting the list-output case to the same `LeafField` abstraction.
The store-resolution bridge in `GraphQL.DataModel.Store` includes
`lookupType_name_eq`, `typeIncludesObject_eq_of_lookupObjectType`,
`ObjectRecord.lookupField?_some_conformsToLookupField`,
`Store.resolveValue_conformsToLookupField`,
`Store.resolveValue_ne_scalar_of_compositeLookupField`,
`possibleTypes_eq_nil_of_isLeafType`,
`fieldReturnType?_some_lookupField`, and
`scalar_not_conformsToType_of_possibleTypes_nonempty`.

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
- `GraphQL/DataModel/Store.lean`: store-resolution well-typedness bridge lemmas.
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

Review workflow: do not commit before review. Prepare one reviewable slice at a
time, run the relevant checks, summarize the diff, and wait for the user to ask
for the commit. After committing, stop again for review before continuing to the
next proof or implementation slice, unless the user explicitly asks to continue
past that review boundary.
