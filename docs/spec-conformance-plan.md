# Spec Conformance Plan

This document records the current plain GraphQL scope and proof plan. The
canonical spec target is the GraphQL September 2025 Edition.

The immediate priority is spec conformance for a query-only executable fragment
large enough to prove response-shape analysis and ground normal form
correctness. Fragment minimization and federation are intentionally later work.

## Goals

The current conformance target includes:

- query operation execution semantics,
- object, interface, union, enum, scalar, input object, list, and non-null type
  references as already represented in `GraphQL.Schema`,
- schema well-formedness predicates separated from raw schema syntax,
- field selection validation, argument name validation, required argument
  presence, leaf and composite selection shape, fragment applicability, and field
  merge compatibility,
- named fragments and inline fragments, lowered through `GraphQL.Semantic`,
- variables and the built-in executable directives `@skip` and `@include`,
- possible-object semantics for abstract types,
- a formal data model with typed object identities and field facts,
- response-shape analysis for possible response-name variants,
- ground normal form construction for field merging and abstract-type grounding,
- correctness statements for response-shape analysis and ground normal form.

## Explicitly Skipped

These are out of scope for the current conformance pass:

- mutation execution,
- subscription execution,
- custom directives and directive definitions beyond modeled `@skip` and
  `@include`,
- input coercion and result coercion,
- assuming invalid or uncoerced variable/argument values are rejected here,
- introspection and meta-fields,
- execution errors, request errors, `errors`, `extensions`, and null bubbling,
- serialization details,

The working assumption is that values entering validation/execution are already
coerced and type-conformant. The proof-facing model should state that assumption
explicitly instead of trying to recover full coercion behavior.

## Current Status

The main modules are:

- `GraphQL.Schema`: raw schema syntax, type references, type categories, lookup,
  and possible-object helpers.
- `GraphQL.SchemaWellFormedness`: partial schema well-formedness predicates.
- `GraphQL.Operation`: raw operation syntax, named fragments, variables, and
  modeled directive applications.
- `GraphQL.Semantic`: fragment-inlined semantic operation syntax.
- `GraphQL.Validation`: operation validity predicates for the current fragment.
- `GraphQL.FieldMerge`: same-response-name merge compatibility checks.
- `GraphQL.Execution`: bounded resolver-based execution.
- `GraphQL.ResponseShape`: response-name variant summaries, condition utilities,
  inclusion/equivalence checks, and shape construction.
- `GraphQL.NormalForm`: ground normal form predicates and normalizer scaffold.
- `GraphQL.DataModel`: typed object-store model, store-backed resolvers, typed
  response trees, response-shape conformance checks, and correctness predicates.
- `GraphQL.DataModel.Store`: store-resolution bridge lemmas for connecting
  `Store.resolveValue` results to well-typed schema field facts.
- `GraphQL.DataModel.Directives`: directive-sensitive response-shape soundness
  proofs for modeled `@skip` and `@include` base cases.
- `GraphQL.DataModel.SelectionSet`: multi-selection proof cases and the
  `LeafField` proof abstraction for direct no-directive leaf fields, including
  list-level `CollectFields`, typed execution factoring lemmas, response-shape
  construction, normal-form response-shape preservation, and typed response-shape
  soundness for distinct response names. It also contains the initial
  same-response-name field merging proofs.

`GraphQL.DataModel` is the current bridge from resolver execution to proof
semantics. It models typed object identities, field facts keyed by already
coerced arguments, and deterministic store-backed resolution.

`GraphQL.DataModel.TypedExecution` now gives typed execution over the same data
model while retaining runtime object type names in response objects. The untyped
data-model execution functions are definitionally tied to `GraphQL.Execution`
through store-backed resolvers, and data-model operation equivalence has
reflexivity, symmetry, and transitivity theorems. Typed execution also has
erasure theorems through `TypedExecution.executeOperation_erase`, connecting
typed responses back to the existing `GraphQL.Execution.Response` semantics.

`DataModel.groundNormalFormCorrect` is stated over a shared source-operation
execution fuel budget. This avoids treating normalizer size changes as semantic
changes in the bounded executor: the original and normalized operations are run
with `Execution.executeSemanticQueryFuel operation`. The self-budgeted
`semanticOperationsEquivalentOnData` relation remains available for direct
operation equivalence, but ground normal form proofs should use
`semanticOperationsEquivalentOnDataWithFuel`.

`GraphQL.ResponseShape.Condition.forChildType` is important for nested object
fields: child shapes must reset possible runtime types to the field return type
instead of inheriting the parent object's possible types.

## Proof Plan

The current proof ladder is:

1. Prove data-model execution matches the intended resolver execution for
   store-backed resolvers. Done for the current model via the typed-execution
   erasure theorems.
2. Prove response-shape soundness: every typed response produced by valid
   store-backed execution conforms to `ResponseShape.Shape.ofSemanticOperation`.
   This target is named `DataModel.responseShapeCorrectForTypedExecution`.
   Done for empty selections, no-directive single-leaf selections, and parsed
   `@skip`/`@include` single-leaf selections at a known root runtime type,
   including directives on direct fields, untyped inline fragments, and typed
   inline fragments. Also done for two direct no-directive leaf fields with
   distinct response names, the three-field no-directive extension, and any
   direct no-directive leaf-field list with distinct response names.
3. Prove response-shape stability under semantic lowering from raw operations,
   assuming validation supplies fragment existence and acyclicity.
4. Prove normalizer output satisfies `NormalForm.semanticOperationNormal` under
   schema well-formedness and operation validity assumptions. Done for any
   direct no-directive leaf-field list with distinct response names.
5. Prove ground normal form semantic preservation:
   `DataModel.groundNormalFormCorrect`. Done for direct single-leaf selections
   with or without modeled directives, inline-fragment single-leaf selections
   without directives, and object-type typed inline fragments with modeled
   directives. Also done for two direct no-directive leaf fields with distinct
   response names, the three-field no-directive extension, and any direct
   no-directive leaf-field list with distinct response names through the
   `LeafField` abstraction.
6. Prove normal form preserves response shape:
   `DataModel.normalFormPreservesResponseShape`. Done for direct single-leaf
   selections with or without modeled directives, and inline-fragment single-leaf
   selections without directives. Also done for object-type typed inline
   fragments with modeled directives and two direct no-directive leaf fields
   with distinct response names, plus the three-field no-directive extension.
   Also done for any direct no-directive leaf-field list with distinct response
   names through the `LeafField` abstraction.
7. Extend the `LeafField` proof boundary to same-response-name field merging,
   covering execution grouping, shape variant merging, and normal-form response
   shape preservation. Started with identical duplicate direct leaf fields through
   response-shape soundness, and with two same-response-name composite fields
   whose merged child leaf response names are distinct through ground normal-form
   semantic preservation, normal-form response-shape preservation, and typed
   response-shape soundness for named composite-output fields, one-level
   list-valued composite-output fields, and their non-null wrappers. The helpers
   `DataModel.LeafField.mergeFields_parentVariant_twoChildShapeFields` and
   `DataModel.typedResponseConformsToShapeBool_completeValue_namedComposite_listOneFuel`
   record the corresponding identical-parent-variant shape merge and list
   complete-value conformance bridge. The theorem bodies are factored through
   `_ofObjectOutput` and `_ofListOutput` variants so wrapper-specific cases stay
   thin. Reusable `LeafField` helpers now lift the parent-variant shape merge and
   object `completeValue` response-shape check from the hard-coded two-child case
   to arbitrary direct leaf-field lists:
   `LeafField.mergeFields_parentVariant_childShapeFields_append`,
   `LeafField.mergeWithFuel_parentVariant_childShapeFields_append`, and
   `LeafField.typedResponseConformsToShape_completeValue_objectSelectionSet`.
   Fuel-polymorphic variants now cover the response-shape checker fuel used by
   parent composite fields:
   `LeafField.typedFieldsConformToShapeFieldsWithFuel`,
   `LeafField.typedResponseConformsToShape_completeValue_objectSelectionSetWithFuel`,
   `LeafField.typedVariantConformsToShape_parentObjectSelectionSetWithFuel`,
   `LeafField.typedResponseConformsToShape_completeValue_objectSelectionSetAnyFuel`,
   and `LeafField.typedVariantConformsToShape_parentObjectSelectionSetAnyFuel`.
8. Lift typed response-shape soundness for the same composite merge case from the
   current two distinct child leaf fields to the `LeafField` list abstraction.
   The object-output core is now generalized by
   `DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofObjectOutput`,
   using `LeafField.toSelectionSet_append` and
   `LeafField.childShape_toSelectionSet` to connect child semantic selections
   to collected child response shapes. Thin wrappers now expose named and
   non-null named object-output cases through
   `DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives`
   and
   `DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullLeafFieldsNoDirectives`.
   The list-output case now has reusable element/list bridges:
   `LeafField.typedResponseConformsToShape_completeValue_namedCompositeSelectionSetAnyFuel`
   and
   `LeafField.typedResponseConformsToShape_completeValue_namedCompositeListSelectionSetAnyFuel`.
   The generalized list-output parent theorem is now
   `DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeLeafFieldsNoDirectives_ofListOutput`.
   Thin wrappers now expose list and non-null list cases through
   `DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeListLeafFieldsNoDirectives`
   and
   `DataModel.responseShapeCorrectForTypedExecutionAtRoot_twoSameCompositeNonNullListLeafFieldsNoDirectives`.
   The older two-child public theorem names for named, non-null named, list, and
   non-null list composite parents now delegate to those generalized `LeafField`
   wrappers. Normalization and ground normal-form correctness now also cover two
   same-response-name composite parent fields whose child selection sets are
   arbitrary direct `LeafField` lists, through
   `LeafField.normalizeSemanticOperation_twoSameCompositeLeafFieldsNoDirectives`
   and
   `DataModel.groundNormalFormCorrect_twoSameCompositeLeafFieldsNoDirectives`.
   Response-shape helper lemmas for that lift are now available:
   `LeafField.mergeFields_parentVariant_childShape_nil`,
   `LeafField.childShape_toSelectionSet_unsat`,
   `LeafField.equivalentBool_parentVariant_childShapeFields_self`,
   `LeafField.condition_and_empty`,
   `LeafField.collectSelectionShapeFields_field_toSelectionSet`, and
   `LeafField.collectSelectionShapeFields_field_toSelectionSet_unsat`.
   Normal-form response-shape preservation now also covers that same generalized
   `LeafField` composite merge case through
   `DataModel.normalFormPreservesResponseShapeBool_twoSameCompositeLeafFieldsNoDirectives`
   and
   `DataModel.normalFormPreservesResponseShape_twoSameCompositeLeafFieldsNoDirectives`.
   Next, wire older hard-coded two-child normal-form response-shape theorem
   names through the generalized wrapper, then decide the next merge
   generalization beyond arbitrary direct child `LeafField` lists.
   Bridge lemmas now live in `GraphQL.DataModel.Store`:
   `lookupType_name_eq`, `typeIncludesObject_eq_of_lookupObjectType`,
   `ObjectRecord.lookupField?_some_conformsToLookupField`,
   `Store.resolveValue_conformsToLookupField`,
   `Store.resolveValue_ne_scalar_of_compositeLookupField`,
   `possibleTypes_eq_nil_of_isLeafType`, `fieldReturnType?_some_lookupField`, and
   `scalar_not_conformsToType_of_possibleTypes_nonempty`.
9. Only after those proofs, revisit operation equivalence and minimization.

## Related Documentation

- `docs/overview.md`: project structure and module dependency map.
- `docs/references.md`: GraphCoQL notes and proof strategy references.
- `README.md`: build, lint, and entry-point information.
