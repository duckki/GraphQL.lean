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

`GraphQL.DataModel` is the current bridge from resolver execution to proof
semantics. It models typed object identities, field facts keyed by already
coerced arguments, and deterministic store-backed resolution.

`GraphQL.ResponseShape.Condition.forChildType` is important for nested object
fields: child shapes must reset possible runtime types to the field return type
instead of inheriting the parent object's possible types.

## Proof Plan

The next proof ladder is:

1. Prove data-model execution matches the intended resolver execution for
   store-backed resolvers. The definitions already share the resolver path, so
   this should mostly establish the assumptions and notation needed by later
   theorems.
2. Prove response-shape soundness: every typed response produced by valid
   store-backed execution conforms to `ResponseShape.Shape.ofSemanticOperation`.
3. Prove response-shape stability under semantic lowering from raw operations,
   assuming validation supplies fragment existence and acyclicity.
4. Prove normalizer output satisfies `NormalForm.semanticOperationNormal` under
   schema well-formedness and operation validity assumptions.
5. Prove ground normal form semantic preservation:
   `DataModel.groundNormalFormCorrect`.
6. Only after those proofs, revisit operation equivalence and minimization.

## Related Documentation

- `docs/overview.md`: project structure and module dependency map.
- `docs/references.md`: GraphCoQL notes and proof strategy references.
- `README.md`: build, lint, and entry-point information.

