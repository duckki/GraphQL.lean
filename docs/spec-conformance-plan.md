# Spec Conformance Plan

This document records the current plain GraphQL scope and proof plan. The
canonical spec target is the GraphQL September 2025 Edition.

The immediate priority is spec conformance for a query-only executable fragment
large enough to state semantic execution and ground-normal-form correctness.

## Goals

The current conformance target includes:

- query operation execution semantics,
- object, interface, union, enum, scalar, input object, list, and non-null type
  references as represented in `GraphQL.Schema`,
- schema well-formedness predicates separated from raw schema syntax, including
  default-value validity, non-empty type member/field lists, and
  object/interface implementation compatibility,
- field selection validation, argument name validation, required argument
  presence, variable-use compatibility at input locations, leaf and composite
  selection shape, fragment applicability, and field merge compatibility,
- named fragments and inline fragments, lowered through `GraphQL.Semantic`,
- variables and the built-in executable directives `@skip` and `@include`,
- possible-object semantics for abstract types,
- a formal data model with typed object identities and field facts,
- ground normal form construction for field merging and abstract-type grounding,
- correctness statements for ground normal form over store-backed execution.

## Explicitly Skipped

These are out of scope for the current conformance pass:

- mutation execution,
- subscription execution,
- custom directives and directive definitions beyond modeled `@skip` and
  `@include`,
- full input coercion and result coercion,
- scalar and enum literal coercion details; validation records structural
  input-object and variable/input-type compatibility, while assuming values are
  already coerced where scalar semantics would matter,
- introspection and meta-fields,
- execution errors, request errors, `errors`, `extensions`, and null bubbling,
- serialization details,
- response-shape analysis,
- directive-sensitive normal-form semantics; validation and execution still
  model `@skip` and `@include`, but the current normal-form proof path assumes
  source operations have no modeled directives,
- minimization,
- federation.

The working assumption is that values entering validation/execution are already
coerced and type-conformant. The proof-facing model should state that assumption
explicitly instead of trying to recover full coercion behavior.

## Current Status

The main modules are:

- `GraphQL.Schema`: raw schema syntax, type references, type categories, lookup,
  possible-object helpers, constant default-value validation, and output subtype
  helpers for interface implementation checks.
- `GraphQL.SchemaWellFormedness`: schema well-formedness predicates for the
  scoped fragment, including uniqueness, non-empty definition/member lists,
  valid type references/defaults, query root existence, and object/interface
  implementation compatibility.
- `GraphQL.Operation`: raw operation syntax, named fragments, variables, and
  modeled directive applications.
- `GraphQL.Semantic`: fragment-inlined semantic operation syntax.
- `GraphQL.Validation`: operation validity predicates for the current fragment,
  including recursive input-object validation and spec-style variable-use
  compatibility with the nullable-variable default exception.
- `GraphQL.FieldMerge`: same-response-name merge compatibility checks.
- `GraphQL.Execution`: bounded resolver-based execution.
- `GraphQL.NormalForm`: ground normal form predicates and normalizer scaffold.
- `GraphQL.DataModel`: typed object-store model, store-backed resolvers, and
  semantic equivalence/correctness predicates over store-backed execution.
- `GraphQL.DataModel.Store`: store-resolution bridge lemmas for connecting
  `Store.resolveValue` results to well-typed schema field facts.

`GraphQL.DataModel` is the current bridge from resolver execution to proof
semantics. It models typed object identities, field facts keyed by already
coerced arguments, and deterministic store-backed resolution. Store field keys
compare arguments and input-object fields by GraphQL's unordered semantics after
validation has ruled out duplicate names.

`GraphQL.NormalForm` follows the GraphCoQL-level normal-form target under a
directive-free source-operation assumption. It merges fields and grounds
abstract selections without a separate directive-erasure pass.
Directive-sensitive normalization can be revisited after the directive-free
semantic preservation proof is stable.

`DataModel.groundNormalFormCorrect` is stated over
`semanticOperationsEquivalentOnData`. The ground-type normalizer itself has no
fuel parameter: it terminates by structural descent on semantic selection-set
size while merging same-response-name fields and grounding abstract returns
through possible object types.

## Proof Plan

The current proof ladder is:

1. Keep schema and operation validation faithful to the scoped GraphQL spec
   definitions.
2. Keep data-model execution definitionally tied to `GraphQL.Execution` through
   store-backed resolvers.
3. Prove normalizer output satisfies `NormalForm.semanticOperationNormal` under
   schema well-formedness and operation-validity assumptions.
4. Prove ground normal form semantic preservation:
   `DataModel.groundNormalFormCorrect`.
5. Revisit broader operation transformation algorithms only after the scoped
   validation, execution, and normal-form semantics are stable.

## Related Documentation

- `docs/overview.md`: project structure and module dependency map.
- `docs/references.md`: GraphCoQL notes and proof strategy references.
- `README.md`: build, lint, and entry-point information.
