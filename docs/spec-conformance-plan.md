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
  selection shape, inline-fragment applicability, and field merge compatibility,
- inline fragments,
- variables and the built-in executable directives `@skip` and `@include`,
- possible-object semantics for abstract types,
- a formal data model with typed object identities and field facts,
- ground normal form construction for field merging and abstract-type grounding,
- correctness statements for ground normal form over store-backed execution.

## Explicitly Skipped

These are out of scope for the current conformance pass:

- mutation execution,
- subscription execution,
- named fragment definitions and fragment spreads,
- custom directives and directive definitions beyond modeled `@skip` and
  `@include`,
- full input coercion and result coercion,
- scalar and enum literal coercion details; validation records structural
  input-object and variable/input-type compatibility, while assuming values are
  already coerced where scalar semantics would matter,
- introspection and meta-fields,
- execution errors, request errors, `errors`, `extensions`, and null bubbling,
- serialization details,

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
- `GraphQL.Operation`: operation syntax, variables, inline fragments, and
  modeled directive applications.
- `GraphQL.Validation`: operation validity predicates for the current fragment,
  including recursive input-object validation and spec-style variable-use
  compatibility with the nullable-variable default exception, plus
  same-response-name merge compatibility checks.
- `GraphQL.Execution`: bounded resolver-based execution.
- `GraphQL.DataModel`: typed graph store with path-based object identities,
  store-backed resolvers, and semantic equivalence/correctness predicates over
  graph-backed execution.
- `GraphQL.DataModel.Store`: store-resolution bridge lemmas for connecting
  path-based graph lookup and composite-field resolution to schema facts.

## Related Documentation

- `docs/overview.md`: project structure and module dependency map.
- `docs/references.md`: GraphCoQL notes and proof strategy references.
- `README.md`: build, lint, and entry-point information.
