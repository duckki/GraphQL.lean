# Project Overview

`graphql-lean` is a Lean formalization workspace for a scoped plain GraphQL
fragment.

Canonical GraphQL specification reference:
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).

## Dependency Diagram

```mermaid
flowchart TD
  Schema["GraphQL.Schema"]
  SchemaWF["GraphQL.SchemaWellFormedness"]
  Operation["GraphQL.Operation"]
  Validation["GraphQL.Validation"]
  NormalForm["GraphQL.NormalForm"]
  NormalFormGround["GraphQL.NormalForm.GroundTypeNormalization"]
  CompleteNormalization["GraphQL.NormalForm.CompleteNormalization"]
  Execution["GraphQL.Execution"]
  DataModel["GraphQL.DataModel"]
  DataModelStore["GraphQL.DataModel.Store"]
  GraphQLRoot["GraphQL"]

  Schema --> SchemaWF
  Schema --> Operation
  Operation --> Validation
  Operation --> NormalForm
  Operation --> Execution
  Execution --> DataModel
  SchemaWF --> NormalForm
  Validation --> NormalForm
  Validation --> DataModel
  DataModel --> NormalForm
  NormalForm --> NormalFormGround
  NormalForm --> CompleteNormalization
  DataModel --> DataModelStore

  SchemaWF --> GraphQLRoot
  Operation --> GraphQLRoot
  Validation --> GraphQLRoot
  NormalForm --> GraphQLRoot
  NormalFormGround --> GraphQLRoot
  CompleteNormalization --> GraphQLRoot
  Execution --> GraphQLRoot
  DataModel --> GraphQLRoot
  DataModelStore --> GraphQLRoot
```

## Modules

The plain GraphQL layer is organized under the top-level `GraphQL` library root.

- `GraphQL.Schema`: shared names, type references, input values, constant input
  values, built-in scalars, custom scalars, enums, objects, interfaces, unions,
  input objects, field definitions, argument definitions, lookup helpers,
  possible-object inclusion, constant default-value validation, and output
  subtype checks.
- `GraphQL.SchemaWellFormedness`: schema-level invariants separated from raw
  schema syntax, including unique names, non-empty definition/member lists,
  root query object type, valid type references/defaults, and object/interface
  implementation compatibility.
- `GraphQL.Operation`: operation syntax, field arguments, variable definitions,
  built-in directive applications, selections, inline fragments, operation size,
  and shared selection helpers. Named fragment definitions and fragment spreads
  are intentionally out of scope.
- `GraphQL.Validation`: validation as a proposition over a schema and operation,
  including variable definitions/defaults, variable-use compatibility, argument
  checks, recursive input/output type checks, required non-empty selection sets,
  modeled `@skip`/`@include`, same-response-name field merge checks, and
  inline-fragment applicability.
- `GraphQL.NormalForm`: ground-typed normal form and non-redundancy predicates over
  operation selection sets, a normalization pass for field merging and
  abstract-type grounding, and the public semantic preservation and store-backed
  correctness predicates for directive-free ground-type normalization.
- `GraphQL.NormalForm.GroundTypeNormalization`: proof-facing lemmas for the
  directive-free ground-type normalizer.
- `GraphQL.NormalForm.CompleteNormalization`: proof-facing lemmas for complete
  normalization, which lifts modeled `@skip`/`@include` behavior into Boolean
  case branches and keeps bottom-branch fields directive-free. Its proof
  modules separate variable/directive facts, BoolCase wrappers, static
  collection, normal-shape facts, operation variables/wrappers, field and
  inline static-collection execution cases, BoolCase runtime selection,
  child completion, scoped resolver/store bridges, and final root semantics.
- `GraphQL.Execution`: execution over operation selections as a function
  parameterized by abstract resolver functions. It collects executable fields by
  response name, resolves each response name once, passes field arguments to
  resolvers, and applies `@skip` / `@include` filtering. Runtime object values
  carry their GraphQL object type plus an optional resolver-owned opaque object
  reference; final responses do not carry object identity.
- `GraphQL.DataModel`: an extensional graph-backed model for the scoped
  conformance target. It represents typed nodes, node-local scalar properties,
  source-id/field-labeled object edges, unordered GraphQL argument/input-object
  key comparison, graph-root execution, schema-conformant field labels, node-id
  uniqueness, edge/property key uniqueness, list-index discipline, graph
  well-typedness predicates, store-backed resolvers, and data-model equivalence
  of operations.
- `GraphQL.DataModel.Store`: store-resolution bridge lemmas connecting
  node/type-keyed store lookup and composite-field resolution to schema facts.

## Flow

The current flow is:

1. `GraphQL.Schema` and `GraphQL.Operation` define raw syntax.
2. `GraphQL.SchemaWellFormedness` and `GraphQL.Validation` state
   well-formedness and operation validity.
3. `GraphQL.Execution` gives bounded execution over operation selections by
   collecting fields by response name, then resolving each response name once.
4. `GraphQL.DataModel` describes the typed graph store.
5. `GraphQL.DataModel` instantiates spec execution with store-backed resolvers
   over that graph while keeping object references abstract to execution.
6. `GraphQL.NormalForm` provides normalization definitions and public
   ground-normal-form correctness predicates.
7. `GraphQL.NormalForm.GroundTypeNormalization` provides proof-facing
   ground-type lemmas.
8. `GraphQL.NormalForm.CompleteNormalization` provides proof-facing lemmas for
   directive-aware Boolean case branch normalization.

Normalization consumes `GraphQL.Operation` directly. The directive-free
`normalizeOperation` proof path assumes source operations have no modeled
directives.

Complete normalization is the directive-aware path: it enumerates modeled
Boolean directive variables once at the operation root, creates one
unconditional inline-fragment case branch per complete case, and
statically collects directive-free fields for each ground type under the
selected case. Nested field child normalization receives that case
as proof context and does not introduce another directive-only BoolCase DNF.

Raw syntax remains permissive. Validation supplies the invariants that later
semantic proofs should rely on.

The completed ground-type normal form correctness proof is summarized in
`docs/ground-type-normal-form-proof.md`.

Lean module organization rules are documented in
`docs/lean-organization.md`.
