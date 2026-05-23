# Project Overview

`graphql-lean` is a Lean formalization workspace for GraphQL and GraphQL federation.

Part 1 models plain GraphQL. Part 2 builds on Part 1 to model federation concepts such as composition and query planning.

Canonical GraphQL specification reference: [GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).

## Dependency Diagram

```mermaid
flowchart TD
  Schema["GraphQL.Schema"]
  SchemaWF["GraphQL.SchemaWellFormedness"]
  Operation["GraphQL.Operation"]
  FieldMerge["GraphQL.FieldMerge"]
  Validation["GraphQL.Validation"]
  NormalForm["GraphQL.NormalForm"]
  ResponseShape["GraphQL.ResponseShape"]
  Execution["GraphQL.Execution"]
  Minimization["GraphQL.Minimization"]
  GraphQLRoot["GraphQL"]

  FederationComposition["Federation.Composition"]
  FederationQueryPlanning["Federation.QueryPlanning"]
  FederationRoot["Federation"]

  Schema --> SchemaWF
  Schema --> Operation
  Operation --> FieldMerge
  FieldMerge --> Validation
  Operation --> NormalForm
  Validation --> Execution
  Operation --> ResponseShape
  Operation --> Minimization

  SchemaWF --> GraphQLRoot
  Validation --> GraphQLRoot
  NormalForm --> GraphQLRoot
  ResponseShape --> GraphQLRoot
  Execution --> GraphQLRoot
  Minimization --> GraphQLRoot

  GraphQLRoot --> FederationComposition
  GraphQLRoot --> FederationQueryPlanning
  FederationComposition --> FederationRoot
  FederationQueryPlanning --> FederationRoot
```

## Part 1: Plain GraphQL

The plain GraphQL layer is organized under the top-level `GraphQL` library root.

- `GraphQL.Schema`: shared names, type references, input values, built-in scalars, custom scalars, enums, objects, interfaces, unions, input objects, field definitions with output types, argument definitions with input types, field lookup, and possible-object inclusion for abstract types.
- `GraphQL.SchemaWellFormedness`: schema-level invariants separated from raw schema syntax, including unique type/field/argument names, root query object type, valid type references, and object/interface/union consistency.
- `GraphQL.Operation`: operation syntax, field arguments, variable definitions, built-in directive applications, selections, named fragment spreads, inline fragments, fragments, operation size, fragment-spread collection, and shared selection helpers for response names, filtering, and selection-set merging.
- `GraphQL.FieldMerge`: same-response-name field collection and merge compatibility, including response-shape compatibility and recursive subfield merge checks.
- `GraphQL.Validation`: validation as a proposition over a schema and operation, including variable definitions, duplicate argument checks, required argument checks, recursive input/output type checks, non-empty required selection sets, field merge checks, unique fragment names, spread resolution, acyclic fragment dependencies, and fragment applicability by possible-object overlap.
- `GraphQL.NormalForm`: ground-typed normal form and non-redundancy predicates plus a bounded normalization pass for field merging and abstract-type grounding.
- `GraphQL.ResponseShape`: an operation summary between raw operation syntax and ground-type normal form. It records response keys, conditional field variants, child shapes, shape inclusion, and shape equivalence.
- `GraphQL.Execution`: execution as a function parameterized by abstract resolver functions, with field arguments passed to resolvers and `@skip` / `@include` filtering for fields, named spreads, and inline spreads.
- `GraphQL.Minimization`: finite-candidate operation minimization parameterized by an explicit operation-equivalence predicate, plus the generic minimality theorem.

### Plain GraphQL Flow

The current Part 1 flow is:

1. `GraphQL.Schema` and `GraphQL.Operation` define raw syntax.
2. `GraphQL.SchemaWellFormedness`, `GraphQL.FieldMerge`, and `GraphQL.Validation` state well-formedness and operation validity.
3. `GraphQL.ResponseShape` summarizes operations as unnormalized conditional response-key variants.
4. `GraphQL.Execution` gives bounded execution as a function, parameterized by abstract resolvers.
5. `GraphQL.NormalForm` and `GraphQL.Minimization` provide the normalization/minimization proof scaffolding.

Validation assumptions should be used when proving semantic facts about later stages. Raw syntax remains permissive; validation supplies the invariants that later proofs should rely on.

### Response Shape Model

Response shapes currently distinguish only:

- `scalar`
- `object fields`

Object shapes are keyed by response name. Each key maps to one or more conditional variants. A variant records:

- the selected field definition, modeled as `fieldName` plus arguments,
- a type condition, modeled as an optional set/list of possible object types,
- a boolean condition, modeled as a conjunction of boolean variable literals `v` or `not v`,
- the child response shape for that variant.

Variants under a response key are interpreted disjunctively and are not normalized. Their conditions may overlap, and both variants may be true. For example, a key may contain `field(arg: 1)` on `{T}` with child `{a}` and another `field(arg: 1)` on `{T, U}` with child `{b}`.

This intentionally ignores concrete scalar values, object identities, list/null completion, resolver internals, and error propagation. It is a structural operation summary, not a full response-value model and not a definition of operation equivalence.

`GraphQL.ResponseShape` provides two views of inclusion:

- propositional inclusion, `Shape.includes required available`
- computable inclusion, `Shape.includesBool required available`

The module proves soundness and completeness bridges between those two forms. Equivalence is inclusion in both directions, again with both propositional and boolean APIs.

Shape merging is also structural. Object shapes merge by response name; variants under the same key merge only when their type condition, boolean condition, and selected field definition match. This is intentionally weaker than normal-form construction because overlapping variants are preserved instead of normalized away.

Response-shape equivalence is weaker than operation equivalence. Operation equivalence should be determined through normal forms or a separate semantic equivalence theorem. Shape equivalence can be used as a supporting invariant, but it is not sufficient by itself.

### Shape And Normal Form

`GraphQL.ResponseShape` is an intermediate summary of an operation. It is closer to operation syntax than ground-type normal form: it records response-key variants with type and boolean conditions, but it does not split or normalize overlapping conditions.

Operation equivalence should be determined by normal forms or a separate semantic equivalence theorem. Shape equivalence is useful as a supporting invariant and as a staging point for minimization, but it is not sufficient by itself.

### Minimization Plan

The intended minimization proof split is:

The pieces already in place are:

- response-shape inclusion and equivalence, with boolean/propositional bridges,
- a generic finite minimizer theorem over any finite list of candidates equivalent under an explicit operation-equivalence predicate.

The remaining proof ladder is:

1. Make normal forms canonical enough to decide operation equivalence up to fragment-name alpha-renaming.
2. Prove normalization preserves execution semantics and response shape as a supporting invariant.
3. Define a finite candidate generator for fragment-introducing rewrites of a fragment-free operation.
4. Prove generator soundness: every generated operation has the same normal-form semantics as the input.
5. Prove generator completeness for the chosen normal form, modulo fragment-name alpha-renaming and the operation size metric.
6. Instantiate the generic finite minimizer theorem with that candidate generator.

The normal-form work is the bridge to this proof. Fragment minimization should operate over normalized or canonicalized selection sets so equivalence is tractable.

## Part 2: Federation

Federation starts as a separate top-level Lean library root.

- `Federation.Composition`: composition rules for directives and composite schema constraints.
- `Federation.QueryPlanning`: query planning as constraint solving.

Part 2 should depend on the plain GraphQL semantics and validation core rather than duplicating GraphQL concepts.
