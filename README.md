# graphql-lean

Lean models for GraphQL and, later, GraphQL federation.

## Part 1: Plain GraphQL

The current scaffold separates the plain GraphQL work into small modules:

- `GraphQL.Syntax`: schema-independent names, type references, directive applications, operations, fields, named fragment spreads, inline fragments, fragments, and operation size.
- `GraphQL.Schema`: scalar, enum, object, interface, and union types; field lookup; possible-object inclusion for abstract types.
- `GraphQL.Validation`: validation as a proposition over a schema and operation, including fragment applicability by possible-object overlap.
- `GraphQL.Execution`: execution as a function parameterized by abstract resolver functions, with `@skip` / `@include` filtering for fields, named spreads, and inline spreads.
- `GraphQL.ResponseShape`: response shapes plus shape-to-shape inclusion and equivalence.
- `GraphQL.Minimization`: finite-candidate operation minimization and the minimality theorem shape.

The intended minimization proof split is:

1. Define a finite candidate generator for fragment-introducing rewrites of a fragment-free operation.
2. Prove the generator is sound: every generated operation has the same response shape as the input.
3. Prove the generator is complete: every operation equivalent to the input, up to fragment-name alpha-renaming and the chosen size metric, appears in the candidate set.
4. Use the generic finite minimizer theorem to prove the selected output is minimal.

## Part 2: Federation

Part 2 should build on Part 1 by modeling:

- composition rules for directives,
- composite schema constraints,
- query planning as constraint solving.

Federation starts as a separate top-level Lean library root:

- `Federation.Composition`
- `Federation.QueryPlanning`
