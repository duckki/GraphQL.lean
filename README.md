# graphql-lean

Lean models for GraphQL.

Canonical GraphQL specification reference:
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).

For the project structure, dependency diagram, and module overview, see
[docs/overview.md](docs/overview.md).

For the current spec-conformance scope and proof plan, see
[docs/spec-conformance-plan.md](docs/spec-conformance-plan.md).

For project-specific normal forms and verified algorithms, see
[docs/normal-form.md](docs/normal-form.md) and
[docs/algorithms.md](docs/algorithms.md).

## Build

Build all Lean targets:

```sh
lake build
```

Run linting:

```sh
lake lint
```

The lint target runs Lean's built-in linters with documentation warnings disabled.
It also enforces project-local community-style checks inspired by common
Mathlib/CSLib practice: lines at 100 columns except URLs, no trailing
whitespace or tabs, no unscoped diagnostic/resource `set_option`, no bare
`open Classical`, no lambda or dollar syntax, no double underscores in
declaration names, and a 1500-line soft file limit.

The main top-level libraries are:

- `GraphQL`
