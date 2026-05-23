import Federation.Composition
import Federation.QueryPlanning

/-!
Spec reference: Apollo Federation subgraph/supergraph documentation and specs.apollo.dev
federation specs.
- Federation composition: combines subgraph schemas and federation directives into a
  supergraph.
- Federation query planning: decomposes a GraphQL operation into subgraph fetch
  constraints.
- This root module is import-only; concrete federation definitions are not modeled yet.
-/
