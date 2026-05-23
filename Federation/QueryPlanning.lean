import GraphQL

/-!
Spec reference: Apollo Federation query planning behavior and supergraph execution model.
- Query planning uses the composed supergraph, entity keys, `@requires`, `@provides`, and
  subgraph ownership/shareability metadata to choose subgraph fetches.
- Plans must preserve the GraphQL operation's validation/execution semantics while
  satisfying subgraph boundary constraints.
- Fidelity note: no concrete query-planning definitions are present yet, so there are no
  definition-level spec matches to review in this file.
-/
namespace Federation

namespace QueryPlanning

-- Federation query planning constraints will be modeled here on top of `GraphQL`.

end QueryPlanning

end Federation
