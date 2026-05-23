import GraphQL

/-!
Spec reference: Apollo Federation subgraph specification and federation directive
specifications.
- Subgraph schema additions: federation adds `_Service`, `_Entity`, `_Any`, `FieldSet`,
  and federation/link directives to subgraph schemas.
- Federation directives such as `@key`, `@external`, `@requires`, `@provides`,
  `@shareable`, and `@inaccessible` drive composition validity and supergraph
  construction.
- Fidelity note: no concrete composition definitions are present yet, so there are no
  definition-level spec matches to review in this file.
-/
namespace Federation

namespace Composition

-- Federation composition rules will be modeled here on top of `GraphQL.Schema`.

end Composition

end Federation
