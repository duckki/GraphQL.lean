import GraphQL.NormalForm

/-!
Proof-facing lemmas for directive-free ground-type normalization.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem normalizeOperation_name (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).name = operation.name := by
  rfl

theorem normalizeOperation_rootType (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).rootType = operation.rootType := by
  rfl

theorem normalizeOperation_variableDefinitions (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).variableDefinitions
      = operation.variableDefinitions := by
  rfl

end GroundTypeNormalization

end NormalForm

end GraphQL
