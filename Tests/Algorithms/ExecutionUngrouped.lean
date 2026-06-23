import GraphQL.Algorithms.ExecutionUngrouped.Semantics

namespace Tests

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL
open GraphQL.Algorithms.ExecutionUngrouped

example (schema : Schema) (operation : Operation) :
    ungroupedExecutionPreservesSpecExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues depth source hcomplete
  exact executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
    schema operation resolvers variableValues depth source hschema hvalid hcomplete

end ExecutionUngrouped
end Algorithms

end Tests
