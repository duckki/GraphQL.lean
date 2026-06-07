import GraphQL.Execution

namespace GraphQL
namespace Tests
namespace Execution

def genericUnitObject : GraphQL.Execution.Value Unit :=
  .object "Query" ()

theorem genericUnitObjectSmoke :
    genericUnitObject = GraphQL.Execution.Value.object "Query" () := by
  rfl

end Execution
end Tests
end GraphQL
