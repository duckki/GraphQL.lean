import Tests.Common

namespace GraphQL
namespace Tests
namespace Execution

def genericUnitObject : GraphQL.Execution.Value Unit :=
  .object "Query" ()

theorem genericUnitObjectSmoke :
    genericUnitObject = GraphQL.Execution.Value.object "Query" () := by
  rfl

mutual
  def responseEqBool :
      GraphQL.Execution.Response -> GraphQL.Execution.Response -> Bool
    | .null, .null => true
    | .scalar left, .scalar right => left == right
    | .object left, .object right => responseFieldsEqBool left right
    | .list left, .list right => responseListEqBool left right
    | _, _ => false

  def responseListEqBool :
      List GraphQL.Execution.Response -> List GraphQL.Execution.Response -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        responseEqBool left right && responseListEqBool lefts rights
    | _, _ => false

  def responseFieldsEqBool :
      List (Name × GraphQL.Execution.Response) ->
        List (Name × GraphQL.Execution.Response) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        (leftName == rightName)
          && responseEqBool leftValue rightValue
          && responseFieldsEqBool lefts rights
    | _, _ => false
end

def sampleResolvers : GraphQL.Execution.Resolvers String :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => .object "Character" "hero"
      | "Character", "name" => .scalar "Leia"
      | _, _ => .null }

theorem executeHeroQuerySmoke :
    responseEqBool
      (GraphQL.Execution.executeQuery sampleSchema sampleResolvers []
        sampleHeroQuery (.object "Query" "root"))
      (.object [("mainHero", .object [("name", .scalar "Leia")])]) = true := by
  native_decide

end Execution
end Tests
end GraphQL
