import GraphQL.Execution

namespace GraphQL
namespace Tests
namespace Execution

def genericUnitObject : GraphQL.Execution.Value :=
  .object "Query"

theorem genericUnitObjectSmoke :
    genericUnitObject =
      GraphQL.Execution.Value.object "Query" := by
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

def testStringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .named "String", arguments := [] }

def testObjectFieldDefinition
    (name typeName : Name) (arguments : List InputValueDefinition := []) :
    FieldDefinition :=
  { name := name, outputType := .named typeName, arguments := arguments }

def testEpisodeArgumentDefinition : InputValueDefinition :=
  { name := "episode", inputType := .named "Episode" }

def sampleSchema : Schema :=
  { queryType := "Query"
    types :=
      [ .enum { name := "Episode", values := ["NEWHOPE"] }
      , .object
          { name := "Query"
            fields :=
              [ testObjectFieldDefinition "hero" "Character"
                  [testEpisodeArgumentDefinition]
              , testStringFieldDefinition "name"
              , { name := "age", outputType := .named "Int" } ]
            interfaces := [] }
      , .object
          { name := "Character"
            fields :=
              [ testStringFieldDefinition "name"
              , testObjectFieldDefinition "friends" "Character" ]
            interfaces := [] } ] }

def sampleHeroQuery : Operation :=
  { name := some "HeroName"
    rootType := "Query"
    selectionSet :=
      [ .field "mainHero" "hero" [] [] [
          .field "name" "name" [] [] []
        ]
      ] }

def sampleResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => .object "Character"
      | "Character", "name" => .scalar "Leia"
      | _, _ => .null }

theorem executeHeroQuerySmoke :
    responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema sampleResolvers []
          sampleHeroQuery
          (GraphQL.Execution.Value.object "Query"))
      (.object [("mainHero", .object [("name", .scalar "Leia")])]) = true := by
  native_decide

theorem collectSubfieldsMatchesGroupedSelections
    (field : GraphQL.Execution.ExecutableField)
    (fields : List GraphQL.Execution.ExecutableField) :
    GraphQL.Execution.collectSubfields sampleSchema [] "Query"
        (GraphQL.Execution.Value.object (ObjectRef := PUnit) "Query") (field :: fields)
      =
        GraphQL.Execution.mergeExecutableGroups
          (GraphQL.Execution.collectFields sampleSchema [] "Query"
            (GraphQL.Execution.Value.object (ObjectRef := PUnit) "Query") field.selectionSet)
          (GraphQL.Execution.collectSubfields sampleSchema [] "Query"
            (GraphQL.Execution.Value.object (ObjectRef := PUnit) "Query") fields) := by
  rfl

theorem executeRootSelectionSetSmoke :
    responseEqBool
      (.object
        (GraphQL.Execution.executeRootSelectionSet sampleSchema sampleResolvers []
            (GraphQL.Execution.executeQueryDepthBound sampleHeroQuery)
            "Query"
            (GraphQL.Execution.Value.object "Query")
            sampleHeroQuery.selectionSet))
      (.object [("mainHero", .object [("name", .scalar "Leia")])]) = true := by
  native_decide

end Execution
end Tests
end GraphQL
