import GraphQL

namespace GraphQL
namespace Tests
namespace DataModel

open GraphQL.DataModel

def heroAccess : FieldAccess :=
  { name := "hero", arguments := [] }

def friendsAccess : FieldAccess :=
  { name := "friends", arguments := [] }

def nameAccess : FieldAccess :=
  { name := "name", arguments := [] }

def heroEpisodeArg : Argument :=
  { name := "episode", value := .enum "JEDI" }

def heroFormatArg : Argument :=
  { name := "format", value := .string "compact" }

def heroAccessWithArgsA : FieldAccess :=
  { name := "hero", arguments := [heroEpisodeArg, heroFormatArg] }

def heroAccessWithArgsB : FieldAccess :=
  { name := "hero", arguments := [heroFormatArg, heroEpisodeArg] }

def searchFilterArgA : Argument :=
  { name := "filter", value := .object [("b", .int 2), ("a", .int 1)] }

def searchFilterArgB : Argument :=
  { name := "filter", value := .object [("a", .int 1), ("b", .int 2)] }

def searchAccessWithArgsA : FieldAccess :=
  { name := "search", arguments := [searchFilterArgA] }

def searchAccessWithArgsB : FieldAccess :=
  { name := "search", arguments := [searchFilterArgB] }

def heroPath : ObjectPath :=
  FieldAccess.childPath [] heroAccess

def firstFriendPath : ObjectPath :=
  FieldAccess.childListElementPath [] friendsAccess 0

def firstHeroFriendPath : ObjectPath :=
  FieldAccess.childListElementPath heroPath friendsAccess 0

def queryType : ObjectType :=
  { name := "Query",
    fields := [
      { name := "hero", outputType := .named "Character" }
    ] }

def characterType : ObjectType :=
  { name := "Character",
    fields := [
      { name := "name", outputType := .named "String" },
      { name := "friends", outputType := .list (.named "Character") }
    ] }

def graphSchema : Schema :=
  { queryType := "Query",
    types := [.object queryType, .object characterType] }

def rootNode : ObjectNode :=
  { typeName := "Query",
    path := [] }

def heroNode : ObjectNode :=
  { typeName := "Character",
    path := heroPath,
    properties := [(nameAccess, .scalar "R2-D2")] }

def firstHeroFriendNode : ObjectNode :=
  { typeName := "Character",
    path := firstHeroFriendPath,
    properties := [(nameAccess, .scalar "C-3PO")] }

def heroEdge : ObjectEdge :=
  { sourcePath := [],
    field := heroAccess,
    index? := none,
    targetType := "Character" }

def firstHeroFriendEdge : ObjectEdge :=
  { sourcePath := heroPath,
    field := friendsAccess,
    index? := some 0,
    targetType := "Character" }

def graphStore : Store :=
  { root := rootNode,
    nodes := [heroNode, firstHeroFriendNode],
    edges := [heroEdge, firstHeroFriendEdge] }

def duplicateHeroEdgeStore : Store :=
  { graphStore with edges := graphStore.edges ++ [heroEdge] }

theorem rootPathSmoke : ([] : ObjectPath) = ([] : ObjectPath) := by
  rfl

theorem singletonPathSmoke :
    heroPath = [.field heroAccess] := by
  rfl

theorem listElementPathSmoke :
    firstFriendPath = [.field friendsAccess, .index 0] := by
  rfl

theorem fieldAccessPathCanonicalizesArgumentOrder :
    FieldAccess.childPath [] heroAccessWithArgsA =
      FieldAccess.childPath [] heroAccessWithArgsB := by
  rfl

theorem fieldAccessPathCanonicalizesInputObjectFieldOrder :
    FieldAccess.childPath [] searchAccessWithArgsA =
      FieldAccess.childPath [] searchAccessWithArgsB := by
  rfl

theorem heroEdgeTargetPathSmoke :
    heroEdge.targetPath = heroPath := by
  rfl

theorem firstHeroFriendEdgeTargetPathSmoke :
    firstHeroFriendEdge.targetPath = firstHeroFriendPath := by
  rfl

theorem heroFieldResolvesToPath :
    graphStore.resolveValue graphSchema "hero" []
      (.object "Query" ([] : ObjectPath)) =
        .object "Character" heroPath := by
  rfl

set_option linter.unusedSimpArgs false in
theorem heroNamePropertyResolves :
    graphStore.resolveValue graphSchema "name" []
      (.object "Character" heroPath) =
        .scalar "R2-D2" := by
  simp [graphStore, graphSchema, Store.resolveValue, Store.lookupNode?,
    Store.lookupNodeIn?, Store.allNodes, Store.fieldAccess,
    Store.indexedMatchingEdges, Store.matchingEdges, Store.firstMatchingEdge?,
    ObjectNode.lookupProperty?, ObjectNode.lookupPropertyIn?,
    Schema.lookupField, Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, Schema.getPossibleTypes,
    TypeDefinition.name, TypeDefinition.fields?, TypeRef.namedType,
    BuiltinScalar.name, List.find?,
    PropertyValue.toValue, typeRefIsListLike,
    ObjectPath.eqBool, PathStep.eqBool, FieldAccess.eqBool,
    FieldAccess.argumentsEqBool, FieldAccess.argumentsEqBoolOrdered,
    FieldAccess.argumentEqBool, FieldAccess.canonicalArgument,
    FieldAccess.canonicalInputValue, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, FieldAccess.insertArgumentSorted,
    FieldAccess.childPath, FieldAccess.childListElementPath,
    FieldAccess.canonical,
    rootNode, heroNode, firstHeroFriendNode, heroPath, heroAccess, nameAccess,
    queryType, characterType]

theorem heroFriendsListResolvesToIndexedPath :
    graphStore.resolveValue graphSchema "friends" []
      (.object "Character" heroPath) =
        .list [.object "Character" firstHeroFriendPath] := by
  rfl

theorem resolverBridgeResolvesHero :
    (graphStore.resolvers graphSchema).resolve "Query" "hero" []
      (.object "Query" ([] : ObjectPath)) =
        Execution.Value.object "Character" heroPath := by
  change (graphStore.resolveValue graphSchema "hero" []
    (GraphQL.DataModel.Value.object "Query" ([] : ObjectPath))).toExecutionValue =
      Execution.Value.object "Character" heroPath
  rw [heroFieldResolvesToPath]
  simp [GraphQL.DataModel.Value.toExecutionValue]

theorem duplicateHeroEdgeRejected :
    ¬ duplicateHeroEdgeStore.nonListCompositeEdgesUnique := by
  simp [duplicateHeroEdgeStore, graphStore, Store.nonListCompositeEdgesUnique,
    Store.nonListCompositeEdgeKeys, ObjectEdge.nonListKey?, heroEdge,
    firstHeroFriendEdge]

end DataModel
end Tests
end GraphQL
