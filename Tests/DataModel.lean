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

def heroEpisodeStringArg : Argument :=
  { name := "episode", value := .string "JEDI" }

def heroAccessWithArgsA : FieldAccess :=
  { name := "hero", arguments := [heroEpisodeArg, heroFormatArg] }

def heroAccessWithArgsB : FieldAccess :=
  { name := "hero", arguments := [heroFormatArg, heroEpisodeArg] }

def heroAccessWithStringArgsA : FieldAccess :=
  { name := "hero", arguments := [heroEpisodeStringArg, heroFormatArg] }

def heroAccessWithStringArgsB : FieldAccess :=
  { name := "hero", arguments := [heroFormatArg, heroEpisodeStringArg] }

def nameAccessWithUnexpectedArg : FieldAccess :=
  { name := "name", arguments := [heroFormatArg] }

def heroAccessWithUnexpectedArg : FieldAccess :=
  { name := "hero", arguments := [heroFormatArg] }

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

def secondHeroFriendPath : ObjectPath :=
  FieldAccess.childListElementPath heroPath friendsAccess 1

def heroPathWithStringArgs : ObjectPath :=
  FieldAccess.childPath [] heroAccessWithStringArgsA

def heroPathWithUnexpectedArg : ObjectPath :=
  FieldAccess.childPath [] heroAccessWithUnexpectedArg

def rawHeroPathWithStringArgsA : ObjectPath :=
  [.field heroAccessWithStringArgsA]

def rawHeroPathWithStringArgsB : ObjectPath :=
  [.field heroAccessWithStringArgsB]

def queryType : ObjectType :=
  { name := "Query",
    fields := [
      { name := "hero", outputType := .named "Character" }
    ] }

def queryTypeWithHeroArgs : ObjectType :=
  { name := "Query",
    fields := [
      { name := "hero",
        outputType := .named "Character",
        arguments := [
          { name := "episode", inputType := .named "String" },
          { name := "format", inputType := .named "String" }
        ] }
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

def graphSchemaWithHeroArgs : Schema :=
  { queryType := "Query",
    types := [.object queryTypeWithHeroArgs, .object characterType] }

def rootNode : ObjectNode :=
  { typeName := "Query",
    path := [] }

def mismatchedRootNode : ObjectNode :=
  { typeName := "Character",
    path := [] }

def heroNode : ObjectNode :=
  { typeName := "Character",
    path := heroPath,
    properties := [(nameAccess, .scalar "R2-D2")] }

def heroNodeWithUnexpectedPropertyArg : ObjectNode :=
  { heroNode with properties := [(nameAccessWithUnexpectedArg, .scalar "R2-D2")] }

def heroNodeWithDuplicateProperties : ObjectNode :=
  { heroNode with
    properties := [
      (nameAccess, .scalar "R2-D2"),
      (nameAccess, .scalar "Artoo")
    ] }

def heroNodeWithStringArgsA : ObjectNode :=
  { heroNode with path := rawHeroPathWithStringArgsA }

def heroNodeWithStringArgsB : ObjectNode :=
  { heroNode with path := rawHeroPathWithStringArgsB }

def heroNodeWithUnexpectedArgPath : ObjectNode :=
  { heroNode with path := heroPathWithUnexpectedArg }

def firstHeroFriendNode : ObjectNode :=
  { typeName := "Character",
    path := firstHeroFriendPath,
    properties := [(nameAccess, .scalar "C-3PO")] }

def secondHeroFriendNode : ObjectNode :=
  { typeName := "Character",
    path := secondHeroFriendPath,
    properties := [(nameAccess, .scalar "Luke")] }

def heroEdge : ObjectEdge :=
  { sourcePath := [],
    field := heroAccess,
    index? := none,
    targetType := "Character" }

def heroEdgeWithStringArgs : ObjectEdge :=
  { sourcePath := [],
    field := heroAccessWithStringArgsA,
    index? := none,
    targetType := "Character" }

def heroEdgeWithUnexpectedArg : ObjectEdge :=
  { sourcePath := [],
    field := heroAccessWithUnexpectedArg,
    index? := none,
    targetType := "Character" }

def firstHeroFriendEdge : ObjectEdge :=
  { sourcePath := heroPath,
    field := friendsAccess,
    index? := some 0,
    targetType := "Character" }

def secondHeroFriendEdge : ObjectEdge :=
  { sourcePath := heroPath,
    field := friendsAccess,
    index? := some 1,
    targetType := "Character" }

def graphStore : Store :=
  { root := rootNode,
    nodes := [heroNode, firstHeroFriendNode],
    edges := [heroEdge, firstHeroFriendEdge] }

def duplicateHeroEdgeStore : Store :=
  { graphStore with edges := graphStore.edges ++ [heroEdge] }

def mismatchedRootStore : Store :=
  { root := mismatchedRootNode }

def unexpectedPropertyArgumentStore : Store :=
  { root := rootNode,
    nodes := [heroNodeWithUnexpectedPropertyArg],
    edges := [heroEdge] }

def unexpectedEdgeArgumentStore : Store :=
  { root := rootNode,
    nodes := [heroNodeWithUnexpectedArgPath],
    edges := [heroEdgeWithUnexpectedArg] }

def duplicateSemanticPathStore : Store :=
  { root := rootNode,
    nodes := [heroNodeWithStringArgsA, heroNodeWithStringArgsB],
    edges := [heroEdgeWithStringArgs] }

def duplicatePropertyStore : Store :=
  { root := rootNode,
    nodes := [heroNodeWithDuplicateProperties],
    edges := [heroEdge] }

def duplicateListIndexStore : Store :=
  { graphStore with edges := graphStore.edges ++ [firstHeroFriendEdge] }

def gapListIndexStore : Store :=
  { root := rootNode,
    nodes := [heroNode, secondHeroFriendNode],
    edges := [heroEdge, secondHeroFriendEdge] }

def outOfOrderListStore : Store :=
  { root := rootNode,
    nodes := [heroNode, firstHeroFriendNode, secondHeroFriendNode],
    edges := [heroEdge, secondHeroFriendEdge, firstHeroFriendEdge] }

def orphanNodeStore : Store :=
  { root := rootNode,
    nodes := [heroNode],
    edges := [] }

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

theorem mismatchedRootRejected :
    ¬ mismatchedRootStore.rootWellTyped graphSchema := by
  simp [mismatchedRootStore, graphSchema, Store.rootWellTyped,
    Schema.typeIncludesObject, Schema.getPossibleTypes, Schema.lookupType,
    Schema.allTypes, Schema.builtinScalarDefinitions, TypeDefinition.name,
    BuiltinScalar.name, mismatchedRootNode, queryType, characterType]

theorem unexpectedPropertyArgumentRejected :
    ¬ nameAccessWithUnexpectedArg.argumentsWellTyped graphSchema
      { name := "name", outputType := .named "String" } := by
  simp [FieldAccess.argumentsWellTyped, Validation.argumentsValid,
    Validation.argumentValid, Schema.lookupArgumentDefinition,
    nameAccessWithUnexpectedArg, heroFormatArg]

theorem unexpectedEdgeArgumentRejected :
    ¬ heroAccessWithUnexpectedArg.argumentsWellTyped graphSchema
      { name := "hero", outputType := .named "Character" } := by
  simp [FieldAccess.argumentsWellTyped, Validation.argumentsValid,
    Validation.argumentValid, Schema.lookupArgumentDefinition,
    heroAccessWithUnexpectedArg, heroFormatArg]

set_option linter.unusedSimpArgs false in
theorem duplicateSemanticPathRejected :
    ¬ duplicateSemanticPathStore.nodePathsUnique := by
  simp [duplicateSemanticPathStore, Store.nodePathsUnique, Store.allNodes,
    pairwiseUniqueByEqBool, ObjectPath.eqBool, PathStep.eqBool,
    FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.argumentEqBool,
    FieldAccess.canonicalInputValue, FieldAccess.structuralInputValueEqBool,
    FieldAccess.structuralInputValuesEqBool, FieldAccess.canonicalArguments,
    FieldAccess.canonicalArgument, FieldAccess.sortArgumentsByName,
    FieldAccess.insertArgumentSorted, InputValue.canonical,
    rootNode, heroNodeWithStringArgsA, heroNodeWithStringArgsB,
    rawHeroPathWithStringArgsA,
    rawHeroPathWithStringArgsB, heroAccessWithStringArgsA,
    heroAccessWithStringArgsB, heroEpisodeStringArg, heroFormatArg,
    nameAccess]

theorem duplicatePropertyRejected :
    ¬ heroNodeWithDuplicateProperties.propertyKeysUnique := by
  simp [ObjectNode.propertyKeysUnique, ObjectNode.propertyKeys,
    pairwiseUniqueByEqBool, FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, heroNodeWithDuplicateProperties, nameAccess]

set_option linter.unusedSimpArgs false in
theorem duplicateListIndexRejected :
    ¬ duplicateListIndexStore.listCompositeEdgesUnique := by
  simp [duplicateListIndexStore, graphStore, Store.listCompositeEdgesUnique,
    Store.listCompositeEdgeKeys, ObjectEdge.listIndexKey?,
    pairwiseUniqueByEqBool, ListIndexKey.eqBool, ObjectPath.eqBool,
    PathStep.eqBool, FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, FieldAccess.childPath, FieldAccess.canonical,
    firstHeroFriendEdge, heroEdge, heroPath, friendsAccess, heroAccess]

set_option linter.unusedSimpArgs false in
theorem gapListIndexRejected :
    ¬ gapListIndexStore.listCompositeEdgesDense := by
  simp [gapListIndexStore, Store.listCompositeEdgesDense,
    Store.indexedMatchingEdges, Store.indexedMatchingEdgesUnsorted,
    Store.sortEdgesByIndex, Store.insertEdgeByIndex, Store.matchingEdges,
    ObjectEdge.matchesField, ObjectPath.eqBool, PathStep.eqBool,
    FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, FieldAccess.childPath, FieldAccess.canonical,
    heroEdge, secondHeroFriendEdge, heroPath, heroAccess, friendsAccess]

set_option linter.unusedSimpArgs false in
theorem orphanNodeRejected :
    ¬ orphanNodeStore.nodesCoveredByRootOrEdge := by
  simp [orphanNodeStore, Store.nodesCoveredByRootOrEdge,
    Store.nodeCoveredByRootOrEdge, Store.allNodes, ObjectPath.eqBool,
    PathStep.eqBool, FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, FieldAccess.childPath, FieldAccess.canonical,
    rootNode, heroNode, heroPath, heroAccess]

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

theorem outOfOrderListResolvesByIndex :
    outOfOrderListStore.resolveValue graphSchema "friends" []
      (.object "Character" heroPath) =
        .list [
          .object "Character" firstHeroFriendPath,
          .object "Character" secondHeroFriendPath
        ] := by
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
    Store.nonListCompositeEdgeKeys, ObjectEdge.nonListKey?,
    pairwiseUniqueByEqBool, FieldPathKey.eqBool, ObjectPath.eqBool,
    FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, FieldAccess.childPath, FieldAccess.canonical,
    heroEdge, firstHeroFriendEdge, heroPath, heroAccess, friendsAccess]

end DataModel
end Tests
end GraphQL
