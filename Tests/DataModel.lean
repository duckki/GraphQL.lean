import GraphQL

namespace GraphQL
namespace Tests
namespace DataModel

open GraphQL.DataModel

abbrev field (name : Name) (arguments : List Argument := []) : FieldAccess :=
  { name, arguments }

abbrev node (id : ObjectId) (typeName : Name)
    (properties : List (FieldAccess × PropertyValue) := []) : ObjectNode :=
  { id, typeName, properties }

abbrev edge (sourceId : ObjectId) (field : FieldAccess)
    (targetId : ObjectId) (targetType : Name) : ObjectEdge :=
  { sourceId, field, index? := none, targetId, targetType }

abbrev listEdge (sourceId : ObjectId) (field : FieldAccess)
    (index : Nat) (targetId : ObjectId) (targetType : Name) : ObjectEdge :=
  { sourceId, field, index? := some index, targetId, targetType }

syntax "field!" str : term

macro_rules
  | `(field! $name:str) => do
      let term ← `(field $name [])
      pure term.raw

mutual
  def valueEqBool :
      Execution.ResolverValue ObjectRef -> Execution.ResolverValue ObjectRef -> Bool
    | .null, .null => true
    | .scalar left, .scalar right => left == right
    | .object leftType leftRef, .object rightType rightRef =>
        (leftType == rightType) && (leftRef == rightRef)
    | .list left, .list right => valueListEqBool left right
    | _, _ => false

  def valueListEqBool :
      List (Execution.ResolverValue ObjectRef) ->
        List (Execution.ResolverValue ObjectRef) -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        valueEqBool left right && valueListEqBool lefts rights
    | _, _ => false
end

def optionValueEqBool :
    Option (Execution.ResolverValue ObjectRef) ->
      Option (Execution.ResolverValue ObjectRef) -> Bool
  | none, none => true
  | some left, some right => valueEqBool left right
  | _, _ => false

mutual
  def responseEqBool :
      Execution.ResponseValue -> Execution.ResponseValue -> Bool
    | .null, .null => true
    | .scalar left, .scalar right => left == right
    | .object left, .object right => responseFieldsEqBool left right
    | .list left, .list right => responseListEqBool left right
    | _, _ => false

  def responseListEqBool :
      List Execution.ResponseValue -> List Execution.ResponseValue -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        responseEqBool left right && responseListEqBool lefts rights
    | _, _ => false

  def responseFieldsEqBool :
      List (Name × Execution.ResponseValue) ->
        List (Name × Execution.ResponseValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        (leftName == rightName)
          && responseEqBool leftValue rightValue
          && responseFieldsEqBool lefts rights
    | _, _ => false
end

def heroAccess : FieldAccess :=
  field! "hero"

def villainAccess : FieldAccess :=
  field! "villain"

def friendsAccess : FieldAccess :=
  field! "friends"

def nameAccess : FieldAccess :=
  field! "name"

def heroEpisodeArg : Argument :=
  { name := "episode", value := .enum "JEDI" }

def heroFormatArg : Argument :=
  { name := "format", value := .string "compact" }

def heroAccessWithArgsA : FieldAccess :=
  field "hero" [heroEpisodeArg, heroFormatArg]

def heroAccessWithArgsB : FieldAccess :=
  field "hero" [heroFormatArg, heroEpisodeArg]

def nameAccessWithUnexpectedArg : FieldAccess :=
  field "name" [heroFormatArg]

def heroAccessWithUnexpectedArg : FieldAccess :=
  field "hero" [heroFormatArg]

def searchFilterArgA : Argument :=
  { name := "filter", value := .object [("b", .int 2), ("a", .int 1)] }

def searchFilterArgB : Argument :=
  { name := "filter", value := .object [("a", .int 1), ("b", .int 2)] }

def searchAccessWithArgsA : FieldAccess :=
  field "search" [searchFilterArgA]

def searchAccessWithArgsB : FieldAccess :=
  field "search" [searchFilterArgB]

def queryType : ObjectType :=
  { name := "Query",
    fields := [
      { name := "hero", outputType := .named "Character" },
      { name := "villain", outputType := .named "Character" }
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
  node 0 "Query"

def mismatchedRootNode : ObjectNode :=
  node 0 "Character"

def heroNode : ObjectNode :=
  node 1 "Character" [(nameAccess, .scalar "R2-D2")]

def villainNode : ObjectNode :=
  node 2 "Character" [(nameAccess, .scalar "Darth Vader")]

def heroNodeWithUnexpectedPropertyArg : ObjectNode :=
  { heroNode with properties := [(nameAccessWithUnexpectedArg, .scalar "R2-D2")] }

def heroNodeWithDuplicateProperties : ObjectNode :=
  { heroNode with
    properties := [
      (nameAccess, .scalar "R2-D2"),
      (nameAccess, .scalar "Artoo")
    ] }

def firstHeroFriendNode : ObjectNode :=
  node 3 "Character" [(nameAccess, .scalar "C-3PO")]

def secondHeroFriendNode : ObjectNode :=
  node 4 "Character" [(nameAccess, .scalar "Luke")]

def heroEdge : ObjectEdge :=
  edge 0 heroAccess 1 "Character"

def villainEdge : ObjectEdge :=
  edge 0 villainAccess 2 "Character"

def heroEdgeWithUnexpectedArg : ObjectEdge :=
  edge 0 heroAccessWithUnexpectedArg 1 "Character"

def firstHeroFriendEdge : ObjectEdge :=
  listEdge 1 friendsAccess 0 3 "Character"

def secondHeroFriendEdge : ObjectEdge :=
  listEdge 1 friendsAccess 1 4 "Character"

def graphStore : Store :=
  { root := rootNode,
    nodes := [heroNode, firstHeroFriendNode],
    edges := [heroEdge, firstHeroFriendEdge] }

def duplicateHeroEdgeStore : Store :=
  { graphStore with edges := graphStore.edges ++ [heroEdge] }

def mismatchedRootStore : Store :=
  { root := mismatchedRootNode }

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

def pathSensitiveStore : Store :=
  { root := rootNode,
    nodes := [heroNode, villainNode],
    edges := [heroEdge, villainEdge] }

def pathSensitiveQuery : Operation :=
  { name := some "PathSensitive"
    rootType := "Query"
    selectionSet := [
      .field "hero" "hero" [] [] [
        .field "name" "name" [] [] []
      ],
      .field "villain" "villain" [] [] [
        .field "name" "name" [] [] []
      ]
    ] }

def pathSensitiveExpectedResponse : Execution.ResponseValue :=
  .object [
    ("hero", .object [("name", .scalar "R2-D2")]),
    ("villain", .object [("name", .scalar "Darth Vader")])
  ]

def pathInsensitiveSpecResponse : Execution.ResponseValue :=
  .object [
    ("hero", .object [("name", .scalar "R2-D2")]),
    ("villain", .object [("name", .scalar "R2-D2")])
  ]

def pathSensitiveActualResponse : Execution.ResponseValue :=
  (executeOperationAtDepth graphSchema pathSensitiveStore []
    pathSensitiveQuery 6).data

theorem fieldAccessCanonicalizesArgumentOrder :
    FieldAccess.eqBool heroAccessWithArgsA heroAccessWithArgsB = true := by
  rfl

theorem fieldAccessCanonicalizesInputObjectFieldOrder :
    FieldAccess.eqBool searchAccessWithArgsA searchAccessWithArgsB = true := by
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
    pairwiseUniqueByEqBool, ListIndexKey.eqBool,
    FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, FieldAccess.canonical,
    firstHeroFriendEdge, heroEdge, friendsAccess, heroAccess]

set_option linter.unusedSimpArgs false in
theorem gapListIndexRejected :
    ¬ gapListIndexStore.listCompositeEdgesDense := by
  simp [gapListIndexStore, Store.listCompositeEdgesDense,
    Store.indexedMatchingEdges, Store.indexedMatchingEdgesUnsorted,
    Store.sortEdgesByIndex, Store.insertEdgeByIndex, Store.matchingEdges,
    ObjectEdge.matchesField, FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName, FieldAccess.canonical,
    heroEdge, secondHeroFriendEdge, heroAccess, friendsAccess]

theorem heroFieldResolvesToObject :
    valueEqBool
      (graphStore.resolveValue graphSchema "hero" [] "Query")
      (.object "Character" (objectRefOfId 1)) = true := by
  native_decide

theorem heroNamePropertyResolves :
    valueEqBool
      (graphStore.resolveValue graphSchema "name" [] "Character")
      (.scalar "R2-D2") = true := by
  native_decide

theorem heroFriendsListResolvesByIndex :
    valueEqBool
      (graphStore.resolveValue graphSchema "friends" [] "Character")
      (.list [.object "Character" (objectRefOfId 3)]) = true := by
  native_decide

theorem outOfOrderListResolvesByIndex :
    valueEqBool
      (outOfOrderListStore.resolveValue graphSchema "friends" [] "Character")
      (.list [
        .object "Character" (objectRefOfId 3),
        .object "Character" (objectRefOfId 4)
      ]) = true := by
  native_decide

theorem specExecutionDistinguishesSameTypeObjects :
    responseEqBool pathSensitiveActualResponse pathInsensitiveSpecResponse = false := by
  native_decide

theorem specExecutionMatchesPathSensitiveObjects :
    responseEqBool pathSensitiveActualResponse pathSensitiveExpectedResponse = true := by
  native_decide

theorem resolverBridgeResolvesHero :
    optionValueEqBool
      ((graphStore.resolvers graphSchema).resolve "Query" "hero" []
        (.object "Query" (objectRefOfId 0)))
      (some (Execution.ResolverValue.object "Character" (objectRefOfId 1))) = true := by
  native_decide

theorem resolverBridgeRejectsMismatchedRef :
    optionValueEqBool
      ((pathSensitiveStore.resolvers graphSchema).resolve "Character" "name" []
        (.object "Character" (objectRefOfId 0)))
      none = true := by
  native_decide

theorem resolverBridgeRejectsMissingRef :
    optionValueEqBool
      ((pathSensitiveStore.resolvers graphSchema).resolve "Character" "name" []
        (.object "Character" (objectRefOfId 99)))
      none = true := by
  native_decide

theorem resolverBridgeRejectsMissingRuntimeType :
    optionValueEqBool
      ((graphStore.resolvers graphSchema).resolve "Query" "hero" []
        (.object "MissingType" (objectRefOfId 0)))
      none = true := by
  native_decide

theorem duplicateHeroEdgeRejected :
    ¬ duplicateHeroEdgeStore.nonListCompositeEdgesUnique := by
  simp [duplicateHeroEdgeStore, graphStore, Store.nonListCompositeEdgesUnique,
    Store.nonListCompositeEdgeKeys, ObjectEdge.nonListKey?,
    pairwiseUniqueByEqBool, FieldAccessKey.eqBool,
    FieldAccess.eqBool, FieldAccess.argumentsEqBool,
    FieldAccess.argumentsEqBoolOrdered, FieldAccess.canonicalArguments,
    FieldAccess.sortArgumentsByName,
    heroEdge, firstHeroFriendEdge, heroAccess, friendsAccess]

end DataModel
end Tests
end GraphQL
