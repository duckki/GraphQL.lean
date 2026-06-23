import GraphQL.DataModel.FieldAccess

/-!
Store resolver stability under data-model field access equality.
-/
namespace GraphQL

namespace DataModel

namespace ObjectNode

theorem lookupPropertyIn?_eq_of_field_eqBool :
    ∀ (properties : List (FieldAccess × PropertyValue)) (left right : FieldAccess),
      FieldAccess.eqBool left right = true ->
        lookupPropertyIn? left properties = lookupPropertyIn? right properties
  | [], _left, _right, _h => by
      simp [lookupPropertyIn?]
  | (candidate, _value) :: rest, left, right, h => by
      have hcandidate :
          FieldAccess.eqBool candidate left =
            FieldAccess.eqBool candidate right :=
        FieldAccess.eqBool_congr_right h
      simp [lookupPropertyIn?, hcandidate,
        lookupPropertyIn?_eq_of_field_eqBool rest left right h]

theorem lookupProperty?_eq_of_field_eqBool
    (node : ObjectNode) {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      node.lookupProperty? left = node.lookupProperty? right := by
  intro h
  exact lookupPropertyIn?_eq_of_field_eqBool node.properties left right h

end ObjectNode

namespace ObjectEdge

theorem matchesField_eq_of_field_eqBool
    (edge : ObjectEdge) (sourceId : ObjectId)
    {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      edge.matchesField sourceId left = edge.matchesField sourceId right := by
  intro h
  simp [matchesField, FieldAccess.eqBool_congr_right h]

end ObjectEdge

namespace Store

private theorem filterMatchingEdges_eq_of_field_eqBool
    (sourceId : ObjectId) {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      ∀ (edges : List ObjectEdge),
        edges.filter (fun edge => edge.matchesField sourceId left) =
          edges.filter (fun edge => edge.matchesField sourceId right)
  | h, [] => by
      simp
  | h, edge :: rest => by
      have hmatch :=
        ObjectEdge.matchesField_eq_of_field_eqBool edge sourceId h
      simp [List.filter, hmatch,
        filterMatchingEdges_eq_of_field_eqBool sourceId h rest]

theorem matchingEdges_eq_of_field_eqBool
    (store : Store) (sourceId : ObjectId) {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      store.matchingEdges sourceId left =
        store.matchingEdges sourceId right := by
  intro h
  unfold matchingEdges
  exact filterMatchingEdges_eq_of_field_eqBool sourceId h store.edges

theorem indexedMatchingEdgesUnsorted_eq_of_field_eqBool
    (store : Store) (sourceId : ObjectId) {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      store.indexedMatchingEdgesUnsorted sourceId left =
        store.indexedMatchingEdgesUnsorted sourceId right := by
  intro h
  simp [indexedMatchingEdgesUnsorted,
    matchingEdges_eq_of_field_eqBool store sourceId h]

theorem indexedMatchingEdges_eq_of_field_eqBool
    (store : Store) (sourceId : ObjectId) {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      store.indexedMatchingEdges sourceId left =
        store.indexedMatchingEdges sourceId right := by
  intro h
  simp [indexedMatchingEdges,
    indexedMatchingEdgesUnsorted_eq_of_field_eqBool store sourceId h]

private theorem findMatchingEdge_eq_of_field_eqBool
    (sourceId : ObjectId) (index? : Option Nat) {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      ∀ (edges : List ObjectEdge),
        edges.find? (fun edge =>
            edge.matchesField sourceId left && edge.index? == index?) =
          edges.find? (fun edge =>
            edge.matchesField sourceId right && edge.index? == index?)
  | h, [] => by
      simp
  | h, edge :: rest => by
      have hmatch :=
        ObjectEdge.matchesField_eq_of_field_eqBool edge sourceId h
      simp [List.find?, hmatch,
        findMatchingEdge_eq_of_field_eqBool sourceId index? h rest]

theorem firstMatchingEdge?_eq_of_field_eqBool
    (store : Store) (sourceId : ObjectId) (index? : Option Nat)
    {left right : FieldAccess} :
    FieldAccess.eqBool left right = true ->
      store.firstMatchingEdge? sourceId left index? =
        store.firstMatchingEdge? sourceId right index? := by
  intro h
  unfold firstMatchingEdge?
  exact findMatchingEdge_eq_of_field_eqBool sourceId index? h store.edges

theorem fieldAccess_eqBool_of_argumentsEqBool
    (fieldName : Name) {left right : List Argument} :
    FieldAccess.argumentsEqBool left right = true ->
      FieldAccess.eqBool (fieldAccess fieldName left)
        (fieldAccess fieldName right) = true := by
  intro h
  simp [fieldAccess, FieldAccess.eqBool, h]

theorem resolveValueFromNode_eq_of_argumentsEqBool
    (store : Store) (schema : Schema) (fieldName : Name)
    {left right : List Argument} (sourceNode : ObjectNode) :
    FieldAccess.argumentsEqBool left right = true ->
      store.resolveValueFromNode schema fieldName left sourceNode =
        store.resolveValueFromNode schema fieldName right sourceNode := by
  intro harguments
  have hfield :
      FieldAccess.eqBool (fieldAccess fieldName left)
        (fieldAccess fieldName right) = true :=
    fieldAccess_eqBool_of_argumentsEqBool fieldName harguments
  cases hlookup : schema.lookupField sourceNode.typeName fieldName with
  | none =>
      simp [resolveValueFromNode, hlookup]
  | some fieldDefinition =>
      by_cases hleaf :
          schema.getPossibleTypes fieldDefinition.outputType.namedType = []
      · have hproperty :
          sourceNode.lookupProperty? (fieldAccess fieldName left) =
            sourceNode.lookupProperty? (fieldAccess fieldName right) :=
          ObjectNode.lookupProperty?_eq_of_field_eqBool sourceNode hfield
        simp [resolveValueFromNode, hlookup, hleaf, hproperty]
      · by_cases hlist : typeRefIsListLike fieldDefinition.outputType = true
        · have hindexed :
            store.indexedMatchingEdges sourceNode.id (fieldAccess fieldName left) =
              store.indexedMatchingEdges sourceNode.id
                (fieldAccess fieldName right) :=
            indexedMatchingEdges_eq_of_field_eqBool store sourceNode.id hfield
          simp [resolveValueFromNode, hlookup, hleaf, hlist, hindexed]
        · have hfirst :
            store.firstMatchingEdge? sourceNode.id (fieldAccess fieldName left)
                none =
              store.firstMatchingEdge? sourceNode.id
                (fieldAccess fieldName right) none :=
            firstMatchingEdge?_eq_of_field_eqBool store sourceNode.id none hfield
          simp [resolveValueFromNode, hlookup, hleaf, hlist, hfirst]

theorem resolveValueAtNode_eq_of_argumentsEqBool
    (store : Store) (schema : Schema) (fieldName : Name)
    {left right : List Argument} (sourceId : ObjectId) :
    FieldAccess.argumentsEqBool left right = true ->
      store.resolveValueAtNode schema fieldName left sourceId =
        store.resolveValueAtNode schema fieldName right sourceId := by
  intro harguments
  cases hnode : store.lookupNode? sourceId with
  | none =>
      simp [resolveValueAtNode, hnode]
  | some sourceNode =>
      simp [resolveValueAtNode, hnode,
        resolveValueFromNode_eq_of_argumentsEqBool store schema fieldName
          sourceNode harguments]

theorem resolveValue_eq_of_argumentsEqBool
    (store : Store) (schema : Schema) (fieldName : Name)
    {left right : List Argument} (runtimeType : Name) :
    FieldAccess.argumentsEqBool left right = true ->
      store.resolveValue schema fieldName left runtimeType =
        store.resolveValue schema fieldName right runtimeType := by
  intro harguments
  cases hnode : store.firstNodeWithType? runtimeType with
  | none =>
      simp [resolveValue, hnode]
  | some sourceNode =>
      simp [resolveValue, hnode,
        resolveValueFromNode_eq_of_argumentsEqBool store schema fieldName
          sourceNode harguments]

theorem resolve_eq_of_argumentsEqBool
    (store : Store) (schema : Schema) (fieldName : Name)
    {left right : List Argument} (source : Execution.ResolverValue ObjectRef) :
    FieldAccess.argumentsEqBool left right = true ->
      store.resolve schema fieldName left source =
        store.resolve schema fieldName right source := by
  intro harguments
  cases source with
  | null =>
      simp [resolve]
  | scalar value =>
      simp [resolve]
  | object runtimeType identity =>
      cases hnode : store.lookupNode? (objectIdOfRef identity) with
      | none =>
          simp [resolve, hnode]
      | some sourceNode =>
          by_cases htype : (sourceNode.typeName == runtimeType) = true
          · simp [resolve, hnode, htype,
              resolveValueFromNode_eq_of_argumentsEqBool store schema
                fieldName sourceNode harguments]
          · have htypeFalse :
                (sourceNode.typeName == runtimeType) = false := by
              cases h : sourceNode.typeName == runtimeType
              · rfl
              · contradiction
            simp [resolve, hnode, htypeFalse]
  | list values =>
      simp [resolve]

theorem resolvers_eq_of_argumentsEqBool
    (schema : Schema) (store : Store)
    (leftParentType rightParentType fieldName : Name)
    {left right : List Argument} (source : Execution.ResolverValue ObjectRef) :
    FieldAccess.argumentsEqBool left right = true ->
      (store.resolvers schema).resolve leftParentType fieldName left source =
        (store.resolvers schema).resolve rightParentType fieldName right
          source := by
  intro harguments
  simp [resolvers, resolve_eq_of_argumentsEqBool store schema fieldName
    source harguments]

end Store

end DataModel

end GraphQL
