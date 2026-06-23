import GraphQL.DataModel

/-!
Spec reference: GraphQL September 2025.
- 6.4.2 `ResolveFieldValue` and the proof-facing graph data model: store-backed resolver
  facts connect resolved values to schema field output types.
- Fidelity note: these lemmas stay inside the existing data-model assumption that result
  values are already type-conformant.
-/
namespace GraphQL

namespace DataModel

theorem lookupType_name_eq (schema : Schema) {typeName : Name}
    {typeDefinition : TypeDefinition} :
    schema.lookupType typeName = some typeDefinition ->
      typeDefinition.name = typeName := by
  intro hlookup
  have hmatch := List.find?_some hlookup
  simpa [Schema.lookupType] using hmatch

theorem typeIncludesObject_eq_of_lookupObjectType (schema : Schema)
    {typeName runtimeType : Name} {objectType : ObjectType} :
    schema.lookupType typeName = some (.object objectType) ->
      schema.typeIncludesObject typeName runtimeType ->
        runtimeType = typeName := by
  intro hlookup hinclude
  have htypeName : objectType.name = typeName :=
    lookupType_name_eq schema hlookup
  simp [Schema.typeIncludesObject, Schema.getPossibleTypes, hlookup, htypeName]
    at hinclude
  exact hinclude

namespace ObjectNode

theorem lookupPropertyIn?_some_conformsToLookupField (schema : Schema)
    (node : ObjectNode) :
    ∀ (properties : List (FieldAccess × PropertyValue))
      (field : FieldAccess) (value : PropertyValue),
      (∀ property, property ∈ properties ->
        propertyFactWellTyped schema node property.fst property.snd) ->
        lookupPropertyIn? field properties = some value ->
          ∃ fieldDefinition,
            schema.lookupField node.typeName field.name = some fieldDefinition
              ∧ schema.getPossibleTypes fieldDefinition.outputType.namedType = []
              ∧ value.conformsToType schema fieldDefinition.outputType := by
  intro properties
  induction properties with
  | nil =>
      intro field value _hwell hlookup
      simp [lookupPropertyIn?] at hlookup
  | cons property rest ih =>
      intro field value hwell hlookup
      cases property with
      | mk key propertyValue =>
          by_cases hmatch : FieldAccess.eqBool key field = true
          · have hlookupHead : propertyValue = value := by
              simpa [lookupPropertyIn?, hmatch] using hlookup
            subst value
            have hfact :
                propertyFactWellTyped schema node key propertyValue :=
              hwell (key, propertyValue) (by simp)
            rcases hfact with ⟨fieldDefinition, hfield, hleaf, _hargs, hconforms⟩
            have hkeyName : key.name = field.name := by
              have hmatchParts := hmatch
              simp [FieldAccess.eqBool] at hmatchParts
              exact hmatchParts.left
            refine ⟨fieldDefinition, ?_, hleaf, hconforms⟩
            simpa [hkeyName] using hfield
          · have hmatchFalse : FieldAccess.eqBool key field = false := by
              cases h : FieldAccess.eqBool key field
              · rfl
              · contradiction
            have hlookupRest :
                lookupPropertyIn? field rest = some value := by
              simpa [lookupPropertyIn?, hmatchFalse] using hlookup
            have hrestWell :
                ∀ property, property ∈ rest ->
                  propertyFactWellTyped schema node property.fst property.snd := by
              intro property hmem
              exact hwell property (by simp [hmem])
            exact ih field value hrestWell hlookupRest

theorem lookupProperty?_some_conformsToLookupField (schema : Schema)
    (node : ObjectNode) (field : FieldAccess) (value : PropertyValue) :
    node.wellTyped schema ->
      node.lookupProperty? field = some value ->
        ∃ fieldDefinition,
          schema.lookupField node.typeName field.name = some fieldDefinition
            ∧ schema.getPossibleTypes fieldDefinition.outputType.namedType = []
            ∧ value.conformsToType schema fieldDefinition.outputType := by
  intro hnode hlookup
  exact lookupPropertyIn?_some_conformsToLookupField schema node
    node.properties field value hnode.right.right hlookup

end ObjectNode

namespace Store

theorem lookupNode?_some_mem (store : Store)
    {id : ObjectId} {node : ObjectNode} :
    store.lookupNode? id = some node ->
      node ∈ store.allNodes := by
  intro hlookup
  exact List.mem_of_find?_eq_some hlookup

theorem lookupNode?_some_id (store : Store)
    {id : ObjectId} {node : ObjectNode} :
    store.lookupNode? id = some node ->
      node.id = id := by
  intro hlookup
  have hpredicate := List.find?_some hlookup
  exact beq_iff_eq.mp hpredicate

private theorem findNodeById?_some_of_mem_unique (node : ObjectNode) :
    ∀ nodes : List ObjectNode,
      pairwiseUniqueByEqBool (fun left right : ObjectId => left == right)
        (nodes.map ObjectNode.id) ->
      node ∈ nodes ->
        nodes.find? (fun candidate => candidate.id == node.id) = some node
  | [], _hunique, hmem => by
      simp at hmem
  | candidate :: rest, hunique, hmem => by
      cases hmem with
      | head =>
          simp
      | tail _ htail =>
        have hnotSame : (candidate.id == node.id) = false := by
          have hnodeIdMem : node.id ∈ rest.map ObjectNode.id :=
            List.mem_map.mpr ⟨node, htail, rfl⟩
          exact hunique.1 node.id hnodeIdMem
        have hrestUnique :
            pairwiseUniqueByEqBool
              (fun left right : ObjectId => left == right)
              (rest.map ObjectNode.id) :=
          hunique.2
        have hfindRest :
            rest.find? (fun candidate => candidate.id == node.id) =
              some node :=
          findNodeById?_some_of_mem_unique node rest hrestUnique htail
        simp [hnotSame, hfindRest]

theorem lookupNode?_some_of_mem_unique (store : Store)
    (node : ObjectNode) :
    store.nodeIdsUnique ->
    node ∈ store.allNodes ->
      store.lookupNode? node.id = some node := by
  intro hunique hmem
  simpa [lookupNode?, nodeIds] using
    findNodeById?_some_of_mem_unique node store.allNodes hunique hmem

theorem firstNodeWithType?_some_mem (store : Store)
    {runtimeType : Name} {node : ObjectNode} :
    store.firstNodeWithType? runtimeType = some node ->
      node ∈ store.allNodes := by
  intro hlookup
  exact List.mem_of_find?_eq_some hlookup

theorem firstNodeWithType?_some_typeName (store : Store)
    {runtimeType : Name} {node : ObjectNode} :
    store.firstNodeWithType? runtimeType = some node ->
      node.typeName = runtimeType := by
  intro hlookup
  have hpredicate := List.find?_some hlookup
  exact beq_iff_eq.mp hpredicate

end Store

theorem possibleTypes_eq_nil_of_isLeafType (schema : Schema) {typeName : Name} :
    schema.isLeafType typeName ->
      schema.getPossibleTypes typeName = [] := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, hleafType⟩
  cases typeDefinition <;>
    simp [Schema.getPossibleTypes, hlookup, TypeDefinition.isLeafType]
      at hleafType ⊢

theorem fieldReturnType?_some_lookupField (schema : Schema)
    {parentType fieldName childType : Name} :
    schema.fieldReturnType? parentType fieldName = some childType ->
      ∃ fieldDefinition,
        schema.lookupField parentType fieldName = some fieldDefinition
          ∧ fieldDefinition.outputType.namedType = childType := by
  intro hreturn
  cases hfield : schema.lookupField parentType fieldName with
  | none =>
      simp [Schema.fieldReturnType?, hfield] at hreturn
  | some fieldDefinition =>
      have hnamed : fieldDefinition.outputType.namedType = childType := by
        simpa [Schema.fieldReturnType?, hfield] using hreturn
      exact ⟨fieldDefinition, rfl, hnamed⟩

theorem scalar_not_conformsToType_of_possibleTypes_nonempty (schema : Schema)
    (value : String) :
    ∀ (typeRef : TypeRef),
      ¬ schema.getPossibleTypes typeRef.namedType = [] ->
        ¬ valueConformsToType schema (.scalar value) typeRef
  | .named _typeName, hnonempty, hconforms =>
      hnonempty (possibleTypes_eq_nil_of_isLeafType schema hconforms)
  | .list _inner, _hnonempty, hconforms =>
      hconforms
  | .nonNull inner, hnonempty, hconforms =>
      scalar_not_conformsToType_of_possibleTypes_nonempty schema value
        inner hnonempty hconforms

theorem object_conformsToType_typeIncludesObject (schema : Schema)
    (runtimeType : Name) (parentType : Name) (ref : ObjectRef) :
    ∀ (typeRef : TypeRef),
      typeRef.namedType = parentType ->
        valueConformsToType schema (.object runtimeType ref) typeRef ->
          schema.typeIncludesObject parentType runtimeType
  | .named typeName, hnamed, hconforms => by
      simpa [← hnamed] using hconforms
  | .list _inner, _hnamed, hconforms => by
      cases hconforms
  | .nonNull inner, hnamed, hconforms => by
      exact object_conformsToType_typeIncludesObject schema runtimeType
        parentType ref inner hnamed hconforms

namespace Store

theorem resolveValue_ne_scalar_of_compositeLookupField (schema : Schema)
    (store : Store) (runtimeType : Name)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) (value : String) :
    store.wellTyped schema ->
      schema.lookupField runtimeType fieldName = some fieldDefinition ->
        ¬ schema.getPossibleTypes fieldDefinition.outputType.namedType = [] ->
          store.resolveValue schema fieldName arguments
            runtimeType ≠ .scalar value := by
  intro _hstore hfieldDefinition hnonempty hscalar
  cases hnode : store.firstNodeWithType? runtimeType with
  | none =>
      simp [resolveValue, hnode] at hscalar
  | some node =>
      have hnodeType : node.typeName = runtimeType :=
        firstNodeWithType?_some_typeName store hnode
      have hfieldDefinitionNode :
          schema.lookupField node.typeName fieldName = some fieldDefinition := by
        simpa [hnodeType] using hfieldDefinition
      have hpossible :
          ¬ schema.getPossibleTypes fieldDefinition.outputType.namedType = [] :=
        hnonempty
      by_cases hlist :
          typeRefIsListLike fieldDefinition.outputType = true
      · simp [resolveValue, hnode, hpossible,
          hfieldDefinitionNode, hlist, resolveValueFromNode] at hscalar
      · cases hedge :
          store.firstMatchingEdge? node.id
            (fieldAccess fieldName arguments) none with
        | none =>
            simp [resolveValue, hnode, hpossible,
              hfieldDefinitionNode, hlist, hedge, resolveValueFromNode] at hscalar
        | some edge =>
            simp [resolveValue, hnode, hpossible,
              hfieldDefinitionNode, hlist, hedge, resolveValueFromNode] at hscalar

end Store

end DataModel

end GraphQL
