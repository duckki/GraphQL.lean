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
            rcases hfact with ⟨fieldDefinition, hfield, hleaf, hconforms⟩
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
    node.properties field value hnode.right hlookup

end ObjectNode

namespace Store

theorem lookupNodeIn?_some_mem {path : ObjectPath} {node : ObjectNode} :
    ∀ nodes,
      lookupNodeIn? path nodes = some node ->
        node ∈ nodes
  | [], hlookup => by
      simp [lookupNodeIn?] at hlookup
  | candidate :: rest, hlookup => by
      by_cases hmatch : ObjectPath.eqBool candidate.path path = true
      · have hnode : candidate = node := by
          simpa [lookupNodeIn?, hmatch] using hlookup
        subst node
        simp
      · have hmatchFalse : ObjectPath.eqBool candidate.path path = false := by
          cases h : ObjectPath.eqBool candidate.path path
          · rfl
          · contradiction
        have hrest : lookupNodeIn? path rest = some node := by
          simpa [lookupNodeIn?, hmatchFalse] using hlookup
        exact List.mem_cons_of_mem candidate (lookupNodeIn?_some_mem rest hrest)

theorem lookupNode?_some_mem (store : Store) {path : ObjectPath}
    {node : ObjectNode} :
    store.lookupNode? path = some node ->
      node ∈ store.allNodes := by
  intro hlookup
  exact lookupNodeIn?_some_mem store.allNodes hlookup

theorem lookupNodeIn?_some_path {path : ObjectPath} {node : ObjectNode} :
    ∀ nodes,
      lookupNodeIn? path nodes = some node ->
        ObjectPath.eqBool node.path path = true
  | [], hlookup => by
      simp [lookupNodeIn?] at hlookup
  | candidate :: rest, hlookup => by
      by_cases hmatch : ObjectPath.eqBool candidate.path path = true
      · have hnode : candidate = node := by
          simpa [lookupNodeIn?, hmatch] using hlookup
        subst node
        exact hmatch
      · have hmatchFalse : ObjectPath.eqBool candidate.path path = false := by
          cases h : ObjectPath.eqBool candidate.path path
          · rfl
          · contradiction
        have hrest : lookupNodeIn? path rest = some node := by
          simpa [lookupNodeIn?, hmatchFalse] using hlookup
        exact lookupNodeIn?_some_path rest hrest

theorem lookupNode?_some_path (store : Store) {path : ObjectPath}
    {node : ObjectNode} :
    store.lookupNode? path = some node ->
      ObjectPath.eqBool node.path path = true := by
  intro hlookup
  exact lookupNodeIn?_some_path store.allNodes hlookup

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
        ¬ Value.conformsToType schema (.scalar value) typeRef
  | .named _typeName, hnonempty, hconforms =>
      hnonempty (possibleTypes_eq_nil_of_isLeafType schema hconforms)
  | .list _inner, _hnonempty, hconforms =>
      hconforms
  | .nonNull inner, hnonempty, hconforms =>
      scalar_not_conformsToType_of_possibleTypes_nonempty schema value
        inner hnonempty hconforms

theorem object_conformsToType_typeIncludesObject (schema : Schema)
    (runtimeType : Name) (identity : ObjectPath) (parentType : Name) :
    ∀ (typeRef : TypeRef),
      typeRef.namedType = parentType ->
        Value.conformsToType schema (.object runtimeType identity) typeRef ->
          schema.typeIncludesObject parentType runtimeType
  | .named typeName, hnamed, hconforms => by
      simpa [← hnamed] using hconforms
  | .list _inner, _hnamed, hconforms => by
      cases hconforms
  | .nonNull inner, hnamed, hconforms => by
      exact object_conformsToType_typeIncludesObject schema runtimeType identity
        parentType inner hnamed hconforms

namespace Store

theorem resolveValue_ne_scalar_of_compositeLookupField (schema : Schema)
    (store : Store) (runtimeType : Name) (identity : ObjectPath)
    (fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) (value : String) :
    store.wellTyped schema ->
      schema.lookupField runtimeType fieldName = some fieldDefinition ->
        ¬ schema.getPossibleTypes fieldDefinition.outputType.namedType = [] ->
          store.resolveValue schema fieldName arguments
            (.object runtimeType identity) ≠ .scalar value := by
  intro _hstore hfieldDefinition hnonempty hscalar
  cases hnode : store.lookupNode? identity with
  | none =>
      simp [resolveValue, hnode] at hscalar
  | some node =>
      by_cases htype : (node.typeName == runtimeType) = true
      · have hpossible :
            ¬ schema.getPossibleTypes fieldDefinition.outputType.namedType = [] :=
          hnonempty
        by_cases hlist : typeRefIsListLike fieldDefinition.outputType = true
        · simp [resolveValue, hnode, htype, hfieldDefinition, hpossible,
            hlist] at hscalar
        · cases hedge :
            store.firstMatchingEdge? identity (fieldAccess fieldName arguments) none with
          | none =>
              simp [resolveValue, hnode, htype, hfieldDefinition, hpossible,
                hlist, hedge] at hscalar
          | some edge =>
              simp [resolveValue, hnode, htype, hfieldDefinition, hpossible,
                hlist, hedge] at hscalar
      · have htypeFalse : (node.typeName == runtimeType) = false := by
          cases h : node.typeName == runtimeType
          · rfl
          · contradiction
        simp [resolveValue, hnode, htypeFalse] at hscalar

end Store

end DataModel

end GraphQL
