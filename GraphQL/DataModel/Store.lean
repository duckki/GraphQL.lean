import GraphQL.DataModel

/-!
Spec reference: GraphQL September 2025.
- 6.4.2 `ResolveFieldValue` and the proof-facing data model: store-backed resolver
  facts connect resolved values to schema field output types.
- Fidelity note: these lemmas stay inside the existing data-model assumption that result
  values are already type-conformant.
-/
namespace GraphQL

namespace DataModel

namespace ObjectRecord

theorem lookupFieldIn?_some_conformsToLookupField (schema : Schema)
    (object : ObjectRecord) :
    ∀ (fields : List (FieldKey × Value)) (fieldName : Name)
      (arguments : List Argument) (value : Value),
      (∀ fieldFact, fieldFact ∈ fields ->
        fieldFactWellTyped schema object fieldFact.fst fieldFact.snd) ->
        lookupFieldIn? fieldName arguments fields = some value ->
          ∃ fieldDefinition,
            schema.lookupField object.typeName fieldName = some fieldDefinition
              ∧ Value.conformsToType schema value fieldDefinition.outputType := by
  intro fields
  induction fields with
  | nil =>
      intro fieldName arguments value _hwell hlookup
      simp [lookupFieldIn?] at hlookup
  | cons fieldFact rest ih =>
      intro fieldName arguments value hwell hlookup
      cases fieldFact with
      | mk key fieldValue =>
          by_cases hmatch :
              key.name == fieldName
                && ResponseShape.SelectedField.argumentsEqBool key.arguments arguments
          · have hlookupHead : fieldValue = value := by
              simpa [lookupFieldIn?, hmatch] using hlookup
            subst value
            have hkeyName : key.name = fieldName := by
              have hmatchParts := hmatch
              simp at hmatchParts
              exact hmatchParts.left
            have hfact :
                fieldFactWellTyped schema object key fieldValue :=
              hwell (key, fieldValue) (by simp)
            rcases hfact with ⟨fieldDefinition, hfield, hvalue⟩
            refine ⟨fieldDefinition, ?_, hvalue⟩
            simpa [hkeyName] using hfield
          · have hlookupRest :
                lookupFieldIn? fieldName arguments rest = some value := by
              simpa [lookupFieldIn?, hmatch] using hlookup
            have hrestWell :
                ∀ fieldFact, fieldFact ∈ rest ->
                  fieldFactWellTyped schema object fieldFact.fst fieldFact.snd := by
              intro fieldFact hmem
              exact hwell fieldFact (by simp [hmem])
            exact ih fieldName arguments value hrestWell hlookupRest

theorem lookupField?_some_conformsToLookupField (schema : Schema)
    (object : ObjectRecord) (fieldName : Name) (arguments : List Argument)
    (value : Value) :
    object.wellTyped schema ->
      object.lookupField? fieldName arguments = some value ->
        ∃ fieldDefinition,
          schema.lookupField object.typeName fieldName = some fieldDefinition
            ∧ Value.conformsToType schema value fieldDefinition.outputType := by
  intro hobject hlookup
  exact lookupFieldIn?_some_conformsToLookupField schema object object.fields
    fieldName arguments value hobject.right hlookup

end ObjectRecord

namespace Store

theorem lookupObject?_some_mem (store : Store) {typeName : Name}
    {id : ObjectId} {object : ObjectRecord} :
    store.lookupObject? typeName id = some object ->
      object ∈ store.objects := by
  intro hlookup
  simpa [lookupObject?] using List.mem_of_find?_eq_some hlookup

theorem lookupObject?_some_typeName (store : Store) {typeName : Name}
    {id : ObjectId} {object : ObjectRecord} :
    store.lookupObject? typeName id = some object ->
      object.typeName = typeName := by
  intro hlookup
  have hmatch := List.find?_some hlookup
  simp at hmatch
  exact hmatch.left

theorem resolveValue_conformsToLookupField (schema : Schema) (store : Store)
    (runtimeType : Name) (id : ObjectId) (fieldName : Name)
    (arguments : List Argument) (fieldDefinition : FieldDefinition) :
    store.wellTyped schema ->
      schema.lookupField runtimeType fieldName = some fieldDefinition ->
        store.resolveValue fieldName arguments (.object runtimeType id) = .null
          ∨ Value.conformsToType schema
            (store.resolveValue fieldName arguments (.object runtimeType id))
            fieldDefinition.outputType := by
  intro hstore hfieldDefinition
  cases hobject : store.lookupObject? runtimeType id with
  | none =>
      simp [resolveValue, hobject]
  | some object =>
      have hobjectMem : object ∈ store.objects :=
        lookupObject?_some_mem store hobject
      have hobjectType : object.typeName = runtimeType :=
        lookupObject?_some_typeName store hobject
      have hobjectWell : object.wellTyped schema := hstore object hobjectMem
      cases hfield : object.lookupField? fieldName arguments with
      | none =>
          simp [resolveValue, hobject, hfield]
      | some value =>
          right
          have hvalue :=
            ObjectRecord.lookupField?_some_conformsToLookupField schema object
              fieldName arguments value hobjectWell hfield
          rcases hvalue with ⟨storedFieldDefinition, hstoredField, hconforms⟩
          have hstoredField' :
              schema.lookupField runtimeType fieldName = some storedFieldDefinition := by
            simpa [hobjectType] using hstoredField
          have hdefinitionEq : storedFieldDefinition = fieldDefinition := by
            symm
            simpa [hfieldDefinition] using hstoredField'
          simpa [resolveValue, hobject, hfield, hdefinitionEq] using hconforms

end Store

theorem possibleTypes_eq_nil_of_isLeafType (schema : Schema) {typeName : Name} :
    schema.isLeafType typeName ->
      schema.getPossibleTypes typeName = [] := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, hleafType⟩
  cases typeDefinition <;>
    simp [Schema.getPossibleTypes, hlookup, TypeDefinition.getPossibleTypes,
      TypeDefinition.isLeafType] at hleafType ⊢

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
    (runtimeType : Name) (id : ObjectId) (parentType : Name) :
    ∀ (typeRef : TypeRef),
      typeRef.namedType = parentType ->
        Value.conformsToType schema (.object runtimeType id) typeRef ->
          schema.typeIncludesObject parentType runtimeType
  | .named typeName, hnamed, hconforms => by
      simpa [← hnamed] using hconforms
  | .list _inner, _hnamed, hconforms => by
      cases hconforms
  | .nonNull inner, hnamed, hconforms => by
      exact object_conformsToType_typeIncludesObject schema runtimeType id
        parentType inner hnamed hconforms

namespace Store

theorem resolveValue_ne_scalar_of_compositeLookupField (schema : Schema)
    (store : Store) (runtimeType : Name) (id : ObjectId) (fieldName : Name)
    (arguments : List Argument) (fieldDefinition : FieldDefinition) (value : String) :
    store.wellTyped schema ->
      schema.lookupField runtimeType fieldName = some fieldDefinition ->
        ¬ schema.getPossibleTypes fieldDefinition.outputType.namedType = [] ->
          store.resolveValue fieldName arguments (.object runtimeType id) ≠ .scalar value := by
  intro hstore hfieldDefinition hnonempty hscalar
  have hresolved :=
    resolveValue_conformsToLookupField schema store runtimeType id fieldName
      arguments fieldDefinition hstore hfieldDefinition
  cases hresolved with
  | inl hnull =>
      rw [hscalar] at hnull
      cases hnull
  | inr hconforms =>
      rw [hscalar] at hconforms
      exact scalar_not_conformsToType_of_possibleTypes_nonempty schema value
        fieldDefinition.outputType hnonempty hconforms

end Store

end DataModel

end GraphQL
