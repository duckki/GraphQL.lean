import GraphQL.SchemaWellFormedness.FieldLookup

/-!
Possible-type and object implementation facts derived from schema well-formedness.
-/
namespace GraphQL

namespace SchemaWellFormedness

theorem schemaWellFormed_possibleTypesAreObjects {schema : Schema} :
    schemaWellFormed schema ->
      ∀ typeName objectTypeName,
        objectTypeName ∈ schema.getPossibleTypes typeName ->
          schema.objectType objectTypeName := by
  intro hschema
  exact hschema.2.2.2.1

theorem schemaWellFormed_possibleTypesNodup {schema : Schema} :
    schemaWellFormed schema ->
      ∀ typeName, (schema.getPossibleTypes typeName).Nodup := by
  intro hschema
  exact hschema.2.2.2.2.1

theorem schemaWellFormed_possibleObjectFieldDefinitionsImplement
    {schema : Schema} :
    schemaWellFormed schema ->
      possibleObjectFieldDefinitionsImplement schema := by
  intro hschema
  exact hschema.2.2.2.2.2

theorem schemaWellFormed_possibleObject_lookupField_implements
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition} :
    schemaWellFormed schema ->
      objectTypeName ∈ schema.getPossibleTypes parentType ->
        schema.lookupField parentType fieldName = some expected ->
          schema.lookupField objectTypeName fieldName = some implementation ->
            fieldDefinitionImplements schema implementation expected := by
  intro hschema hpossible hexpected himplementation
  rcases schemaWellFormed_possibleObjectFieldDefinitionsImplement hschema
      parentType objectTypeName fieldName expected hpossible hexpected with
    ⟨actual, hactual, himplements, _hshape⟩
  rw [hactual] at himplementation
  cases himplementation
  exact himplements

theorem schemaWellFormed_possibleObject_lookupField_sameResponseShape
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition} :
    schemaWellFormed schema ->
      objectTypeName ∈ schema.getPossibleTypes parentType ->
        schema.lookupField parentType fieldName = some expected ->
          schema.lookupField objectTypeName fieldName = some implementation ->
            FieldMerge.sameResponseShape schema
              implementation.outputType expected.outputType := by
  intro hschema hpossible hexpected himplementation
  rcases schemaWellFormed_possibleObjectFieldDefinitionsImplement hschema
      parentType objectTypeName fieldName expected hpossible hexpected with
    ⟨actual, hactual, _himplements, hshape⟩
  rw [hactual] at himplementation
  cases himplementation
  exact hshape

theorem schemaWellFormed_possibleObject_lookupField_exists
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected : FieldDefinition} :
    schemaWellFormed schema ->
      objectTypeName ∈ schema.getPossibleTypes parentType ->
        schema.lookupField parentType fieldName = some expected ->
          ∃ implementation,
            schema.lookupField objectTypeName fieldName = some implementation := by
  intro hschema hpossible hexpected
  rcases schemaWellFormed_possibleObjectFieldDefinitionsImplement hschema
      parentType objectTypeName fieldName expected hpossible hexpected with
    ⟨implementation, himplementation, _himplements, _hshape⟩
  exact ⟨implementation, himplementation⟩

theorem schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition} :
    schemaWellFormed schema ->
      objectTypeName ∈ schema.getPossibleTypes parentType ->
        schema.lookupField parentType fieldName = some expected ->
          schema.lookupField objectTypeName fieldName = some implementation ->
            schema.outputTypeSubtype implementation.outputType
              expected.outputType := by
  intro hschema hpossible hexpected himplementation
  exact (schemaWellFormed_possibleObject_lookupField_implements hschema
    hpossible hexpected himplementation).1

theorem schemaWellFormed_possibleObject_lookupField_argumentsImplement
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition} :
    schemaWellFormed schema ->
      objectTypeName ∈ schema.getPossibleTypes parentType ->
        schema.lookupField parentType fieldName = some expected ->
          schema.lookupField objectTypeName fieldName = some implementation ->
            argumentDefinitionsImplement implementation.arguments
              expected.arguments := by
  intro hschema hpossible hexpected himplementation
  exact (schemaWellFormed_possibleObject_lookupField_implements hschema
    hpossible hexpected himplementation).2

end SchemaWellFormedness

end GraphQL
