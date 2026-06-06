import GraphQL.Validation

/-!
Spec reference: GraphQL September 2025.
- 3.3 Schema and 3.4-3.12 Type System validation: this file separates raw schema syntax
  from schema well-formedness predicates. The spec describes these as validation rules;
  this module names the resulting schema invariants `WellFormed`.
- 3.6-3.10 Object, Interface, Union, Enum, and Input Object validation: modeled partially,
  covering uniqueness, non-empty member/field lists, default-value validity, and
  object/interface field implementation compatibility.
- Fidelity note: several normative rules are omitted, including reserved `__` names,
  interface cycles, input-object cycles/default cycles, directive validation, extensions,
  OneOf, mutation/subscription roots, and introspection.
-/
namespace GraphQL

namespace SchemaWellFormedness

-- Spec 3.6-3.10 type validation repeatedly requires non-empty definition/member lists.
def listNonempty {α : Type} (values : List α) : Prop :=
  values ≠ []

-- Spec type-system uniqueness clauses: faithful as a generic list-level no-duplicates
-- predicate.
def namesAreUnique (names : List Name) : Prop :=
  names.Nodup

-- Spec 3.6.1 / 3.10 input value definition rules: partial; checks `IsInputType` and
-- constant default validity, omitting directive/name rules and full scalar coercion.
def inputValueDefinitionWellFormed (schema : Schema)
    (definition : InputValueDefinition) : Prop :=
  definition.inputType.isInputType schema
    ∧ match definition.defaultValue with
      | none => True
      | some defaultValue => defaultValue.isCorrectType schema definition.inputType

-- Spec 3.6.1 / 3.10 input value definition lists: names are unique and every definition
-- has an input type and valid default when present. Empty field argument lists are valid.
def inputValueDefinitionsWellFormed (schema : Schema)
    (definitions : List InputValueDefinition) : Prop :=
  namesAreUnique (definitions.map InputValueDefinition.name)
    ∧ ∀ definition, definition ∈ definitions ->
      inputValueDefinitionWellFormed schema definition

-- Spec 3.6 field definition rules: partial; checks output type and argument definitions,
-- omitting reserved names, descriptions, directives, and deprecation-specific rules.
def fieldDefinitionWellFormed (schema : Schema) (field : FieldDefinition) : Prop :=
  field.outputType.isOutputType schema
    ∧ inputValueDefinitionsWellFormed schema field.arguments

-- Spec 3.6 / 3.7 output field lists must be non-empty, uniquely named, and individually
-- well-formed. Field argument lists themselves may be empty.
def fieldDefinitionsWellFormed (schema : Schema) (fields : List FieldDefinition) : Prop :=
  listNonempty fields
    ∧ namesAreUnique (fields.map FieldDefinition.name)
    ∧ ∀ field, field ∈ fields -> fieldDefinitionWellFormed schema field

theorem fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
    {schema : Schema} {fields : List FieldDefinition}
    {fieldName : Name} {fieldDefinition : FieldDefinition} :
    fieldDefinitionsWellFormed schema fields ->
      Schema.lookupFieldDefinition fields fieldName = some fieldDefinition ->
        fieldDefinitionWellFormed schema fieldDefinition := by
  intro hfields hlookup
  have hmem : fieldDefinition ∈ fields := by
    simpa [Schema.lookupFieldDefinition] using
      List.mem_of_find?_eq_some hlookup
  exact hfields.2.2 fieldDefinition hmem

theorem fieldDefinitionsWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {fields : List FieldDefinition}
    {fieldName : Name} {fieldDefinition : FieldDefinition} :
    fieldDefinitionsWellFormed schema fields ->
      Schema.lookupFieldDefinition fields fieldName = some fieldDefinition ->
        fieldDefinition.outputType.isOutputType schema := by
  intro hfields hlookup
  exact
    (fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
      hfields hlookup).1

-- Spec 3.6 / 3.7 field implementation argument rules: inherited arguments must exist
-- with the same input type; additional implementation arguments must not be required.
def argumentDefinitionsImplement
    (implementation expected : List InputValueDefinition) : Prop :=
  (∀ expectedDefinition, expectedDefinition ∈ expected ->
    ∃ implementationDefinition,
      Schema.lookupArgumentDefinition implementation expectedDefinition.name =
        some implementationDefinition
        ∧ implementationDefinition.inputType = expectedDefinition.inputType)
    ∧ (∀ implementationDefinition, implementationDefinition ∈ implementation ->
      Schema.lookupArgumentDefinition expected implementationDefinition.name = none ->
        ¬ implementationDefinition.isRequired)

-- Spec 3.6 / 3.7 field implementation rules: return type is covariant and arguments
-- are compatible.
def fieldDefinitionImplements (schema : Schema)
    (implementation expected : FieldDefinition) : Prop :=
  schema.outputTypeSubtype implementation.outputType expected.outputType
    ∧ argumentDefinitionsImplement implementation.arguments expected.arguments

-- Spec 3.6 / 3.7 object/interface implementation rules: every interface field must be
-- implemented by name with compatible type and arguments.
def fieldsImplementInterface (schema : Schema)
    (implementationFields : List FieldDefinition) (interfaceName : Name) : Prop :=
  ∃ interfaceType,
    schema.lookupInterface interfaceName = some interfaceType
      ∧ ∀ interfaceField, interfaceField ∈ interfaceType.fields ->
        ∃ implementationField,
          Schema.lookupFieldDefinition implementationFields interfaceField.name =
            some implementationField
            ∧ fieldDefinitionImplements schema implementationField interfaceField

-- Spec 3.6 object type rules: checks non-empty fields, declared interface existence,
-- and interface field implementation compatibility.
def objectTypeWellFormed (schema : Schema) (objectType : ObjectType) : Prop :=
  fieldDefinitionsWellFormed schema objectType.fields
    ∧ namesAreUnique objectType.interfaces
    ∧ ∀ interfaceName, interfaceName ∈ objectType.interfaces ->
      fieldsImplementInterface schema objectType.fields interfaceName

theorem objectTypeWellFormed_lookupFieldDefinition_wellFormed
    {schema : Schema} {objectType : ObjectType}
    {fieldName : Name} {fieldDefinition : FieldDefinition} :
    objectTypeWellFormed schema objectType ->
      Schema.lookupFieldDefinition objectType.fields fieldName =
        some fieldDefinition ->
        fieldDefinitionWellFormed schema fieldDefinition := by
  intro hobject hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
    hobject.1 hlookup

theorem objectTypeWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {objectType : ObjectType}
    {fieldName : Name} {fieldDefinition : FieldDefinition} :
    objectTypeWellFormed schema objectType ->
      Schema.lookupFieldDefinition objectType.fields fieldName =
        some fieldDefinition ->
        fieldDefinition.outputType.isOutputType schema := by
  intro hobject hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_outputType
    hobject.1 hlookup

-- Spec 3.7 interface type rules: checks non-empty fields, declared interface existence,
-- and interface field implementation compatibility, but not cycles.
def interfaceTypeWellFormed (schema : Schema) (interfaceType : InterfaceType) : Prop :=
  fieldDefinitionsWellFormed schema interfaceType.fields
    ∧ namesAreUnique interfaceType.interfaces
    ∧ ∀ implementedInterfaceName,
      implementedInterfaceName ∈ interfaceType.interfaces ->
        fieldsImplementInterface schema interfaceType.fields implementedInterfaceName

theorem interfaceTypeWellFormed_lookupFieldDefinition_wellFormed
    {schema : Schema} {interfaceType : InterfaceType}
    {fieldName : Name} {fieldDefinition : FieldDefinition} :
    interfaceTypeWellFormed schema interfaceType ->
      Schema.lookupFieldDefinition interfaceType.fields fieldName =
        some fieldDefinition ->
        fieldDefinitionWellFormed schema fieldDefinition := by
  intro hinterface hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
    hinterface.1 hlookup

theorem interfaceTypeWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {interfaceType : InterfaceType}
    {fieldName : Name} {fieldDefinition : FieldDefinition} :
    interfaceTypeWellFormed schema interfaceType ->
      Schema.lookupFieldDefinition interfaceType.fields fieldName =
        some fieldDefinition ->
        fieldDefinition.outputType.isOutputType schema := by
  intro hinterface hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_outputType
    hinterface.1 hlookup

-- Spec 3.8 union type rules: checks non-empty unique object members; directives and
-- extensions are out of scope.
def unionTypeWellFormed (schema : Schema) (unionType : UnionType) : Prop :=
  listNonempty unionType.members
    ∧ namesAreUnique unionType.members
    ∧ ∀ objectName, objectName ∈ unionType.members -> schema.objectType objectName

-- Spec 3.9 enum type rules: checks non-empty unique values but omits reserved names,
-- directives, and deprecation rules.
def enumTypeWellFormed (enumType : EnumType) : Prop :=
  listNonempty enumType.values
    ∧ namesAreUnique enumType.values

-- Spec 3.10 input object type rules: checks non-empty input field definitions but omits
-- input-object cycles, default-value cycles, and OneOf rules.
def inputObjectTypeWellFormed (schema : Schema) (inputObjectType : InputObjectType) : Prop :=
  listNonempty inputObjectType.inputFields
    ∧ inputValueDefinitionsWellFormed schema inputObjectType.inputFields

-- Spec 3.4-3.10 type well-formedness dispatcher: partial in the same ways as the
-- per-type predicates.
def typeDefinitionWellFormed (schema : Schema) : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .object objectType => objectTypeWellFormed schema objectType
  | .interface interfaceType => interfaceTypeWellFormed schema interfaceType
  | .union unionType => unionTypeWellFormed schema unionType
  | .enum enumType => enumTypeWellFormed enumType
  | .inputObject inputObjectType => inputObjectTypeWellFormed schema inputObjectType

theorem typeDefinitionWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {typeDefinition : TypeDefinition}
    {fields : List FieldDefinition} {fieldName : Name}
    {fieldDefinition : FieldDefinition} :
    typeDefinitionWellFormed schema typeDefinition ->
      typeDefinition.fields? = some fields ->
        Schema.lookupFieldDefinition fields fieldName = some fieldDefinition ->
          fieldDefinition.outputType.isOutputType schema := by
  intro htype hfields hlookup
  cases typeDefinition with
  | object objectType =>
      simp [TypeDefinition.fields?] at hfields
      subst fields
      exact objectTypeWellFormed_lookupFieldDefinition_outputType
        htype hlookup
  | interface interfaceType =>
      simp [TypeDefinition.fields?] at hfields
      subst fields
      exact interfaceTypeWellFormed_lookupFieldDefinition_outputType
        htype hlookup
  | builtinScalar scalar =>
      simp [TypeDefinition.fields?] at hfields
  | customScalar scalar =>
      simp [TypeDefinition.fields?] at hfields
  | union unionType =>
      simp [TypeDefinition.fields?] at hfields
  | enum enumType =>
      simp [TypeDefinition.fields?] at hfields
  | inputObject inputObjectType =>
      simp [TypeDefinition.fields?] at hfields

-- Proof-facing schema invariant: possible runtime object fields are compatible with
-- fields selected through their static parent type. This is the field-level bridge
-- needed when execution grounds abstract parents to concrete object sources.
def possibleObjectFieldDefinitionsImplement (schema : Schema) : Prop :=
  ∀ parentType objectTypeName fieldName expected,
    objectTypeName ∈ schema.getPossibleTypes parentType ->
      schema.lookupField parentType fieldName = some expected ->
        ∃ implementation,
          schema.lookupField objectTypeName fieldName = some implementation
            ∧ fieldDefinitionImplements schema implementation expected
            ∧ FieldMerge.sameResponseShape schema
              implementation.outputType expected.outputType

-- Spec 3.3 schema rules: partial; checks unique type names and a query object root,
-- omitting operation-type uniqueness/existence for mutation/subscription and directive
-- validation.
def schemaWellFormed (schema : Schema) : Prop :=
  namesAreUnique (schema.allTypes.map TypeDefinition.name)
    ∧ schema.objectType schema.queryType
    ∧ (∀ typeDefinition, typeDefinition ∈ schema.types ->
      typeDefinitionWellFormed schema typeDefinition)
    ∧ (∀ typeName objectTypeName,
      objectTypeName ∈ schema.getPossibleTypes typeName ->
        schema.objectType objectTypeName)
    ∧ (∀ typeName, (schema.getPossibleTypes typeName).Nodup)
    ∧ possibleObjectFieldDefinitionsImplement schema

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

theorem schemaWellFormed_lookupType_typeDefinitionWellFormed
    {schema : Schema} {typeName : Name} {typeDefinition : TypeDefinition} :
    schemaWellFormed schema ->
      schema.lookupType typeName = some typeDefinition ->
        typeDefinitionWellFormed schema typeDefinition := by
  intro hschema hlookup
  have hmemAll : typeDefinition ∈ schema.allTypes := by
    simpa [Schema.lookupType] using List.mem_of_find?_eq_some hlookup
  rcases List.mem_append.mp (by simpa [Schema.allTypes] using hmemAll) with
    hbuiltin | hschemaType
  · simp [Schema.builtinScalarDefinitions] at hbuiltin
    rcases hbuiltin with htype | htype | htype | htype | htype
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
  · exact hschema.2.2.1 typeDefinition hschemaType

theorem schemaWellFormed_lookupField_outputType
    {schema : Schema} {parentType fieldName : Name}
    {fieldDefinition : FieldDefinition} :
    schemaWellFormed schema ->
      schema.lookupField parentType fieldName = some fieldDefinition ->
        fieldDefinition.outputType.isOutputType schema := by
  intro hschema hlookup
  cases htype : schema.lookupType parentType with
  | none =>
      simp [Schema.lookupField, htype] at hlookup
  | some typeDefinition =>
      have htypeWell :
          typeDefinitionWellFormed schema typeDefinition :=
        schemaWellFormed_lookupType_typeDefinitionWellFormed hschema htype
      cases hfields : typeDefinition.fields? with
      | none =>
          simp [Schema.lookupField, htype, hfields] at hlookup
      | some fields =>
          have hfield :
              Schema.lookupFieldDefinition fields fieldName =
                some fieldDefinition := by
            simpa [Schema.lookupField, htype, hfields,
              Schema.lookupFieldDefinition] using hlookup
          exact typeDefinitionWellFormed_lookupFieldDefinition_outputType
            htypeWell hfields hfield

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

-- Spec-conformance pattern, not a GraphQL spec definition: bundles a schema with this
-- file's partial well-formedness proof.
structure WellFormedSchema where
  schema : Schema
  wellFormed : schemaWellFormed schema

end SchemaWellFormedness

end GraphQL
