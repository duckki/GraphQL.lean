import GraphQL.Validation

/-! Well-formedness of GraphQL schemas
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
def inputValueDefinitionWellFormed (schema : Schema) (definition : InputValueDefinition)
    : Prop :=
  definition.inputType.isInputType schema
  ∧ match definition.defaultValue with
    | none => True
    | some defaultValue => defaultValue.isCorrectType schema definition.inputType

-- Spec 3.6.1 / 3.10 input value definition lists: names are unique and every definition
-- has an input type and valid default when present. Empty field argument lists are valid.
def inputValueDefinitionsWellFormed (schema : Schema)
    (definitions : List InputValueDefinition)
    : Prop :=
  namesAreUnique (definitions.map InputValueDefinition.name)
  ∧ ∀ definition,
      definition ∈ definitions -> inputValueDefinitionWellFormed schema definition

-- Spec 3.6 field definition rules: partial; checks output type and argument definitions,
-- omitting reserved names, descriptions, directives, and deprecation-specific rules.
def fieldDefinitionWellFormed (schema : Schema) (field : FieldDefinition) : Prop :=
  field.outputType.isOutputType schema
  ∧ inputValueDefinitionsWellFormed schema field.arguments

-- Spec 3.6 / 3.7 output field lists must be non-empty, uniquely named, and individually
-- well-formed. Field argument lists themselves may be empty.
def fieldDefinitionsWellFormed (schema : Schema) (fields : List FieldDefinition)
    : Prop :=
  listNonempty fields
  ∧ namesAreUnique (fields.map FieldDefinition.name)
  ∧ ∀ field, field ∈ fields -> fieldDefinitionWellFormed schema field

-- Spec 3.6 / 3.7 field implementation argument rules: inherited arguments must exist
-- with the same input type; additional implementation arguments must not be required.
def argumentDefinitionsImplement (implementation expected : List InputValueDefinition)
    : Prop :=
  (∀ expectedDefinition,
    expectedDefinition ∈ expected
    -> ∃ implementationDefinition,
        Schema.lookupArgumentDefinition implementation expectedDefinition.name
          = some implementationDefinition
        ∧ implementationDefinition.inputType = expectedDefinition.inputType)
  ∧ (∀ implementationDefinition,
      implementationDefinition ∈ implementation
      -> Schema.lookupArgumentDefinition expected implementationDefinition.name = none
      -> ¬ implementationDefinition.isRequired)

-- Spec 3.6 / 3.7 field implementation rules: return type is covariant and arguments
-- are compatible.
def fieldDefinitionImplements (schema : Schema)
    (implementation expected : FieldDefinition)
    : Prop :=
  schema.outputTypeSubtype implementation.outputType expected.outputType
  ∧ argumentDefinitionsImplement implementation.arguments expected.arguments

-- Spec 3.6 / 3.7 object/interface implementation rules: every interface field must be
-- implemented by name with compatible type and arguments.
def fieldsImplementInterface (schema : Schema)
    (implementationFields : List FieldDefinition) (interfaceName : Name)
    : Prop :=
  ∃ interfaceType,
    schema.lookupInterface interfaceName = some interfaceType
    ∧ ∀ interfaceField,
        interfaceField ∈ interfaceType.fields
        -> ∃ implementationField,
            Schema.lookupFieldDefinition implementationFields interfaceField.name
              = some implementationField
            ∧ fieldDefinitionImplements schema implementationField interfaceField

-- Spec 3.6 object type rules: checks non-empty fields, declared interface existence,
-- and interface field implementation compatibility.
def objectTypeWellFormed (schema : Schema) (objectType : ObjectType) : Prop :=
  fieldDefinitionsWellFormed schema objectType.fields
  ∧ namesAreUnique objectType.interfaces
  ∧ ∀ interfaceName,
      interfaceName ∈ objectType.interfaces
      -> fieldsImplementInterface schema objectType.fields interfaceName

-- Spec 3.7 interface type rules: checks non-empty fields, declared interface existence,
-- and interface field implementation compatibility, but not cycles.
def interfaceTypeWellFormed (schema : Schema) (interfaceType : InterfaceType) : Prop :=
  fieldDefinitionsWellFormed schema interfaceType.fields
  ∧ namesAreUnique interfaceType.interfaces
  ∧ ∀ implementedInterfaceName,
      implementedInterfaceName ∈ interfaceType.interfaces
      -> fieldsImplementInterface schema interfaceType.fields implementedInterfaceName

-- Spec 3.8 union type rules: checks non-empty unique object members; directives and
-- extensions are out of scope.
def unionTypeWellFormed (schema : Schema) (unionType : UnionType) : Prop :=
  listNonempty unionType.members
  ∧ namesAreUnique unionType.members
  ∧ ∀ objectName, objectName ∈ unionType.members -> schema.objectType objectName

-- Spec 3.9 enum type rules: checks non-empty unique values but omits reserved names,
-- directives, and deprecation rules.
def enumTypeWellFormed (enumType : EnumType) : Prop :=
  listNonempty enumType.values ∧ namesAreUnique enumType.values

-- Spec 3.10 input object type rules: checks non-empty input field definitions but omits
-- input-object cycles, default-value cycles, and OneOf rules.
def inputObjectTypeWellFormed (schema : Schema) (inputObjectType : InputObjectType)
    : Prop :=
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

-- Proof-facing schema invariant: possible runtime object fields are compatible with
-- fields selected through their static parent type. This is the field-level bridge
-- needed when execution grounds abstract parents to concrete object sources.
def possibleObjectFieldDefinitionsImplement (schema : Schema) : Prop :=
  ∀ parentType objectTypeName fieldName expected,
    objectTypeName ∈ schema.getPossibleTypes parentType
    -> schema.lookupField parentType fieldName = some expected
    -> ∃ implementation,
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
  ∧ (∀ typeDefinition,
      typeDefinition ∈ schema.types -> typeDefinitionWellFormed schema typeDefinition)
  ∧ (∀ typeName objectTypeName,
      objectTypeName ∈ schema.getPossibleTypes typeName
      -> schema.objectType objectTypeName)
  ∧ (∀ typeName, (schema.getPossibleTypes typeName).Nodup)
  ∧ possibleObjectFieldDefinitionsImplement schema

-- Spec-conformance pattern, not a GraphQL spec definition: bundles a schema with this
-- file's partial well-formedness proof.
structure WellFormedSchema where
  schema : Schema
  wellFormed : schemaWellFormed schema

end SchemaWellFormedness

end GraphQL
