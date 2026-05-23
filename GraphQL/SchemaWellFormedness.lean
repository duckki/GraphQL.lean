import GraphQL.Schema

/-!
Spec reference: GraphQL September 2025.
- 3.3 Schema and 3.4-3.12 Type System validation: this file separates raw schema syntax
  from well-formedness predicates.
- 3.6-3.10 Object, Interface, Union, Enum, and Input Object validation: modeled partially,
  mostly for uniqueness and type-reference validity.
- Fidelity note: several normative rules are omitted, including reserved `__` names,
  non-empty object/interface/input-field lists, interface field/type covariance, interface
  cycles, input-object cycles/default cycles, directive validation, extensions, OneOf,
  mutation/subscription roots, and introspection.
-/
namespace GraphQL

namespace SchemaWellFormedness

-- Spec type-system validation uniqueness clauses: faithful as a generic list-level
-- no-duplicates predicate.
def namesNodup (names : List Name) : Prop :=
  names.Nodup

-- Spec 3.6.1 / 3.10 input value definition validation: partial; checks only
-- `IsInputType`, omitting default-value coercion and directive/name rules.
def inputValueDefinitionWellFormed (schema : Schema)
    (definition : InputValueDefinition) : Prop :=
  definition.inputType.validInput schema

def inputValueDefinitionsWellFormed (schema : Schema)
    (definitions : List InputValueDefinition) : Prop :=
  namesNodup (definitions.map InputValueDefinition.name)
    ∧ ∀ definition, definition ∈ definitions ->
      inputValueDefinitionWellFormed schema definition

-- Spec 3.6 Field validation: partial; checks output type and argument definitions,
-- omitting reserved names, descriptions, directives, and deprecation-specific rules.
def fieldDefinitionWellFormed (schema : Schema) (field : FieldDefinition) : Prop :=
  field.outputType.validOutput schema
    ∧ inputValueDefinitionsWellFormed schema field.arguments

def fieldDefinitionsWellFormed (schema : Schema) (fields : List FieldDefinition) : Prop :=
  namesNodup (fields.map FieldDefinition.name)
    ∧ ∀ field, field ∈ fields -> fieldDefinitionWellFormed schema field

-- Spec 3.6 Object type validation: partial; validates fields and inverse interface
-- membership but not interface field implementation compatibility or non-empty fields.
def objectTypeWellFormed (schema : Schema) (objectType : ObjectType) : Prop :=
  fieldDefinitionsWellFormed schema objectType.fields
    ∧ namesNodup objectType.interfaces
    ∧ ∀ interfaceName, interfaceName ∈ objectType.interfaces ->
      ∃ interfaceType,
        schema.lookupInterface interfaceName = some interfaceType
          ∧ objectType.name ∈ interfaceType.implementations

-- Spec 3.7 Interface type validation: partial; this model stores implementors, so it
-- checks inverse object membership rather than the spec's interface-implements-interface
-- rules.
def interfaceTypeWellFormed (schema : Schema) (interfaceType : InterfaceType) : Prop :=
  fieldDefinitionsWellFormed schema interfaceType.fields
    ∧ namesNodup interfaceType.implementations
    ∧ ∀ objectName, objectName ∈ interfaceType.implementations ->
      ∃ objectType,
        schema.lookupObject objectName = some objectType
          ∧ interfaceType.name ∈ objectType.interfaces

-- Spec 3.8 Union type validation: partial; validates unique object members but does not
-- enforce non-empty member lists or directives/extensions.
def unionTypeWellFormed (schema : Schema) (unionType : UnionType) : Prop :=
  namesNodup unionType.members
    ∧ ∀ objectName, objectName ∈ unionType.members -> schema.objectType objectName

-- Spec 3.9 Enum type validation: partial; validates unique values but omits non-empty
-- values, reserved names, directives, and deprecation rules.
def enumTypeWellFormed (enumType : EnumType) : Prop :=
  namesNodup enumType.values

-- Spec 3.10 Input Object type validation: partial; validates input field definitions but
-- omits non-empty fields, input-object cycles, default-value cycles, and OneOf rules.
def inputObjectTypeWellFormed (schema : Schema) (inputObjectType : InputObjectType) : Prop :=
  inputValueDefinitionsWellFormed schema inputObjectType.inputFields

-- Spec 3.4-3.10 type validation dispatcher: partial in the same ways as the per-type
-- predicates.
def typeDefinitionWellFormed (schema : Schema) : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .object objectType => objectTypeWellFormed schema objectType
  | .interface interfaceType => interfaceTypeWellFormed schema interfaceType
  | .union unionType => unionTypeWellFormed schema unionType
  | .enum enumType => enumTypeWellFormed enumType
  | .inputObject inputObjectType => inputObjectTypeWellFormed schema inputObjectType

-- Spec 3.3 Schema validation: partial; checks unique type names and a query object root,
-- omitting operation-type uniqueness/existence for mutation/subscription and directive
-- validation.
def schemaWellFormed (schema : Schema) : Prop :=
  namesNodup (schema.allTypes.map TypeDefinition.name)
    ∧ schema.objectType schema.queryType
    ∧ ∀ typeDefinition, typeDefinition ∈ schema.types ->
      typeDefinitionWellFormed schema typeDefinition

-- Spec-conformance pattern, not a GraphQL spec definition: bundles a schema with this
-- file's partial well-formedness proof.
structure WellFormedSchema where
  schema : Schema
  wellFormed : schemaWellFormed schema

end SchemaWellFormedness

end GraphQL
