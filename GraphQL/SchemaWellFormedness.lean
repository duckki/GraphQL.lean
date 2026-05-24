import GraphQL.Schema

/-!
Spec reference: GraphQL September 2025.
- 3.3 Schema and 3.4-3.12 Type System validation: this file separates raw schema syntax
  from schema well-formedness predicates. The spec describes these as validation rules;
  this module names the resulting schema invariants `WellFormed`.
- 3.6-3.10 Object, Interface, Union, Enum, and Input Object validation: modeled partially,
  mostly for uniqueness and type-reference well-formedness.
- Fidelity note: several normative rules are omitted, including reserved `__` names,
  non-empty object/interface/input-field lists, interface field/type covariance,
  interface cycles, input-object cycles/default cycles, directive validation,
  extensions, OneOf, mutation/subscription roots, and introspection.
-/
namespace GraphQL

namespace SchemaWellFormedness

-- Spec type-system uniqueness clauses: faithful as a generic list-level no-duplicates
-- predicate.
def namesAreUnique (names : List Name) : Prop :=
  names.Nodup

-- Spec 3.6.1 / 3.10 input value definition rules: partial; checks only
-- `IsInputType`, omitting default-value coercion and directive/name rules.
def inputValueDefinitionWellFormed (schema : Schema)
    (definition : InputValueDefinition) : Prop :=
  definition.inputType.isInputType schema

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

def fieldDefinitionsWellFormed (schema : Schema) (fields : List FieldDefinition) : Prop :=
  namesAreUnique (fields.map FieldDefinition.name)
    ∧ ∀ field, field ∈ fields -> fieldDefinitionWellFormed schema field

-- Spec 3.6 object type rules: partial; checks fields and declared interface existence,
-- but not interface field implementation compatibility or non-empty fields.
def objectTypeWellFormed (schema : Schema) (objectType : ObjectType) : Prop :=
  fieldDefinitionsWellFormed schema objectType.fields
    ∧ namesAreUnique objectType.interfaces
    ∧ ∀ interfaceName, interfaceName ∈ objectType.interfaces ->
      schema.interfaceType interfaceName

-- Spec 3.7 interface type rules: partial; checks fields and declared interface existence,
-- but not interface field implementation compatibility, cycles, or non-empty fields.
def interfaceTypeWellFormed (schema : Schema) (interfaceType : InterfaceType) : Prop :=
  fieldDefinitionsWellFormed schema interfaceType.fields
    ∧ namesAreUnique interfaceType.interfaces
    ∧ ∀ implementedInterfaceName,
      implementedInterfaceName ∈ interfaceType.interfaces ->
        schema.interfaceType implementedInterfaceName

-- Spec 3.8 union type rules: partial; checks unique object members but does not
-- enforce non-empty member lists or directives/extensions.
def unionTypeWellFormed (schema : Schema) (unionType : UnionType) : Prop :=
  namesAreUnique unionType.members
    ∧ ∀ objectName, objectName ∈ unionType.members -> schema.objectType objectName

-- Spec 3.9 enum type rules: partial; checks unique values but omits non-empty
-- values, reserved names, directives, and deprecation rules.
def enumTypeWellFormed (enumType : EnumType) : Prop :=
  namesAreUnique enumType.values

-- Spec 3.10 input object type rules: partial; checks input field definitions but
-- omits non-empty fields, input-object cycles, default-value cycles, and OneOf rules.
def inputObjectTypeWellFormed (schema : Schema) (inputObjectType : InputObjectType) : Prop :=
  inputValueDefinitionsWellFormed schema inputObjectType.inputFields

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

-- Spec 3.3 schema rules: partial; checks unique type names and a query object root,
-- omitting operation-type uniqueness/existence for mutation/subscription and directive
-- validation.
def schemaWellFormed (schema : Schema) : Prop :=
  namesAreUnique (schema.allTypes.map TypeDefinition.name)
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
