import GraphQL.Schema

namespace GraphQL

namespace SchemaWellFormedness

def namesNodup (names : List Name) : Prop :=
  names.Nodup

def inputValueDefinitionWellFormed (schema : Schema)
    (definition : InputValueDefinition) : Prop :=
  definition.inputType.validInput schema

def inputValueDefinitionsWellFormed (schema : Schema)
    (definitions : List InputValueDefinition) : Prop :=
  namesNodup (definitions.map InputValueDefinition.name)
    ∧ ∀ definition, definition ∈ definitions ->
      inputValueDefinitionWellFormed schema definition

def fieldDefinitionWellFormed (schema : Schema) (field : FieldDefinition) : Prop :=
  field.outputType.validOutput schema
    ∧ inputValueDefinitionsWellFormed schema field.arguments

def fieldDefinitionsWellFormed (schema : Schema) (fields : List FieldDefinition) : Prop :=
  namesNodup (fields.map FieldDefinition.name)
    ∧ ∀ field, field ∈ fields -> fieldDefinitionWellFormed schema field

def objectTypeWellFormed (schema : Schema) (objectType : ObjectType) : Prop :=
  fieldDefinitionsWellFormed schema objectType.fields
    ∧ namesNodup objectType.interfaces
    ∧ ∀ interfaceName, interfaceName ∈ objectType.interfaces ->
      ∃ interfaceType,
        schema.lookupInterface interfaceName = some interfaceType
          ∧ objectType.name ∈ interfaceType.implementations

def interfaceTypeWellFormed (schema : Schema) (interfaceType : InterfaceType) : Prop :=
  fieldDefinitionsWellFormed schema interfaceType.fields
    ∧ namesNodup interfaceType.implementations
    ∧ ∀ objectName, objectName ∈ interfaceType.implementations ->
      ∃ objectType,
        schema.lookupObject objectName = some objectType
          ∧ interfaceType.name ∈ objectType.interfaces

def unionTypeWellFormed (schema : Schema) (unionType : UnionType) : Prop :=
  namesNodup unionType.members
    ∧ ∀ objectName, objectName ∈ unionType.members -> schema.objectType objectName

def enumTypeWellFormed (enumType : EnumType) : Prop :=
  namesNodup enumType.values

def inputObjectTypeWellFormed (schema : Schema) (inputObjectType : InputObjectType) : Prop :=
  inputValueDefinitionsWellFormed schema inputObjectType.inputFields

def typeDefinitionWellFormed (schema : Schema) : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .object objectType => objectTypeWellFormed schema objectType
  | .interface interfaceType => interfaceTypeWellFormed schema interfaceType
  | .union unionType => unionTypeWellFormed schema unionType
  | .enum enumType => enumTypeWellFormed enumType
  | .inputObject inputObjectType => inputObjectTypeWellFormed schema inputObjectType

def schemaWellFormed (schema : Schema) : Prop :=
  namesNodup (schema.allTypes.map TypeDefinition.name)
    ∧ schema.objectType schema.queryType
    ∧ ∀ typeDefinition, typeDefinition ∈ schema.types ->
      typeDefinitionWellFormed schema typeDefinition

structure WellFormedSchema where
  schema : Schema
  wellFormed : schemaWellFormed schema

end SchemaWellFormedness

end GraphQL
