import GraphQL.Syntax

namespace GraphQL

inductive BuiltinScalar where
  | int
  | float
  | string
  | boolean
  | id
deriving Repr, DecidableEq

namespace BuiltinScalar

def name : BuiltinScalar -> Name
  | .int => "Int"
  | .float => "Float"
  | .string => "String"
  | .boolean => "Boolean"
  | .id => "ID"

end BuiltinScalar

structure CustomScalarType where
  name : Name
deriving Repr, DecidableEq

structure EnumType where
  name : Name
  values : List Name
deriving Repr, DecidableEq

structure InputValueDefinition where
  name : Name
  inputType : TypeRef
  defaultValue : Option InputValue := none
deriving Repr

structure FieldDefinition where
  name : Name
  outputType : TypeRef
  arguments : List InputValueDefinition := []
deriving Repr

structure ObjectType where
  name : Name
  fields : List FieldDefinition
  interfaces : List Name := []
deriving Repr

structure InterfaceType where
  name : Name
  fields : List FieldDefinition
  implementations : List Name
deriving Repr

structure UnionType where
  name : Name
  members : List Name
deriving Repr, DecidableEq

structure InputObjectType where
  name : Name
  inputFields : List InputValueDefinition
deriving Repr

inductive TypeDefinition where
  | builtinScalar : BuiltinScalar -> TypeDefinition
  | customScalar : CustomScalarType -> TypeDefinition
  | object : ObjectType -> TypeDefinition
  | interface : InterfaceType -> TypeDefinition
  | union : UnionType -> TypeDefinition
  | enum : EnumType -> TypeDefinition
  | inputObject : InputObjectType -> TypeDefinition
deriving Repr

namespace TypeDefinition

def name : TypeDefinition -> Name
  | .builtinScalar scalar => scalar.name
  | .customScalar scalar => scalar.name
  | .object objectType => objectType.name
  | .interface interfaceType => interfaceType.name
  | .union unionType => unionType.name
  | .enum enumType => enumType.name
  | .inputObject inputObjectType => inputObjectType.name

def fields? : TypeDefinition -> Option (List FieldDefinition)
  | .object objectType => some objectType.fields
  | .interface interfaceType => some interfaceType.fields
  | _ => none

def possibleObjectNames : TypeDefinition -> List Name
  | .object objectType => [objectType.name]
  | .interface interfaceType => interfaceType.implementations
  | .union unionType => unionType.members
  | _ => []

def isLeaf : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .enum _ => True
  | _ => False

def isComposite : TypeDefinition -> Prop
  | .object _ => True
  | .interface _ => True
  | .union _ => True
  | _ => False

def isInput : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .enum _ => True
  | .inputObject _ => True
  | _ => False

def isOutput : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .object _ => True
  | .interface _ => True
  | .union _ => True
  | .enum _ => True
  | _ => False

end TypeDefinition

structure Schema where
  queryType : Name
  types : List TypeDefinition
deriving Repr

namespace Schema

def builtinScalarDefinitions : List TypeDefinition :=
  [.builtinScalar .int, .builtinScalar .float, .builtinScalar .string,
    .builtinScalar .boolean, .builtinScalar .id]

def allTypes (schema : Schema) : List TypeDefinition :=
  builtinScalarDefinitions ++ schema.types

def lookupType (schema : Schema) (typeName : Name) : Option TypeDefinition :=
  schema.allTypes.find? (fun typeDefinition => typeDefinition.name == typeName)

def lookupObject (schema : Schema) (typeName : Name) : Option ObjectType := do
  match schema.lookupType typeName with
  | some (.object object) => some object
  | _ => none

def lookupInputObject (schema : Schema) (typeName : Name) : Option InputObjectType := do
  match schema.lookupType typeName with
  | some (.inputObject inputObject) => some inputObject
  | _ => none

def lookupField (schema : Schema) (parentType fieldName : Name) : Option FieldDefinition := do
  let typeDefinition <- schema.lookupType parentType
  let fields <- typeDefinition.fields?
  fields.find? (fun field => field.name == fieldName)

def lookupArgumentDefinition (definitions : List InputValueDefinition)
    (argumentName : Name) : Option InputValueDefinition :=
  definitions.find? (fun definition => definition.name == argumentName)

def fieldReturnType? (schema : Schema) (parentType fieldName : Name) : Option Name := do
  let field <- schema.lookupField parentType fieldName
  pure field.outputType.namedType

def possibleObjectNames (schema : Schema) (typeName : Name) : List Name :=
  match schema.lookupType typeName with
  | some typeDefinition => typeDefinition.possibleObjectNames
  | none => []

def typeIncludesObject (schema : Schema) (typeName objectName : Name) : Prop :=
  objectName ∈ schema.possibleObjectNames typeName

def typeIncludesObjectBool (schema : Schema) (typeName objectName : Name) : Bool :=
  (schema.possibleObjectNames typeName).contains objectName

def typesOverlap (schema : Schema) (left right : Name) : Prop :=
  ∃ objectName,
    schema.typeIncludesObject left objectName
      ∧ schema.typeIncludesObject right objectName

def typesOverlapBool (schema : Schema) (left right : Name) : Bool :=
  (schema.possibleObjectNames left).any
    (fun objectName => schema.typeIncludesObjectBool right objectName)

def typeExists (schema : Schema) (typeName : Name) : Prop :=
  schema.lookupType typeName ≠ none

def inputType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition
      ∧ typeDefinition.isInput

def outputType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition
      ∧ typeDefinition.isOutput

def compositeType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition
      ∧ typeDefinition.isComposite

def leafType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition
      ∧ typeDefinition.isLeaf

end Schema

end GraphQL
