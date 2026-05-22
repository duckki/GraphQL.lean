import GraphQL.Syntax

namespace GraphQL

structure ArgumentDefinition where
  name : Name
  typeRef : TypeRef
deriving Repr, DecidableEq

structure FieldDefinition where
  name : Name
  typeRef : TypeRef
  arguments : List ArgumentDefinition := []
deriving Repr, DecidableEq

structure ScalarType where
  name : Name
deriving Repr, DecidableEq

structure EnumType where
  name : Name
  values : List Name
deriving Repr, DecidableEq

structure ObjectType where
  name : Name
  fields : List FieldDefinition
  interfaces : List Name := []
deriving Repr, DecidableEq

structure InterfaceType where
  name : Name
  fields : List FieldDefinition
  implementations : List Name
deriving Repr, DecidableEq

structure UnionType where
  name : Name
  members : List Name
deriving Repr, DecidableEq

inductive TypeDefinition where
  | scalar : ScalarType -> TypeDefinition
  | enum : EnumType -> TypeDefinition
  | object : ObjectType -> TypeDefinition
  | interface : InterfaceType -> TypeDefinition
  | union : UnionType -> TypeDefinition
deriving Repr, DecidableEq

namespace TypeDefinition

def name : TypeDefinition -> Name
  | .scalar scalarType => scalarType.name
  | .enum enumType => enumType.name
  | .object objectType => objectType.name
  | .interface interfaceType => interfaceType.name
  | .union unionType => unionType.name

def fields? : TypeDefinition -> Option (List FieldDefinition)
  | .object objectType => some objectType.fields
  | .interface interfaceType => some interfaceType.fields
  | _ => none

def possibleObjectNames : TypeDefinition -> List Name
  | .object objectType => [objectType.name]
  | .interface interfaceType => interfaceType.implementations
  | .union unionType => unionType.members
  | .scalar _ => []
  | .enum _ => []

def isLeaf : TypeDefinition -> Prop
  | .scalar _ => True
  | .enum _ => True
  | _ => False

def isComposite : TypeDefinition -> Prop
  | .object _ => True
  | .interface _ => True
  | .union _ => True
  | _ => False

end TypeDefinition

structure Schema where
  queryType : Name
  types : List TypeDefinition
deriving Repr, DecidableEq

namespace Schema

def lookupType (schema : Schema) (typeName : Name) : Option TypeDefinition :=
  schema.types.find? (fun typeDefinition => typeDefinition.name == typeName)

def lookupObject (schema : Schema) (typeName : Name) : Option ObjectType := do
  match schema.lookupType typeName with
  | some (.object object) => some object
  | _ => none

def lookupField (schema : Schema) (parentType fieldName : Name) : Option FieldDefinition := do
  let typeDefinition <- schema.lookupType parentType
  let fields <- typeDefinition.fields?
  fields.find? (fun field => field.name == fieldName)

def fieldReturnType? (schema : Schema) (parentType fieldName : Name) : Option Name := do
  let field <- schema.lookupField parentType fieldName
  pure field.typeRef.namedType

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
