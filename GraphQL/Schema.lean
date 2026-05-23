/-!
Spec reference: GraphQL September 2025.
- 2.1.8 Names: names identify schema and executable elements; this model stores raw
  strings and leaves grammar/reserved-name checks to well-formedness/validation work.
- 2.10 Input Values and 2.12 Type References: value and type-reference syntax are
  represented directly, with coercion and source parsing out of scope.
- 3.3-3.13 Type System: schema and type definitions cover core GraphQL types, wrapping
  types, built-in scalars, and the `@skip`/`@include` scalar dependencies, but omit
  descriptions, arbitrary directives, extensions, introspection, mutation/subscription
  roots, and OneOf metadata.
- 5.5.2.3 Fragment Spread Is Possible: possible-object helpers model the spec's
  `GetPossibleTypes` basis for overlap checks.
-/
namespace GraphQL

-- Spec 2.1.8 `Name`: partial; raw `String` does not enforce the GraphQL name grammar or
-- reserved `__` rules.
abbrev Name := String

-- Spec 2.12 `Type`, `NamedType`, `ListType`, `NonNullType`: partial; syntax is
-- represented, and invalid nested non-null is rejected by `TypeRef.wellFormed`/validity
-- predicates rather than by construction.
inductive TypeRef where
  | named : Name -> TypeRef
  | list : TypeRef -> TypeRef
  | nonNull : TypeRef -> TypeRef
deriving Repr, DecidableEq

namespace TypeRef

-- Spec 2.12 Type reference semantics: faithful for retrieving the underlying named type
-- of modeled wrapping references.
def namedType : TypeRef -> Name
  | .named name => name
  | .list inner => inner.namedType
  | .nonNull inner => inner.namedType

end TypeRef

-- Spec 2.10 `Value`: partial; literals and variables are represented, but
-- constant-vs-variable contexts and input coercion are handled elsewhere or omitted.
inductive InputValue where
  | null
  | int (value : Int)
  | float (value : String)
  | string (value : String)
  | boolean (value : Bool)
  | enum (value : Name)
  | list (values : List InputValue)
  | object (fields : List (Name × InputValue))
  | variable (name : Name)
deriving Repr

namespace InputValue

-- Spec 3.13.1 `@skip` / 3.13.2 `@include` `if` argument: partial; this only recognizes
-- statically provided Boolean literals.
def staticBoolean? : InputValue -> Option Bool
  | .boolean value => some value
  | _ => none

end InputValue

-- Spec 3.5.1-3.5.5 built-in scalars: faithful for the five required scalar names, without
-- modeling coercion behavior.
inductive BuiltinScalar where
  | int
  | float
  | string
  | boolean
  | id
deriving Repr, DecidableEq

namespace BuiltinScalar

-- Spec 3.5.1-3.5.5 built-in scalar names: faithful.
def name : BuiltinScalar -> Name
  | .int => "Int"
  | .float => "Float"
  | .string => "String"
  | .boolean => "Boolean"
  | .id => "ID"

end BuiltinScalar

-- Spec 3.5 `ScalarTypeDefinition`: partial; custom scalar identity only, no description,
-- directives, specifiedBy URL, or coercion hooks.
structure CustomScalarType where
  name : Name
deriving Repr, DecidableEq

-- Spec 3.9 `EnumTypeDefinition`: partial; enum values are named but descriptions,
-- directives, deprecation, and reserved-name validation are omitted.
structure EnumType where
  name : Name
  values : List Name
deriving Repr, DecidableEq

-- Spec 3.6.1 `InputValueDefinition` and 3.10 input fields: partial; name/type/default are
-- represented, but descriptions, directives, OneOf constraints, and value coercion are
-- omitted.
structure InputValueDefinition where
  name : Name
  inputType : TypeRef
  defaultValue : Option InputValue := none
deriving Repr

-- Spec 3.6 `FieldDefinition`: partial; name, return type, and arguments are represented,
-- but descriptions, directives, and deprecation are omitted.
structure FieldDefinition where
  name : Name
  outputType : TypeRef
  arguments : List InputValueDefinition := []
deriving Repr

-- Spec 3.6 `ObjectTypeDefinition`: partial; object fields and implemented interfaces are
-- represented, while descriptions, directives, extensions, and introspection fields are
-- omitted.
structure ObjectType where
  name : Name
  fields : List FieldDefinition
  interfaces : List Name := []
deriving Repr

-- Spec 3.7 `InterfaceTypeDefinition`: partial and inverted; fields are faithful, but
-- `implementations` stores implementors rather than the spec's declared implemented
-- interfaces.
structure InterfaceType where
  name : Name
  fields : List FieldDefinition
  implementations : List Name
deriving Repr

-- Spec 3.8 `UnionTypeDefinition`: partial; member object names are represented, but
-- descriptions, directives, extensions, and reserved-name validation are omitted.
structure UnionType where
  name : Name
  members : List Name
deriving Repr, DecidableEq

-- Spec 3.10 `InputObjectTypeDefinition`: partial; input fields are represented, but
-- descriptions, directives, OneOf status, extensions, and cycle validation are omitted.
structure InputObjectType where
  name : Name
  inputFields : List InputValueDefinition
deriving Repr

-- Spec 3.4 `TypeDefinition`: partial; core type categories are represented, but
-- type-system extensions, directive definitions, and introspection definitions are
-- outside this syntax.
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

-- Spec 3.4 named type definitions: faithful for the modeled type categories.
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

-- Spec 5.5.2.3 `GetPossibleTypes`: partial; object and union cases are direct, interface
-- cases depend on the stored `implementations` list rather than deriving it from object
-- declarations.
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

-- Spec note in 5.3.2 and type-system usage of composite types: faithful for
-- object/interface/union in the modeled type universe.
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

-- Spec 3.3 `Schema`: partial; only the query root and type list are modeled, omitting
-- mutation/subscription roots, directives, descriptions, extensions, and introspection.
structure Schema where
  queryType : Name
  types : List TypeDefinition
deriving Repr

namespace Schema

-- Spec 3.5 built-in scalar availability: faithful for adding the five required scalar
-- definitions to every modeled schema.
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

def lookupInterface (schema : Schema) (typeName : Name) : Option InterfaceType := do
  match schema.lookupType typeName with
  | some (.interface interfaceType) => some interfaceType
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

-- Spec 5.5.2.3 `GetPossibleTypes`: partial; delegates to
-- `TypeDefinition.possibleObjectNames`, so interface fidelity depends on stored
-- implementors.
def possibleObjectNames (schema : Schema) (typeName : Name) : List Name :=
  match schema.lookupType typeName with
  | some typeDefinition => typeDefinition.possibleObjectNames
  | none => []

def typeIncludesObject (schema : Schema) (typeName objectName : Name) : Prop :=
  objectName ∈ schema.possibleObjectNames typeName

def typeIncludesObjectBool (schema : Schema) (typeName objectName : Name) : Bool :=
  (schema.possibleObjectNames typeName).contains objectName

-- Spec 5.5.2.3 Fragment Spread Is Possible: faithful at the set-overlap level for modeled
-- possible-object lists.
def typesOverlap (schema : Schema) (left right : Name) : Prop :=
  ∃ objectName,
    schema.typeIncludesObject left objectName
      ∧ schema.typeIncludesObject right objectName

def typesOverlapBool (schema : Schema) (left right : Name) : Bool :=
  (schema.possibleObjectNames left).any
    (fun objectName => schema.typeIncludesObjectBool right objectName)

def typeExists (schema : Schema) (typeName : Name) : Prop :=
  schema.lookupType typeName ≠ none

def objectType (schema : Schema) (typeName : Name) : Prop :=
  ∃ objectType,
    schema.lookupType typeName = some (.object objectType)

def interfaceType (schema : Schema) (typeName : Name) : Prop :=
  ∃ interfaceType,
    schema.lookupType typeName = some (.interface interfaceType)

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

namespace TypeRef

-- Spec 2.12 / 3.12 `NonNullType`: faithful for rejecting a non-null wrapper around
-- another non-null wrapper.
def wellFormed : TypeRef -> Prop
  | .named _ => True
  | .list inner => inner.wellFormed
  | .nonNull (.nonNull _) => False
  | .nonNull inner => inner.wellFormed

-- Spec 3.4.2 `IsInputType`: faithful for the modeled type categories and wrapping-type
-- recursion.
def validInput : TypeRef -> Schema -> Prop
  | .named name, schema => schema.inputType name
  | .list inner, schema => inner.validInput schema
  | .nonNull (.nonNull _), _schema => False
  | .nonNull inner, schema => inner.validInput schema

-- Spec 3.4.2 `IsOutputType`: faithful for the modeled type categories and wrapping-type
-- recursion.
def validOutput : TypeRef -> Schema -> Prop
  | .named name, schema => schema.outputType name
  | .list inner, schema => inner.validOutput schema
  | .nonNull (.nonNull _), _schema => False
  | .nonNull inner, schema => inner.validOutput schema

end TypeRef

end GraphQL
