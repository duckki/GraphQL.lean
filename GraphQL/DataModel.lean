import GraphQL.Execution
import GraphQL.NormalForm
import GraphQL.ResponseShape

/-!
Spec reference: GraphQL September 2025.
- 6 Execution and 7 Response: this module gives an extensional data model for the
  intentionally scoped execution fragment: query-like operations, already-coerced
  arguments/variables, built-in `@skip`/`@include`, no introspection, no mutation, and no
  subscription.
- The model represents typed object identities with field facts. It can be converted into
  the existing resolver interface, and it provides the semantic predicates needed to state
  response-shape and ground-normal-form correctness.
- Fidelity note: scalar coercion, enum coercion, input coercion, result coercion, execution
  errors, null bubbling, and serialization are assumed out of scope here.
-/
namespace GraphQL

namespace DataModel

abbrev ObjectId := Nat

-- Spec 6.4.2 field resolution key, specialized to already-coerced argument values.
structure FieldKey where
  name : Name
  arguments : List Argument := []
deriving Repr

-- Host result values before GraphQL response serialization, retaining runtime object type.
inductive Value where
  | null
  | scalar (value : String)
  | object (typeName : Name) (id : ObjectId)
  | list (values : List Value)
deriving Repr

namespace Value

def toExecutionValue : Value -> Execution.Value
  | .null => .null
  | .scalar value => .scalar value
  | .object typeName id => .object typeName id
  | .list values => .list (values.map toExecutionValue)

-- Assumption boundary for the scoped model: result values are already type-conformant.
def conformsToType (schema : Schema) : Value -> TypeRef -> Prop
  | .null, .nonNull _inner => False
  | .null, _typeRef => True
  | .scalar _value, .named typeName => schema.isLeafType typeName
  | .scalar value, .nonNull inner => conformsToType schema (.scalar value) inner
  | .scalar _value, .list _inner => False
  | .object objectType _id, .named typeName => schema.typeIncludesObject typeName objectType
  | .object objectType id, .nonNull inner =>
      conformsToType schema (.object objectType id) inner
  | .object _objectType _id, .list _inner => False
  | .list values, .list inner =>
      ∀ value, value ∈ values -> conformsToType schema value inner
  | .list values, .nonNull inner => conformsToType schema (.list values) inner
  | .list _values, .named _typeName => False

end Value

structure ObjectRecord where
  typeName : Name
  id : ObjectId
  fields : List (FieldKey × Value) := []
deriving Repr

namespace ObjectRecord

def lookupFieldIn? (fieldName : Name) (arguments : List Argument) :
    List (FieldKey × Value) -> Option Value
  | [] => none
  | (key, value) :: rest =>
      if key.name == fieldName
          && ResponseShape.SelectedField.argumentsEqBool key.arguments arguments then
        some value
      else
        lookupFieldIn? fieldName arguments rest

def lookupField? (object : ObjectRecord) (fieldName : Name)
    (arguments : List Argument) : Option Value :=
  lookupFieldIn? fieldName arguments object.fields

def fieldFactWellTyped (schema : Schema) (object : ObjectRecord)
    (fieldKey : FieldKey) (value : Value) : Prop :=
  ∃ fieldDefinition,
    schema.lookupField object.typeName fieldKey.name = some fieldDefinition
      ∧ Value.conformsToType schema value fieldDefinition.outputType

def wellTyped (schema : Schema) (object : ObjectRecord) : Prop :=
  schema.objectType object.typeName
    ∧ ∀ fieldFact, fieldFact ∈ object.fields ->
      fieldFactWellTyped schema object fieldFact.fst fieldFact.snd

end ObjectRecord

structure Store where
  objects : List ObjectRecord := []
deriving Repr

namespace Store

def lookupObject? (store : Store) (typeName : Name)
    (id : ObjectId) : Option ObjectRecord :=
  store.objects.find? (fun object => object.typeName == typeName && object.id == id)

def resolve (store : Store) (fieldName : Name) (arguments : List Argument)
    (source : Execution.Value) : Execution.Value :=
  match source with
  | .object runtimeType id =>
      match store.lookupObject? runtimeType id with
      | none => .null
      | some object =>
          match object.lookupField? fieldName arguments with
          | none => .null
          | some value => value.toExecutionValue
  | _ => .null

def resolvers (store : Store) : Execution.Resolvers :=
  { resolve := fun _parentType fieldName arguments source =>
      store.resolve fieldName arguments source }

def wellTyped (schema : Schema) (store : Store) : Prop :=
  ∀ object, object ∈ store.objects -> object.wellTyped schema

end Store

structure Root where
  typeName : Name
  id : ObjectId
deriving Repr, DecidableEq

namespace Root

def toExecutionValue (root : Root) : Execution.Value :=
  .object root.typeName root.id

def wellTyped (schema : Schema) (root : Root) : Prop :=
  schema.typeIncludesObject schema.queryType root.typeName

end Root

def executeSemanticQuery (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Semantic.Operation) (root : Root) : Execution.Response :=
  Execution.executeSemanticQuery schema store.resolvers variableValues
    operation root.toExecutionValue

def executeOperation (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (root : Root) : Execution.Response :=
  Execution.executeQuery schema store.resolvers variableValues
    operation root.toExecutionValue

-- Typed response trees retain runtime object type so response-shape conditions can be
-- interpreted without relying on introspection fields.
inductive TypedResponse where
  | null
  | scalar (value : String)
  | object (typeName : Name) (fields : List (Name × TypedResponse))
  | list (values : List TypedResponse)
deriving Repr

namespace TypedResponse

mutual
  def erase : TypedResponse -> Execution.Response
    | .null => .null
    | .scalar value => .scalar value
    | .object _typeName fields => .object (eraseFields fields)
    | .list values => .list (eraseList values)

  def eraseList : List TypedResponse -> List Execution.Response
    | [] => []
    | value :: rest => erase value :: eraseList rest

  def eraseFields :
      List (Name × TypedResponse) -> List (Name × Execution.Response)
    | [] => []
    | (responseName, value) :: rest =>
        (responseName, erase value) :: eraseFields rest
end

end TypedResponse

def possibleTypesHoldBool (possibleTypes : Option (List Name))
    (runtimeType : Name) : Bool :=
  match possibleTypes with
  | none => true
  | some names => names.contains runtimeType

def booleanLiteralHoldsBool (variableValues : Execution.VariableValues) :
    ResponseShape.BooleanLiteral -> Bool
  | .positive name =>
      match Execution.inputValueBoolean? variableValues (.variable name) with
      | some value => value
      | none => false
  | .negative name =>
      match Execution.inputValueBoolean? variableValues (.variable name) with
      | some value => !value
      | none => false

def conditionHoldsBool (variableValues : Execution.VariableValues)
    (runtimeType : Name) (condition : ResponseShape.Condition) : Bool :=
  possibleTypesHoldBool condition.possibleTypes runtimeType
    && condition.booleanLiterals.all
      (fun literal => booleanLiteralHoldsBool variableValues literal)

def variantHeaderActiveBool (variableValues : Execution.VariableValues)
    (runtimeType : Name) (header : ResponseShape.VariantHeader) : Bool :=
  conditionHoldsBool variableValues runtimeType header.fst

def shapeEmptyBool : ResponseShape.Shape -> Bool
  | ⟨[]⟩ => true
  | ⟨_ :: _⟩ => false

-- A checked relation between a typed response tree and a response-shape summary. It is
-- fuel-bounded for proof ergonomics; callers should use fuel at least the response depth.
mutual
  def typedResponseConformsToShapeBool (variableValues : Execution.VariableValues) :
      Nat -> TypedResponse -> ResponseShape.Shape -> Bool
    | 0, _response, _shape => true
    | _fuel + 1, .null, _shape => true
    | _fuel + 1, .scalar _value, shape => shapeEmptyBool shape
    | fuel + 1, .list values, shape =>
        values.all
          (fun value => typedResponseConformsToShapeBool variableValues fuel value shape)
    | fuel + 1, .object runtimeType fields, shape =>
        typedFieldsConformToShapeBool variableValues fuel runtimeType fields shape

  def typedFieldsConformToShapeBool (variableValues : Execution.VariableValues) :
      Nat -> Name -> List (Name × TypedResponse) -> ResponseShape.Shape -> Bool
    | 0, _runtimeType, _fields, _shape => true
    | _fuel + 1, _runtimeType, [], _shape => true
    | fuel + 1, runtimeType, (responseName, value) :: rest, ⟨shapeFields⟩ =>
        match ResponseShape.Shape.lookupField responseName shapeFields with
        | none => false
        | some variants =>
            typedVariantConformsToShapeBool variableValues fuel runtimeType value variants
              && typedFieldsConformToShapeBool variableValues fuel runtimeType rest
                ⟨shapeFields⟩

  def typedVariantConformsToShapeBool (variableValues : Execution.VariableValues) :
      Nat -> Name -> TypedResponse -> List ResponseShape.Shape.Variant -> Bool
    | 0, _runtimeType, _value, _variants => true
    | _fuel + 1, _runtimeType, _value, [] => false
    | fuel + 1, runtimeType, value, (header, childShape) :: rest =>
        (variantHeaderActiveBool variableValues runtimeType header
          && typedResponseConformsToShapeBool variableValues fuel value childShape)
        || typedVariantConformsToShapeBool variableValues fuel runtimeType value rest
end

def semanticOperationsEquivalentOnData (schema : Schema)
    (left right : Semantic.Operation) : Prop :=
  ∀ store variableValues root,
    store.wellTyped schema ->
      root.wellTyped schema ->
        executeSemanticQuery schema store variableValues left root
          = executeSemanticQuery schema store variableValues right root

def operationsEquivalentOnData (schema : Schema) (left right : Operation) : Prop :=
  semanticOperationsEquivalentOnData schema
    (Semantic.fromOperation left) (Semantic.fromOperation right)

def groundNormalFormCorrect (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  semanticOperationsEquivalentOnData schema operation
    (NormalForm.normalizeSemanticOperation schema operation)

def responseShapeCorrectForTypedResponse (schema : Schema)
    (operation : Semantic.Operation)
    (variableValues : Execution.VariableValues)
    (response : TypedResponse) : Prop :=
  typedResponseConformsToShapeBool variableValues (operation.size + 1)
    response (ResponseShape.Shape.ofSemanticOperation schema operation) = true

end DataModel

end GraphQL
