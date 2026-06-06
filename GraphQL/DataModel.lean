import GraphQL.Execution

/-!
Spec reference: GraphQL September 2025.
- 6 Execution and 7 Response: this module gives an extensional data model for the
  intentionally scoped execution fragment: query-like operations, already-coerced
  arguments/variables, built-in `@skip`/`@include`, no introspection, no mutation, and no
  subscription.
- The model represents typed object identities with field facts. It can be converted into
  the existing resolver interface, and it provides the semantic predicates used by
  normal-form correctness statements.
- Fidelity note: scalar coercion, enum coercion, input coercion, result coercion, execution
  errors, null bubbling, and serialization are assumed out of scope here.
-/
namespace GraphQL

namespace DataModel

-- Non-spec object identity used by the proof-facing typed store model.
abbrev ObjectId := Nat

-- Spec 6.4.2 field resolution key, specialized to already-coerced argument values.
structure FieldKey where
  name : Name
  arguments : List Argument := []
deriving Repr

namespace FieldKey

-- Spec 2.10 input value equality for store keys: structural equality over already
-- coerced argument values. Input object field order is ignored, matching GraphQL's
-- argument/input-object semantics after validation has rejected duplicate names.
def insertInputFieldSorted
    (field : Name × InputValue) :
    List (Name × InputValue) -> List (Name × InputValue)
  | [] => [field]
  | candidate :: rest =>
      if field.1 <= candidate.1 then
        field :: candidate :: rest
      else
        candidate :: insertInputFieldSorted field rest

def sortInputFieldsByName : List (Name × InputValue) -> List (Name × InputValue)
  | [] => []
  | field :: rest =>
      insertInputFieldSorted field (sortInputFieldsByName rest)

mutual
  def canonicalInputValue : InputValue -> InputValue
    | .null => .null
    | .int value => .int value
    | .float value => .float value
    | .string value => .string value
    | .boolean value => .boolean value
    | .enum value => .enum value
    | .variable name => .variable name
    | .list values => .list (canonicalInputValues values)
    | .object fields =>
        .object (sortInputFieldsByName (canonicalInputFields fields))

  def canonicalInputValues : List InputValue -> List InputValue
    | [] => []
    | value :: rest =>
        canonicalInputValue value :: canonicalInputValues rest

  def canonicalInputFields :
      List (Name × InputValue) -> List (Name × InputValue)
    | [] => []
    | (name, value) :: rest =>
        (name, canonicalInputValue value) :: canonicalInputFields rest
end

mutual
  def structuralInputValueEqBool : InputValue -> InputValue -> Bool
    | .null, .null => true
    | .int left, .int right => left == right
    | .float left, .float right => left == right
    | .string left, .string right => left == right
    | .boolean left, .boolean right => left == right
    | .enum left, .enum right => left == right
    | .variable left, .variable right => left == right
    | .list left, .list right => structuralInputValuesEqBool left right
    | .object left, .object right => structuralInputFieldsEqBool left right
    | _left, _right => false

  def structuralInputValuesEqBool :
      List InputValue -> List InputValue -> Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        structuralInputValueEqBool left right
          && structuralInputValuesEqBool leftRest rightRest
    | _left, _right => false

  def structuralInputFieldsEqBool :
      List (Name × InputValue) -> List (Name × InputValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: leftRest,
        (rightName, rightValue) :: rightRest =>
        (leftName == rightName)
          && structuralInputValueEqBool leftValue rightValue
          && structuralInputFieldsEqBool leftRest rightRest
    | _left, _right => false
end

def inputValueEqBool (left right : InputValue) : Bool :=
  structuralInputValueEqBool
    (canonicalInputValue left) (canonicalInputValue right)

def inputValuesEqBool (left right : List InputValue) : Bool :=
  structuralInputValuesEqBool
    (canonicalInputValues left) (canonicalInputValues right)

def inputFieldsEqBool (left right : List (Name × InputValue)) : Bool :=
  structuralInputFieldsEqBool
    (sortInputFieldsByName (canonicalInputFields left))
    (sortInputFieldsByName (canonicalInputFields right))

def canonicalArgument (argument : Argument) : Argument :=
  { argument with value := canonicalInputValue argument.value }

def argumentEqBool (left right : Argument) : Bool :=
  (left.name == right.name)
    && structuralInputValueEqBool
      (canonicalInputValue left.value) (canonicalInputValue right.value)

def insertArgumentSorted (argument : Argument) : List Argument -> List Argument
  | [] => [argument]
  | candidate :: rest =>
      if argument.name <= candidate.name then
        argument :: candidate :: rest
      else
        candidate :: insertArgumentSorted argument rest

def sortArgumentsByName : List Argument -> List Argument
  | [] => []
  | argument :: rest =>
      insertArgumentSorted argument (sortArgumentsByName rest)

def canonicalArguments : List Argument -> List Argument
  | [] => []
  | argument :: rest =>
      canonicalArgument argument :: canonicalArguments rest

def argumentsEqBoolOrdered : List Argument -> List Argument -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      argumentEqBool left right && argumentsEqBoolOrdered leftRest rightRest
  | _left, _right => false

-- Spec 6.4.2 field resolution key comparison, specialized to this model's raw
-- already-coerced argument representation. Argument order is ignored.
def argumentsEqBool (left right : List Argument) : Bool :=
  argumentsEqBoolOrdered
    (sortArgumentsByName (canonicalArguments left))
    (sortArgumentsByName (canonicalArguments right))

end FieldKey

-- Host result values before GraphQL response serialization, retaining runtime object type.
inductive Value where
  | null
  | scalar (value : String)
  | object (typeName : Name) (id : ObjectId)
  | list (values : List Value)
deriving Repr

namespace Value

-- Spec-related bridge from proof-facing store values to execution resolver values.
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

-- Non-spec typed object record for the proof-facing store model.
structure ObjectRecord where
  typeName : Name
  id : ObjectId
  fields : List (FieldKey × Value) := []
deriving Repr

namespace ObjectRecord

-- Spec 6.4.2 field resolution lookup specialized to already-coerced arguments.
def lookupFieldIn? (fieldName : Name) (arguments : List Argument) :
    List (FieldKey × Value) -> Option Value
  | [] => none
  | (key, value) :: rest =>
      if key.name == fieldName
          && FieldKey.argumentsEqBool key.arguments arguments then
        some value
      else
        lookupFieldIn? fieldName arguments rest

def lookupField? (object : ObjectRecord) (fieldName : Name)
    (arguments : List Argument) : Option Value :=
  lookupFieldIn? fieldName arguments object.fields

-- Spec-related store invariant: each stored field fact conforms to schema lookup.
def fieldFactWellTyped (schema : Schema) (object : ObjectRecord)
    (fieldKey : FieldKey) (value : Value) : Prop :=
  ∃ fieldDefinition,
    schema.lookupField object.typeName fieldKey.name = some fieldDefinition
      ∧ Value.conformsToType schema value fieldDefinition.outputType

-- Spec-related store invariant for object records.
def wellTyped (schema : Schema) (object : ObjectRecord) : Prop :=
  schema.objectType object.typeName
    ∧ ∀ fieldFact, fieldFact ∈ object.fields ->
      fieldFactWellTyped schema object fieldFact.fst fieldFact.snd

end ObjectRecord

-- Non-spec finite typed object store used to instantiate the execution resolver API.
structure Store where
  objects : List ObjectRecord := []
deriving Repr

namespace Store

-- Non-spec object lookup by runtime type and identity.
def lookupObject? (store : Store) (typeName : Name)
    (id : ObjectId) : Option ObjectRecord :=
  store.objects.find? (fun object => object.typeName == typeName && object.id == id)

-- Spec 6.4.2 `ResolveFieldValue` over proof-facing store values.
def resolveValue (store : Store) (fieldName : Name) (arguments : List Argument) :
    Value -> Value
  | .object runtimeType id =>
      match store.lookupObject? runtimeType id with
      | none => .null
      | some object =>
          match object.lookupField? fieldName arguments with
          | none => .null
          | some value => value
  | _ => .null

-- Spec 6.4.2 `ResolveFieldValue` bridge for the existing execution engine.
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

-- Spec 6.4.2 resolver interface backed by the proof-facing store.
def resolvers (store : Store) : Execution.Resolvers :=
  { resolve := fun _parentType fieldName arguments source =>
      store.resolve fieldName arguments source }

-- Spec-related store well-typedness invariant over all object records.
def wellTyped (schema : Schema) (store : Store) : Prop :=
  ∀ object, object ∈ store.objects -> object.wellTyped schema

end Store

-- Non-spec query root object identity for store-backed execution.
structure Root where
  typeName : Name
  id : ObjectId
deriving Repr, DecidableEq

namespace Root

-- Spec-related bridge from a proof-facing root to the execution source value.
def toExecutionValue (root : Root) : Execution.Value :=
  .object root.typeName root.id

-- Spec-related root well-typedness: the root object is included in the query root type.
def wellTyped (schema : Schema) (root : Root) : Prop :=
  schema.typeIncludesObject schema.queryType root.typeName

end Root

-- Spec 6.2.1 `ExecuteQuery` over raw modeled operations and store-backed resolvers.
def executeOperation (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (root : Root) : Execution.Response :=
  Execution.executeQuery schema store.resolvers variableValues
    operation root.toExecutionValue

-- Explicit-depth store-backed execution used by semantic equivalence theorems.
def executeOperationAtDepth (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat) (root : Root) : Execution.Response :=
  Execution.executeQueryAtDepth schema store.resolvers variableValues
    operation depth root.toExecutionValue

-- Spec-related operation equivalence over all well-typed store/root inputs.
def operationsEquivalentOnData (schema : Schema)
    (left right : Operation) : Prop :=
  ∀ store variableValues depth root,
    store.wellTyped schema ->
      root.wellTyped schema ->
        executeOperationAtDepth schema store variableValues left depth root
          = executeOperationAtDepth schema store variableValues right depth root

end DataModel

end GraphQL
