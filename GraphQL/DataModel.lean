import GraphQL.Execution
import GraphQL.NormalForm

/-!
Spec reference: GraphQL September 2025.
- 6 Execution and 7 Response: this module gives an extensional data model for the
  intentionally scoped execution fragment: query-like operations, already-coerced
  arguments/variables, built-in `@skip`/`@include`, no introspection, no mutation, and no
  subscription.
- The model represents typed object identities with field facts. It can be converted into
  the existing resolver interface, and it provides the semantic predicates needed to state
  ground-normal-form correctness.
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

theorem inputValueEqBool_objectFieldsOrderInsensitive :
    inputValueEqBool
      (.object [("left", .int 1), ("right", .boolean true)])
      (.object [("right", .boolean true), ("left", .int 1)]) = true := by
  rfl

theorem argumentsEqBool_orderInsensitive :
    argumentsEqBool
      [
        { name := "left", value := .int 1 },
        { name := "right", value := .object [("nested", .string "value")] }
      ]
      [
        { name := "right", value := .object [("nested", .string "value")] },
        { name := "left", value := .int 1 }
      ] = true := by
  rfl

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

@[simp]
theorem toExecutionValue_null :
    toExecutionValue .null = Execution.Value.null := by
  simp [toExecutionValue]

@[simp]
theorem toExecutionValue_scalar (value : String) :
    toExecutionValue (.scalar value) = Execution.Value.scalar value := by
  simp [toExecutionValue]

@[simp]
theorem toExecutionValue_object (typeName : Name) (id : ObjectId) :
    toExecutionValue (.object typeName id) = Execution.Value.object typeName id := by
  simp [toExecutionValue]

@[simp]
theorem toExecutionValue_list (values : List Value) :
    toExecutionValue (.list values) = Execution.Value.list (values.map toExecutionValue) := by
  simp [toExecutionValue]

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

theorem lookupField?_argumentsOrderInsensitive :
    lookupField?
      { typeName := "Type",
        id := 0,
        fields := [
          ({
            name := "field",
            arguments := [
              { name := "filter",
                value := .object [("left", .int 1), ("right", .boolean true)] },
              { name := "limit", value := .int 10 }
            ]
          }, .scalar "ok")
        ] }
      "field"
      [
        { name := "limit", value := .int 10 },
        { name := "filter",
          value := .object [("right", .boolean true), ("left", .int 1)] }
      ] = some (.scalar "ok") := by
  rfl

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

theorem resolveValue_toExecutionValue (store : Store)
    (fieldName : Name) (arguments : List Argument) (source : Value) :
    (store.resolveValue fieldName arguments source).toExecutionValue
      = store.resolve fieldName arguments source.toExecutionValue := by
  cases source with
  | null =>
      simp [resolveValue, resolve]
  | scalar value =>
      simp [resolveValue, resolve]
  | object runtimeType id =>
      simp [resolveValue, resolve]
      cases store.lookupObject? runtimeType id with
      | none =>
          simp
      | some object =>
          cases hfield : object.lookupField? fieldName arguments with
          | none =>
              simp [hfield]
          | some value =>
              simp [hfield]
  | list values =>
      simp [resolveValue, resolve]

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

theorem executeOperation_usesStoreResolvers (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (root : Root) :
    executeOperation schema store variableValues operation root
      = Execution.executeQuery schema store.resolvers variableValues
        operation root.toExecutionValue := by
  rfl

-- Spec-related operation equivalence over all well-typed store/root inputs.
def operationsEquivalentOnData (schema : Schema)
    (left right : Operation) : Prop :=
  ∀ store variableValues root,
    store.wellTyped schema ->
      root.wellTyped schema ->
        executeOperation schema store variableValues left root
          = executeOperation schema store variableValues right root

theorem operationsEquivalentOnData_refl (schema : Schema) (operation : Operation) :
    operationsEquivalentOnData schema operation operation := by
  intro _store _variableValues _root _hstore _hroot
  rfl

theorem operationsEquivalentOnData_symm (schema : Schema) {left right : Operation} :
    operationsEquivalentOnData schema left right ->
      operationsEquivalentOnData schema right left := by
  intro hequivalent store variableValues root hstore hroot
  exact Eq.symm (hequivalent store variableValues root hstore hroot)

theorem operationsEquivalentOnData_trans (schema : Schema) {left middle right : Operation} :
    operationsEquivalentOnData schema left middle ->
      operationsEquivalentOnData schema middle right ->
        operationsEquivalentOnData schema left right := by
  intro hleft hright store variableValues root hstore hroot
  exact Eq.trans
    (hleft store variableValues root hstore hroot)
    (hright store variableValues root hstore hroot)

-- Project-specific correctness statement: normalizing an operation preserves store-backed
-- execution.
def groundNormalFormCorrect (schema : Schema)
    (operation : Operation) : Prop :=
  operationsEquivalentOnData schema operation
    (NormalForm.normalizeOperation schema operation)

theorem normalizedEquivalentOnData_of_groundNormalFormCorrect (schema : Schema)
    (operation : Operation) :
    groundNormalFormCorrect schema operation ->
      operationsEquivalentOnData schema
        (NormalForm.normalizeOperation schema operation) operation := by
  exact operationsEquivalentOnData_symm schema

end DataModel

end GraphQL
