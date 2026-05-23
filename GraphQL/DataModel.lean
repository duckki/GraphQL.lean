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

theorem executeSemanticQuery_usesStoreResolvers (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Semantic.Operation) (root : Root) :
    executeSemanticQuery schema store variableValues operation root
      = Execution.executeSemanticQuery schema store.resolvers variableValues
        operation root.toExecutionValue := by
  rfl

theorem executeOperation_usesStoreResolvers (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (root : Root) :
    executeOperation schema store variableValues operation root
      = Execution.executeQuery schema store.resolvers variableValues
        operation root.toExecutionValue := by
  rfl

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

@[simp]
theorem erase_null :
    erase .null = Execution.Response.null := by
  simp [erase]

@[simp]
theorem erase_scalar (value : String) :
    erase (.scalar value) = Execution.Response.scalar value := by
  simp [erase]

@[simp]
theorem erase_object (typeName : Name) (fields : List (Name × TypedResponse)) :
    erase (.object typeName fields) = Execution.Response.object (eraseFields fields) := by
  simp [erase]

@[simp]
theorem erase_list (values : List TypedResponse) :
    erase (.list values) = Execution.Response.list (eraseList values) := by
  simp [erase]

@[simp]
theorem eraseList_nil :
    eraseList [] = [] := by
  simp [eraseList]

@[simp]
theorem eraseList_cons (value : TypedResponse) (rest : List TypedResponse) :
    eraseList (value :: rest) = erase value :: eraseList rest := by
  simp [eraseList]

@[simp]
theorem eraseFields_nil :
    eraseFields [] = [] := by
  simp [eraseFields]

@[simp]
theorem eraseFields_cons (responseName : Name) (value : TypedResponse)
    (rest : List (Name × TypedResponse)) :
    eraseFields ((responseName, value) :: rest)
      = (responseName, erase value) :: eraseFields rest := by
  simp [eraseFields]

theorem eraseFields_append (left right : List (Name × TypedResponse)) :
    eraseFields (left ++ right) = eraseFields left ++ eraseFields right := by
  induction left with
  | nil =>
      rfl
  | cons field rest ih =>
      cases field with
      | mk responseName value =>
          simp [eraseFields, ih]

end TypedResponse

mutual
  def shallowTypedResponse : Value -> TypedResponse
    | .null => .null
    | .scalar value => .scalar value
    | .object runtimeType _id => .object runtimeType []
    | .list values => .list (shallowTypedResponses values)

  def shallowTypedResponses : List Value -> List TypedResponse
    | [] => []
    | value :: rest => shallowTypedResponse value :: shallowTypedResponses rest
end

mutual
  theorem shallowTypedResponse_erase (value : Value) :
      TypedResponse.erase (shallowTypedResponse value)
        = Execution.shallowResponse value.toExecutionValue := by
    cases value with
    | null =>
        simp [shallowTypedResponse, Execution.shallowResponse]
    | scalar value =>
        simp [shallowTypedResponse, Execution.shallowResponse]
    | object runtimeType id =>
        simp [shallowTypedResponse, Execution.shallowResponse]
    | list values =>
        simp [shallowTypedResponse, Execution.shallowResponse,
          shallowTypedResponses_erase values]

  theorem shallowTypedResponses_erase (values : List Value) :
      TypedResponse.eraseList (shallowTypedResponses values)
        = (values.map Value.toExecutionValue).map Execution.shallowResponse := by
    cases values with
    | nil =>
        simp [shallowTypedResponses]
    | cons value rest =>
        simp [shallowTypedResponses, shallowTypedResponse_erase value,
          shallowTypedResponses_erase rest]
end

namespace TypedExecution

-- Typed execution over a data model. It follows `GraphQL.Execution`, but keeps runtime
-- object type names in object responses so response-shape conditions can be interpreted.
mutual
  def completeValue (schema : Schema) (store : Store)
      (variableValues : Execution.VariableValues) :
      Nat -> Name -> List Semantic.Selection -> Value -> TypedResponse
    | 0, _parentType, _selectionSet, value =>
        shallowTypedResponse value
    | _fuel + 1, _parentType, _selectionSet, .null => .null
    | _fuel + 1, _parentType, _selectionSet, .scalar value => .scalar value
    | fuel + 1, _parentType, selectionSet, source@(.object runtimeType _id) =>
        .object runtimeType (executeSelectionSet schema store variableValues
          fuel runtimeType source selectionSet)
    | fuel + 1, parentType, selectionSet, .list values =>
        .list (values.map
          (fun value =>
            completeValue schema store variableValues
              fuel parentType selectionSet value))

  def executeSelectionSet (schema : Schema) (store : Store)
      (variableValues : Execution.VariableValues)
      (fuel : Nat) (parentType : Name) (source : Value) :
      List Semantic.Selection -> List (Name × TypedResponse)
    | selectionSet =>
        executeCollectedFields schema store variableValues fuel source
          (Execution.collectFields schema variableValues fuel parentType
            source.toExecutionValue selectionSet)

  def executeField (schema : Schema) (store : Store)
      (variableValues : Execution.VariableValues) (fuel : Nat) (source : Value)
      (responseName : Name) : List Execution.ExecutableField ->
        List (Name × TypedResponse)
    | [] => []
    | field :: fields =>
        match fuel with
        | 0 => []
        | fuel' + 1 =>
            let resolved := store.resolveValue field.fieldName field.arguments source
            let childType :=
              (schema.fieldReturnType? field.parentType field.fieldName).getD field.fieldName
            let selectionSet := Execution.mergedFieldSelectionSet (field :: fields)
            [(responseName,
              completeValue schema store variableValues
                fuel' childType selectionSet resolved)]

  def executeCollectedFields (schema : Schema) (store : Store)
      (variableValues : Execution.VariableValues) (fuel : Nat) (source : Value) :
      List (Name × List Execution.ExecutableField) -> List (Name × TypedResponse)
    | [] => []
    | (responseName, fields) :: rest =>
        executeField schema store variableValues fuel source responseName fields
          ++ executeCollectedFields schema store variableValues fuel source rest
end

def executeSemanticQuery (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Semantic.Operation) (root : Root) : TypedResponse :=
  .object root.typeName
    (executeSelectionSet schema store variableValues
      (Execution.executeSemanticQueryFuel operation) operation.rootType
      (.object root.typeName root.id) operation.selectionSet)

def executeOperation (schema : Schema) (store : Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (root : Root) : TypedResponse :=
  executeSemanticQuery schema store variableValues
    (Semantic.fromOperation operation) root

end TypedExecution

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

theorem semanticOperationsEquivalentOnData_refl (schema : Schema)
    (operation : Semantic.Operation) :
    semanticOperationsEquivalentOnData schema operation operation := by
  intro _store _variableValues _root _hstore _hroot
  rfl

theorem semanticOperationsEquivalentOnData_symm (schema : Schema)
    {left right : Semantic.Operation} :
    semanticOperationsEquivalentOnData schema left right ->
      semanticOperationsEquivalentOnData schema right left := by
  intro hequivalent store variableValues root hstore hroot
  exact Eq.symm (hequivalent store variableValues root hstore hroot)

theorem semanticOperationsEquivalentOnData_trans (schema : Schema)
    {left middle right : Semantic.Operation} :
    semanticOperationsEquivalentOnData schema left middle ->
      semanticOperationsEquivalentOnData schema middle right ->
        semanticOperationsEquivalentOnData schema left right := by
  intro hleft hright store variableValues root hstore hroot
  exact Eq.trans
    (hleft store variableValues root hstore hroot)
    (hright store variableValues root hstore hroot)

def operationsEquivalentOnData (schema : Schema) (left right : Operation) : Prop :=
  semanticOperationsEquivalentOnData schema
    (Semantic.fromOperation left) (Semantic.fromOperation right)

theorem operationsEquivalentOnData_refl (schema : Schema) (operation : Operation) :
    operationsEquivalentOnData schema operation operation := by
  exact semanticOperationsEquivalentOnData_refl schema (Semantic.fromOperation operation)

theorem operationsEquivalentOnData_symm (schema : Schema) {left right : Operation} :
    operationsEquivalentOnData schema left right ->
      operationsEquivalentOnData schema right left := by
  exact semanticOperationsEquivalentOnData_symm schema

theorem operationsEquivalentOnData_trans (schema : Schema) {left middle right : Operation} :
    operationsEquivalentOnData schema left middle ->
      operationsEquivalentOnData schema middle right ->
        operationsEquivalentOnData schema left right := by
  exact semanticOperationsEquivalentOnData_trans schema

def groundNormalFormCorrect (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  semanticOperationsEquivalentOnData schema operation
    (NormalForm.normalizeSemanticOperation schema operation)

theorem normalizedEquivalentOnData_of_groundNormalFormCorrect (schema : Schema)
    (operation : Semantic.Operation) :
    groundNormalFormCorrect schema operation ->
      semanticOperationsEquivalentOnData schema
        (NormalForm.normalizeSemanticOperation schema operation) operation := by
  exact semanticOperationsEquivalentOnData_symm schema

def responseShapeCorrectForTypedExecution (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  ∀ store variableValues root,
    store.wellTyped schema ->
      root.wellTyped schema ->
        typedResponseConformsToShapeBool variableValues (operation.size + 1)
          (TypedExecution.executeSemanticQuery schema store variableValues operation root)
          (ResponseShape.Shape.ofSemanticOperation schema operation) = true

def normalFormPreservesResponseShape (schema : Schema)
    (operation : Semantic.Operation) : Prop :=
  ResponseShape.Shape.equivalent
    (ResponseShape.Shape.ofSemanticOperation schema operation)
    (ResponseShape.Shape.ofSemanticOperation schema
      (NormalForm.normalizeSemanticOperation schema operation))

def normalFormPreservesResponseShapeBool (schema : Schema)
    (operation : Semantic.Operation) : Bool :=
  ResponseShape.Shape.equivalentBool
    (ResponseShape.Shape.ofSemanticOperation schema operation)
    (ResponseShape.Shape.ofSemanticOperation schema
      (NormalForm.normalizeSemanticOperation schema operation))

theorem normalFormPreservesResponseShapeBool_sound (schema : Schema)
    (operation : Semantic.Operation) :
    normalFormPreservesResponseShapeBool schema operation = true ->
      normalFormPreservesResponseShape schema operation := by
  intro h
  exact ResponseShape.Shape.equivalentBool_sound h

theorem normalFormPreservesResponseShapeBool_complete (schema : Schema)
    (operation : Semantic.Operation) :
    normalFormPreservesResponseShape schema operation ->
      normalFormPreservesResponseShapeBool schema operation = true := by
  intro h
  exact ResponseShape.Shape.equivalentBool_complete h

def responseShapeCorrectForTypedResponse (schema : Schema)
    (operation : Semantic.Operation)
    (variableValues : Execution.VariableValues)
    (response : TypedResponse) : Prop :=
  typedResponseConformsToShapeBool variableValues (operation.size + 1)
    response (ResponseShape.Shape.ofSemanticOperation schema operation) = true

end DataModel

end GraphQL
