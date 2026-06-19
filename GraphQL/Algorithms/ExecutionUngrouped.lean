import GraphQL.Execution
import GraphQL.NormalForm

/-!
Alternative GraphQL query execution semantics.

This module keeps the spec execution shape, but visits selections directly instead of
first constructing the complete collected-fields map. Each field visit calls the
resolver; implementations may cache that call in practice. When a later field visit
overlaps an existing response key, completion starts from the previous response slice
and merges newly visited subfields into it.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

instance : Inhabited Response := ⟨.null⟩

def lookupResponseField? (responseName : Name) :
    List (Name × Response) -> Option Response
  | [] => none
  | (fieldResponseName, response) :: rest =>
      if fieldResponseName == responseName then
        some response
      else
        lookupResponseField? responseName rest

def responseObjectField? (responseName : Name) : Response -> Option Response
  | .object fields => lookupResponseField? responseName fields
  | _ => none

mutual
  def mergeResponse (existing incoming : Response) : Response :=
    match existing, incoming with
    | .object existingFields, .object incomingFields =>
        .object (mergeResponseFields existingFields incomingFields)
    | .list existingValues, .list incomingValues =>
        .list (mergeResponseLists existingValues incomingValues)
    | _, _ => existing

  def mergeResponseFields :
      List (Name × Response) -> List (Name × Response) -> List (Name × Response)
    | existingFields, [] => existingFields
    | existingFields, (responseName, incoming) :: rest =>
        mergeResponseFields
          (mergeResponseField responseName incoming existingFields)
          rest

  def mergeResponseField (responseName : Name) (incoming : Response) :
      List (Name × Response) -> List (Name × Response)
    | [] => [(responseName, incoming)]
    | (fieldResponseName, existing) :: rest =>
        if fieldResponseName == responseName then
          (fieldResponseName, mergeResponse existing incoming) :: rest
        else
          (fieldResponseName, existing) ::
            mergeResponseField responseName incoming rest

  def mergeResponseLists : List Response -> List Response -> List Response
    | [], _incomingValues => []
    | existingValues, [] => existingValues
    | existing :: existingRest, incoming :: incomingRest =>
        mergeResponse existing incoming ::
          mergeResponseLists existingRest incomingRest
end

def mergeResponseFieldIntoObject (responseName : Name) (incoming : Response) :
    Response -> Response
  | .object fields => .object (mergeResponseField responseName incoming fields)
  | response => response

def executableField (parentType responseName fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection) :
    ExecutableField :=
  {
    parentType := parentType
    responseName := responseName
    fieldName := fieldName
    arguments := arguments
    selectionSet := selectionSet
  }

mutual
  -- Spec 6.3.1 `ExecuteRootSelectionSet`
  def executeRootSelectionSet {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectRef)
      (selectionSet: List Selection) : List (Name × Response) :=
    match
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object [])
    with
    | .object fields => fields
    | _ => []

  -- Spec 6.3.2 `CollectFields`/`executeCollectedFields`: visitor over a selection list
  -- without constructing a grouped field map.
  def visitSubfields {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectRef) :
      List Selection -> Response -> Response
    | [], output => output
    | selection :: rest, output =>
        let output' :=
          visitSelection schema resolvers variableValues depth parentType source
            selection output
        visitSubfields schema resolvers variableValues depth parentType source
          rest output'

  -- Spec 6.3.2 `CollectFields`/`executeCollectedFields` selection step: handles built-in
  -- directives and inline fragments while updating an output object directly.
  def visitSelection {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectRef) :
      Selection -> Response -> Response
    | .field responseName fieldName arguments directives selectionSet, output =>
        if selectionDirectivesAllowBool variableValues directives then
          match depth with
          | 0 => output
          | depth' + 1 =>
              let field :=
                executableField parentType responseName fieldName arguments
                  selectionSet
              let response :=
                executeField schema resolvers variableValues depth' source output
                  field
              mergeResponseFieldIntoObject responseName response output
        else
          output
    | .inlineFragment none directives selectionSet, output =>
        if !selectionDirectivesAllowBool variableValues directives then
          output
        else
          visitSubfields schema resolvers variableValues depth parentType source
            selectionSet output
    | .inlineFragment (some typeCondition) directives selectionSet, output =>
        if !selectionDirectivesAllowBool variableValues directives then
          output
        else if !doesFragmentTypeApplyBool schema parentType source typeCondition then
          output
        else
          visitSubfields schema resolvers variableValues depth parentType source
            selectionSet output

  -- Spec 6.4 `ExecuteField`: completes one field-carried subselection slice.
  -- Note: This direct visitor calls `ResolveFieldValue` on every field visit; an
  -- implementation can cache that resolver call while preserving the response-merging
  -- behavior here.
  def executeField {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (completionDepth : Nat)
      (source : Value ObjectRef) (output : Response)
      (field : ExecutableField) : Response :=
    let childType :=
      (schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName
    let previous := (responseObjectField? field.responseName output).getD .null
    let resolved :=
      resolvers.resolve field.parentType field.fieldName field.arguments source
    completeValue schema resolvers variableValues completionDepth
      childType field.selectionSet resolved previous

  -- Spec 6.4.3 `CompleteValue`: partial; ignores declared `fieldType` wrappers and result
  -- coercion/errors, using the runtime value shape instead.
  def completeValue {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) :
      Nat -> Name -> List Selection -> Value ObjectRef -> Response -> Response
    | 0, _parentType, _selectionSet, value, _previous => shallowResponse value
    | _depth + 1, _parentType, _selectionSet, .null, _previous => .null
    | _depth + 1, _parentType, _selectionSet, .scalar value, _previous => .scalar value
    | depth + 1, parentType, selectionSet, source@(.object runtimeType _ref),
        previous =>
        if schema.typeIncludesObjectBool parentType runtimeType then
          let output :=
            match previous with
            | .object _fields => previous
            | _ => .object []
          visitSubfields schema resolvers variableValues depth runtimeType source
            selectionSet output
        else
          .null
    | depth + 1, parentType, selectionSet, .list values, previous =>
        let previousValues :=
          match previous with
          | .list previousValues => previousValues
          | _ => []
        let completed :=
          values.foldl
            (fun (state : List Response × List Response) value =>
              let previous :=
                match state.snd with
                | [] => .null
                | previous :: _rest => previous
              let remainingPrevious :=
                match state.snd with
                | [] => []
                | _previous :: rest => rest
              (completeValue schema resolvers variableValues depth parentType
                selectionSet value previous :: state.fst, remainingPrevious))
            ([], previousValues)
        .list completed.fst.reverse
end

-- Compatibility wrapper of `executeRootSelectionSet` for proof modules using the older
-- name.
def executeSelectionSet {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectRef) :
    List Selection -> List (Name × Response) :=
  executeRootSelectionSet schema resolvers variableValues depth parentType source

-- Spec 6.2.1 `ExecuteQuery`
def executeQueryAtDepth {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectRef) : Response :=
  if rootSourceAppliesBool schema operation source then
    .object (executeRootSelectionSet schema resolvers variableValues
      depth operation.rootType source operation.selectionSet)
  else
    .object []

-- Spec 6.2.1 `ExecuteQuery`: Default executable query entry point using the local
-- operation-derived depth bound.
def executeQuery {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectRef) : Response :=
  executeQueryAtDepth schema resolvers variableValues operation
    (executeQueryDepthBound operation) source

-- Store-backed correctness statement for ungrouped execution. The theorem witness lives
-- in `GraphQL.Algorithms.ExecutionUngrouped.DataModel`.
def ungroupedExecutionPreservesSpecExecution
    (schema : Schema) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema ->
  Validation.operationDefinitionValid schema operation ->
    ∀ store variableValues depth,
      store.wellTyped schema ->
      NormalForm.operationBoolVarsComplete operation variableValues ->
        executeQueryAtDepth schema (store.resolvers schema) variableValues
          operation depth store.rootExecutionValue
          =
        GraphQL.DataModel.executeOperationAtDepth schema store variableValues
          operation depth

end ExecutionUngrouped
end Algorithms

end GraphQL
