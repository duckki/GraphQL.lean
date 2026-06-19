import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Response

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem executeField_empty_output
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField) :
    executeField schema resolvers variableValues depth source (.object []) field =
    completeValue schema resolvers variableValues depth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      field.selectionSet
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      .null := by
  simp [executeField, responseObjectField?, lookupResponseField?]

theorem executeField_object_fresh_eq_empty_output
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × Response))
    (hfresh : field.responseName ∉ fields.map Prod.fst) :
    executeField schema resolvers variableValues depth source (.object fields)
        field =
    executeField schema resolvers variableValues depth source (.object [])
        field := by
  have hlookup :
      lookupResponseField? field.responseName fields = none :=
    lookupResponseField?_none_of_not_mem field.responseName fields hfresh
  simp [executeField, responseObjectField?, hlookup, lookupResponseField?]

def executeField_executedResponseFieldAt
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (output : Response)
    (field : ExecutableField) :
    ExecutedResponseFieldAt schema resolvers variableValues depth source output
      field
      (executeField schema resolvers variableValues depth source output
        field) := by
  refine
    { previous :=
        (responseObjectField? field.responseName output).getD .null
      resolved :=
        resolvers.resolve field.parentType field.fieldName field.arguments source
      previous_eq := rfl
      resolved_eq := rfl
      response_eq := ?_ }
  simp [executeField]

def executeField_executedResponseFieldAt_of_lookup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × Response)) (previous : Response)
    (hlookup :
      responseObjectField? field.responseName (.object fields) =
        some previous) :
    ExecutedResponseFieldAt schema resolvers variableValues depth source
      (.object fields) field
      (executeField schema resolvers variableValues depth source
        (.object fields) field) := by
  refine
    { previous := previous
      resolved :=
        resolvers.resolve field.parentType field.fieldName field.arguments source
      previous_eq := ?_
      resolved_eq := rfl
      response_eq := ?_ }
  · simp [hlookup]
  · simp [executeField, hlookup]

def executeField_executedResponseFieldAt_after_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × Response)) (incoming : Response) :
    let output :=
      mergeResponseFieldIntoObject field.responseName incoming (.object fields)
    ExecutedResponseFieldAt schema resolvers variableValues depth source
      output field
      (executeField schema resolvers variableValues depth source output
        field) := by
  intro output
  refine
    { previous :=
        match responseObjectField? field.responseName (.object fields) with
        | some existing => mergeResponse existing incoming
        | none => incoming
      resolved :=
        resolvers.resolve field.parentType field.fieldName field.arguments source
      previous_eq := ?_
      resolved_eq := rfl
      response_eq := ?_ }
  · dsimp [output]
    rw [responseObjectField?_mergeResponseFieldIntoObject_same]
    rfl
  · simp [executeField, output,
      responseObjectField?_mergeResponseFieldIntoObject_same]
    rfl

theorem executeField_reentry_singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (previous : Response) :
    executeField schema resolvers variableValues depth source
      (.object [(field.responseName, previous)]) field =
  completeValue schema resolvers variableValues depth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      field.selectionSet
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      previous := by
  simp [executeField, responseObjectField?, lookupResponseField?]

theorem executeField_reentry_of_lookup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × Response)) (previous : Response)
    (hlookup :
      responseObjectField? field.responseName (.object fields) =
        some previous) :
    executeField schema resolvers variableValues depth source
      (.object fields) field =
    completeValue schema resolvers variableValues depth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      field.selectionSet
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      previous := by
  simp [executeField, hlookup]

theorem executeField_object_append_of_lookup_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields suffix : List (Name × Response)) (previous : Response)
    (hlookup :
      responseObjectField? field.responseName (.object fields) =
        some previous) :
    executeField schema resolvers variableValues depth source
        (.object (fields ++ suffix)) field =
      executeField schema resolvers variableValues depth source
        (.object fields) field := by
  have hlookupAppend :
      responseObjectField? field.responseName (.object (fields ++ suffix)) =
        some previous :=
    responseObjectField?_object_append_of_some_left field.responseName fields
      suffix previous hlookup
  simp [executeField, hlookup, hlookupAppend]

theorem executeField_object_append_of_mem_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields suffix : List (Name × Response))
    (hmem : field.responseName ∈ fields.map Prod.fst) :
    executeField schema resolvers variableValues depth source
        (.object (fields ++ suffix)) field =
      executeField schema resolvers variableValues depth source
        (.object fields) field := by
  rcases lookupResponseField?_some_of_mem field.responseName fields hmem with
    ⟨previous, hlookup⟩
  exact
    executeField_object_append_of_lookup_eq schema resolvers variableValues
      depth source field fields suffix previous
      (by simpa [responseObjectField?] using hlookup)

theorem executeField_reentry_after_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × Response)) (incoming : Response) :
    let output :=
      mergeResponseFieldIntoObject field.responseName incoming (.object fields)
    executeField schema resolvers variableValues depth source output field =
    completeValue schema resolvers variableValues depth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      field.selectionSet
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      (match responseObjectField? field.responseName (.object fields) with
       | some existing => mergeResponse existing incoming
       | none => incoming) := by
    intro output
    simp [executeField, output,
      responseObjectField?_mergeResponseFieldIntoObject_same]
    rfl

theorem executeField_object_reentry_absorbs_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × Response)) (previous : Response)
    (runtimeType : Name) (identity : ObjectIdentity)
    (hlookup :
      responseObjectField? field.responseName (.object fields) =
        some previous)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        .object runtimeType identity)
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true)
    (hpreviousObject :
      ∃ previousFields, previous = .object previousFields)
    (hvisitAbsorb :
      ResponseAbsorbs previous
        (visitSubfields schema resolvers variableValues depth runtimeType
          (.object runtimeType identity) field.selectionSet previous)) :
      ResponseAbsorbs previous
        (executeField schema resolvers variableValues (depth + 1) source
          (.object fields) field) := by
  rw [executeField_reentry_of_lookup schema resolvers variableValues
    (depth + 1) source field fields previous hlookup]
  rw [hresolve]
  rcases hpreviousObject with ⟨previousFields, hpreviousObject⟩
  rw [hpreviousObject] at hvisitAbsorb ⊢
  simpa [completeValue, hincludes] using hvisitAbsorb

theorem specExecuteField_group_eq_mergedFieldSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField) :
    GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
      source responseName (field :: fields) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source))] := by
  simpa [GraphQL.Execution.executeField] using
    congrArg (fun response => [(responseName, response)])
      (GraphQL.NormalForm.completeValue_eq_mergedFieldSelectionSet schema
        resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (field :: fields)
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source))

theorem specExecuteField_group_eq_mergedFieldSelectionSet_of_resolved
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved) :
    GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
      source responseName (field :: fields) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
        resolved)] := by
  rw [specExecuteField_group_eq_mergedFieldSelectionSet schema resolvers
    variableValues depth source responseName field fields, hresolve]

theorem specExecuteCollectedFields_single_group_eq_mergedFieldSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField) :
    GraphQL.Execution.executeCollectedFields schema resolvers variableValues
      (depth + 1) source [(responseName, field :: fields)] =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source))] := by
  simpa [GraphQL.Execution.executeCollectedFields] using
    specExecuteField_group_eq_mergedFieldSelectionSet schema resolvers
      variableValues depth source responseName field fields

theorem specExecuteCollectedFields_single_group_eq_mergedFieldSelectionSet_of_resolved
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved) :
    GraphQL.Execution.executeCollectedFields schema resolvers variableValues
      (depth + 1) source [(responseName, field :: fields)] =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
        resolved)] := by
  simpa [GraphQL.Execution.executeCollectedFields] using
    specExecuteField_group_eq_mergedFieldSelectionSet_of_resolved schema
      resolvers variableValues depth source responseName field fields
      resolved hresolve

theorem specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity)
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (executableFieldSelections (field :: fields)) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
        resolved)] := by
  rw [specExecuteRootSelectionSet_executableFieldSelections_same_group schema
    resolvers variableValues (depth + 1) parentType source responseName field
    fields hresponse hparent]
  exact specExecuteCollectedFields_single_group_eq_mergedFieldSelectionSet_of_resolved
    schema resolvers variableValues depth source responseName field fields
    resolved hresolve

theorem specExecuteRootSelectionSet_executableFieldSelections_collected_group_eq_merged
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity)
    (hmem :
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (executableFieldSelections (field :: fields)) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
        resolved)] := by
  apply specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
    schema resolvers variableValues depth parentType source responseName field
    fields resolved
  · exact
      (collectFields_responseName schema variableValues parentType source
        selectionSet) responseName (field :: fields) hmem
  · exact
      (collectFields_parent schema variableValues parentType source
        selectionSet) responseName (field :: fields) hmem
  · exact hresolve

theorem completeValue_null_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (previous : Response) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.null : Value ObjectIdentity) previous =
    GraphQL.Execution.completeValue schema resolvers variableValues (depth + 1)
      parentType fields (.null : Value ObjectIdentity) := by
  simp [completeValue, GraphQL.Execution.completeValue]

theorem completeValue_zero_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (value : Value ObjectIdentity) (previous : Response) :
    completeValue schema resolvers variableValues 0 parentType selectionSet
      value previous =
    GraphQL.Execution.completeValue schema resolvers variableValues 0
      parentType fields value := by
  cases value <;> simp [completeValue, GraphQL.Execution.completeValue]

theorem completeValue_scalar_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (value : String) (previous : Response) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.scalar value : Value ObjectIdentity) previous =
    GraphQL.Execution.completeValue schema resolvers variableValues (depth + 1)
      parentType fields (.scalar value : Value ObjectIdentity) := by
  simp [completeValue, GraphQL.Execution.completeValue]

theorem completeValue_object_eq_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (previous : Response) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.object runtimeType identity) previous =
    if schema.typeIncludesObjectBool parentType runtimeType then
      visitSubfields schema resolvers variableValues depth runtimeType
        (.object runtimeType identity) selectionSet
        (match previous with | .object _fields => previous | _ => .object [])
    else
      .null := by
  unfold completeValue
  rfl

theorem spec_completeValue_object_eq_executeRootSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (fields : List ExecutableField) :
    GraphQL.Execution.completeValue schema resolvers variableValues
      (depth + 1) parentType fields (.object runtimeType identity) =
    if schema.typeIncludesObjectBool parentType runtimeType then
      .object
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues depth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet fields))
    else
      .null := by
  unfold GraphQL.Execution.completeValue
  simp [GraphQL.Execution.executeRootSelectionSet]

theorem completeValue_empty_list_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (previous : Response) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.list ([] : List (Value ObjectIdentity))) previous =
    GraphQL.Execution.completeValue schema resolvers variableValues (depth + 1)
      parentType fields (.list ([] : List (Value ObjectIdentity))) := by
  unfold completeValue
  cases previous <;> simp [GraphQL.Execution.completeValue]

theorem completeValue_scalar_any_depth_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (value : String) (previous : Response) :
    completeValue schema resolvers variableValues depth parentType selectionSet
      (.scalar value : Value ObjectIdentity) previous =
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      parentType fields (.scalar value : Value ObjectIdentity) := by
  cases depth with
  | zero =>
      exact completeValue_zero_eq_spec schema resolvers variableValues
        parentType selectionSet fields (.scalar value) previous
  | succ depth =>
      exact completeValue_scalar_eq_spec schema resolvers variableValues depth
        parentType selectionSet fields value previous

theorem completeValue_scalar_any_depth_eq_scalar
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    (value : String) (previous : Response) :
    completeValue schema resolvers variableValues depth parentType selectionSet
      (.scalar value : Value ObjectIdentity) previous =
    .scalar value := by
  cases depth <;> simp [completeValue, shallowResponse]

theorem spec_completeValue_scalar_any_depth_eq_scalar
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (fields : List ExecutableField) (value : String) :
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      parentType fields (.scalar value : Value ObjectIdentity) =
    .scalar value := by
  cases depth <;> simp [GraphQL.Execution.completeValue, shallowResponse]

theorem completeValue_duplicate_scalar_merge_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (fields : List ExecutableField) (value : String) :
    mergeResponse
      (completeValue schema resolvers variableValues depth parentType
        firstSelectionSet (.scalar value : Value ObjectIdentity) .null)
      (completeValue schema resolvers variableValues depth parentType
        secondSelectionSet (.scalar value : Value ObjectIdentity)
        (completeValue schema resolvers variableValues depth parentType
          firstSelectionSet (.scalar value : Value ObjectIdentity) .null)) =
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      parentType fields (.scalar value : Value ObjectIdentity) := by
  simp [completeValue_scalar_any_depth_eq_scalar,
    spec_completeValue_scalar_any_depth_eq_scalar, mergeResponse]

theorem completeValue_duplicate_null_merge_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (fields : List ExecutableField) :
    mergeResponse
      (completeValue schema resolvers variableValues depth parentType
        firstSelectionSet (.null : Value ObjectIdentity) .null)
      (completeValue schema resolvers variableValues depth parentType
        secondSelectionSet (.null : Value ObjectIdentity)
        (completeValue schema resolvers variableValues depth parentType
          firstSelectionSet (.null : Value ObjectIdentity) .null)) =
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      parentType fields (.null : Value ObjectIdentity) := by
  cases depth <;> simp [completeValue, GraphQL.Execution.completeValue,
    shallowResponse, mergeResponse]

theorem completeValue_scalar_list_fold_fst
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    (values : List String) (acc previousValues : List Response) :
    (List.foldl
      (fun (state : List Response × List Response)
          (value : Value ObjectIdentity) =>
        (completeValue schema resolvers variableValues depth parentType
          selectionSet value
          (match state.snd with
          | [] => .null
          | previous :: _rest => previous) :: state.fst,
        match state.snd with
        | [] => []
        | _previous :: rest => rest))
      (acc, previousValues)
      (values.map (fun value => (.scalar value : Value ObjectIdentity)))).fst =
    (values.map (fun value => (.scalar value : Response))).reverse ++ acc := by
  induction values generalizing acc previousValues with
  | nil =>
      simp
  | cons value rest ih =>
      cases previousValues with
      | nil =>
          simp [completeValue_scalar_any_depth_eq_scalar,
            ih (.scalar value :: acc) [], List.append_assoc]
      | cons previous previousRest =>
          simp [completeValue_scalar_any_depth_eq_scalar,
            ih (.scalar value :: acc) previousRest, List.append_assoc]

theorem completeValue_scalar_list_fold_reverse
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    (values : List String) (previousValues : List Response) :
    (List.foldl
      (fun (state : List Response × List Response)
          (value : Value ObjectIdentity) =>
        (completeValue schema resolvers variableValues depth parentType
          selectionSet value
          (match state.snd with
          | [] => .null
          | previous :: _rest => previous) :: state.fst,
        match state.snd with
        | [] => []
        | _previous :: rest => rest))
      ([], previousValues)
      (values.map (fun value => (.scalar value : Value ObjectIdentity)))).fst.reverse =
    values.map (fun value => (.scalar value : Response)) := by
  rw [completeValue_scalar_list_fold_fst schema resolvers variableValues depth
    parentType selectionSet values [] previousValues]
  simp

theorem spec_completeValue_scalar_list_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (fields : List ExecutableField) (values : List String) :
    List.map
      ((fun value =>
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value) ∘
        fun value => (.scalar value : Value ObjectIdentity))
      values =
    values.map (fun value => (.scalar value : Response)) := by
  induction values with
  | nil =>
      simp
  | cons value rest ih =>
      simp [Function.comp_apply,
        spec_completeValue_scalar_any_depth_eq_scalar, ih]

theorem completeValue_singleton_scalar_list_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (value : String) (previous : Response) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.list [(.scalar value : Value ObjectIdentity)]) previous =
    GraphQL.Execution.completeValue schema resolvers variableValues (depth + 1)
      parentType fields (.list [(.scalar value : Value ObjectIdentity)]) := by
  unfold completeValue
  cases previous with
  | null =>
      simp [GraphQL.Execution.completeValue,
        completeValue_scalar_any_depth_eq_spec schema resolvers variableValues
          depth parentType selectionSet fields value .null]
  | scalar previousValue =>
      simp [GraphQL.Execution.completeValue,
        completeValue_scalar_any_depth_eq_spec schema resolvers variableValues
          depth parentType selectionSet fields value .null]
  | object previousFields =>
      simp [GraphQL.Execution.completeValue,
        completeValue_scalar_any_depth_eq_spec schema resolvers variableValues
          depth parentType selectionSet fields value .null]
  | list previousValues =>
      cases previousValues with
      | nil =>
          simp [GraphQL.Execution.completeValue,
            completeValue_scalar_any_depth_eq_spec schema resolvers
              variableValues depth parentType selectionSet fields value .null]
      | cons previous previousRest =>
          simp [GraphQL.Execution.completeValue,
            completeValue_scalar_any_depth_eq_spec schema resolvers
              variableValues depth parentType selectionSet fields value previous]

theorem completeValue_scalar_list_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (values : List String) (previous : Response) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.list (values.map (fun value =>
        (.scalar value : Value ObjectIdentity)))) previous =
    GraphQL.Execution.completeValue schema resolvers variableValues (depth + 1)
      parentType fields (.list (values.map (fun value =>
        (.scalar value : Value ObjectIdentity)))) := by
  cases previous with
  | null =>
      simpa [completeValue, GraphQL.Execution.completeValue,
        spec_completeValue_scalar_list_map] using
        congrArg Response.list
          (completeValue_scalar_list_fold_reverse schema resolvers
            variableValues depth parentType selectionSet values [])
  | scalar previousValue =>
      simpa [completeValue, GraphQL.Execution.completeValue,
        spec_completeValue_scalar_list_map] using
        congrArg Response.list
          (completeValue_scalar_list_fold_reverse schema resolvers
            variableValues depth parentType selectionSet values [])
  | object previousFields =>
      simpa [completeValue, GraphQL.Execution.completeValue,
        spec_completeValue_scalar_list_map] using
        congrArg Response.list
          (completeValue_scalar_list_fold_reverse schema resolvers
            variableValues depth parentType selectionSet values [])
  | list previousValues =>
      simpa [completeValue, GraphQL.Execution.completeValue,
        spec_completeValue_scalar_list_map] using
        congrArg Response.list
          (completeValue_scalar_list_fold_reverse schema resolvers
            variableValues depth parentType selectionSet values previousValues)

theorem completeValue_list_fold_empty_previous_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField) :
    ∀ (values : List (Value ObjectIdentity)) (acc : List Response),
      (∀ value, value ∈ values ->
        completeValue schema resolvers variableValues depth parentType
          selectionSet value .null =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value) ->
      (List.foldl
        (fun (state : List Response × List Response)
            (value : Value ObjectIdentity) =>
          (completeValue schema resolvers variableValues depth parentType
            selectionSet value
            (match state.snd with
            | [] => .null
            | previous :: _rest => previous) :: state.fst,
          match state.snd with
          | [] => []
          | _previous :: rest => rest))
        (acc, [])
        values).fst =
      (values.map
        (fun value =>
          GraphQL.Execution.completeValue schema resolvers variableValues depth
            parentType fields value)).reverse ++ acc
  | [], acc, _hvalues => by
      simp
  | value :: rest, acc, hvalues => by
      have hvalue :
          completeValue schema resolvers variableValues depth parentType
            selectionSet value .null =
          GraphQL.Execution.completeValue schema resolvers variableValues depth
            parentType fields value :=
        hvalues value (by simp)
      have hrest :
          ∀ restValue, restValue ∈ rest ->
            completeValue schema resolvers variableValues depth parentType
              selectionSet restValue .null =
            GraphQL.Execution.completeValue schema resolvers variableValues depth
              parentType fields restValue := by
        intro restValue hmem
        exact hvalues restValue (by simp [hmem])
      simp [hvalue,
        completeValue_list_fold_empty_previous_eq_spec schema resolvers
          variableValues depth parentType selectionSet fields rest
          (GraphQL.Execution.completeValue schema resolvers variableValues
            depth parentType fields value :: acc)
          hrest,
        List.append_assoc]

theorem completeValue_list_empty_previous_eq_spec_of_values
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (values : List (Value ObjectIdentity))
    (hvalues :
      ∀ value, value ∈ values ->
        completeValue schema resolvers variableValues depth parentType
          selectionSet value .null =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.list values) .null =
    GraphQL.Execution.completeValue schema resolvers variableValues (depth + 1)
      parentType fields (.list values) := by
  simpa [completeValue, GraphQL.Execution.completeValue] using
    congrArg List.reverse
      (completeValue_list_fold_empty_previous_eq_spec schema resolvers
        variableValues depth parentType selectionSet fields values []
        hvalues)

theorem completeValue_list_fold_empty_previous_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) :
    ∀ (values : List (Value ObjectIdentity)) (acc : List Response),
      (List.foldl
        (fun (state : List Response × List Response)
            (value : Value ObjectIdentity) =>
          (completeValue schema resolvers variableValues depth parentType
            selectionSet value
            (match state.snd with
            | [] => .null
            | previous :: _rest => previous) :: state.fst,
          match state.snd with
          | [] => []
          | _previous :: rest => rest))
        (acc, [])
        values).fst =
      (values.map
        (fun value =>
          completeValue schema resolvers variableValues depth parentType
            selectionSet value .null)).reverse ++ acc
  | [], acc => by
      simp
  | value :: rest, acc => by
      simp [completeValue_list_fold_empty_previous_eq_map schema resolvers
        variableValues depth parentType selectionSet rest
        (completeValue schema resolvers variableValues depth parentType
          selectionSet value .null :: acc), List.append_assoc]

theorem completeValue_list_empty_previous_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    (values : List (Value ObjectIdentity)) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      selectionSet (.list values) .null =
    .list
      (values.map
        (fun value =>
          completeValue schema resolvers variableValues depth parentType
            selectionSet value .null)) := by
  simpa [completeValue] using
    congrArg List.reverse
      (completeValue_list_fold_empty_previous_eq_map schema resolvers
        variableValues depth parentType selectionSet values [])

theorem completeValue_list_fold_previous_map_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection) :
    ∀ (values : List (Value ObjectIdentity)) (acc : List Response),
      (List.foldl
        (fun (state : List Response × List Response)
            (value : Value ObjectIdentity) =>
          (completeValue schema resolvers variableValues depth parentType
            secondSelectionSet value
            (match state.snd with
            | [] => .null
            | previous :: _rest => previous) :: state.fst,
          match state.snd with
          | [] => []
          | _previous :: rest => rest))
        (acc,
          values.map
            (fun value =>
              completeValue schema resolvers variableValues depth parentType
                firstSelectionSet value .null))
        values).fst =
      (values.map
        (fun value =>
          completeValue schema resolvers variableValues depth parentType
            secondSelectionSet value
            (completeValue schema resolvers variableValues depth parentType
              firstSelectionSet value .null))).reverse ++ acc
  | [], acc => by
      simp
  | value :: rest, acc => by
      simp [completeValue_list_fold_previous_map_eq_map schema resolvers
        variableValues depth parentType firstSelectionSet secondSelectionSet
        rest
        (completeValue schema resolvers variableValues depth parentType
          secondSelectionSet value
          (completeValue schema resolvers variableValues depth parentType
            firstSelectionSet value .null) :: acc), List.append_assoc]

theorem completeValue_list_previous_map_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (values : List (Value ObjectIdentity)) :
    completeValue schema resolvers variableValues (depth + 1) parentType
      secondSelectionSet (.list values)
      (.list
        (values.map
          (fun value =>
            completeValue schema resolvers variableValues depth parentType
              firstSelectionSet value .null))) =
    .list
      (values.map
        (fun value =>
          completeValue schema resolvers variableValues depth parentType
            secondSelectionSet value
            (completeValue schema resolvers variableValues depth parentType
              firstSelectionSet value .null))) := by
  simpa [completeValue] using
    congrArg List.reverse
      (completeValue_list_fold_previous_map_eq_map schema resolvers
        variableValues depth parentType firstSelectionSet secondSelectionSet
        values [])

theorem mergeResponseLists_map_of_forall
    {α : Type} (values : List α)
    (left right merged : α -> Response) :
    (∀ value, value ∈ values ->
      mergeResponse (left value) (right value) = merged value) ->
      mergeResponseLists (values.map left) (values.map right) =
        values.map merged := by
  intro hvalues
  induction values with
  | nil =>
      simp [mergeResponseLists]
  | cons value rest ih =>
      have hvalue : mergeResponse (left value) (right value) = merged value :=
        hvalues value (by simp)
      have hrest :
          ∀ restValue, restValue ∈ rest ->
            mergeResponse (left restValue) (right restValue) =
              merged restValue := by
        intro restValue hmem
        exact hvalues restValue (by simp [hmem])
      simp [mergeResponseLists, hvalue, ih hrest]

theorem completeValue_append_slices_list_of_values
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (values : List (Value ObjectIdentity))
    (hvalues :
      ∀ value, value ∈ values ->
        mergeResponse
          (completeValue schema resolvers variableValues depth parentType
            firstSelectionSet value .null)
          (completeValue schema resolvers variableValues depth parentType
            secondSelectionSet value
            (completeValue schema resolvers variableValues depth parentType
              firstSelectionSet value .null)) =
        completeValue schema resolvers variableValues depth parentType
          (firstSelectionSet ++ secondSelectionSet) value .null) :
    mergeResponse
      (completeValue schema resolvers variableValues (depth + 1) parentType
        firstSelectionSet (.list values) .null)
      (completeValue schema resolvers variableValues (depth + 1) parentType
        secondSelectionSet (.list values)
        (completeValue schema resolvers variableValues (depth + 1) parentType
          firstSelectionSet (.list values) .null)) =
    completeValue schema resolvers variableValues (depth + 1) parentType
      (firstSelectionSet ++ secondSelectionSet) (.list values) .null := by
  rw [completeValue_list_empty_previous_eq_map schema resolvers variableValues
    depth parentType firstSelectionSet values]
  rw [completeValue_list_previous_map_eq_map schema resolvers variableValues
    depth parentType firstSelectionSet secondSelectionSet values]
  rw [completeValue_list_empty_previous_eq_map schema resolvers variableValues
    depth parentType (firstSelectionSet ++ secondSelectionSet) values]
  simp [mergeResponse]
  exact mergeResponseLists_map_of_forall values
    (fun value =>
      completeValue schema resolvers variableValues depth parentType
        firstSelectionSet value .null)
    (fun value =>
      completeValue schema resolvers variableValues depth parentType
        secondSelectionSet value
        (completeValue schema resolvers variableValues depth parentType
          firstSelectionSet value .null))
    (fun value =>
      completeValue schema resolvers variableValues depth parentType
        (firstSelectionSet ++ secondSelectionSet) value .null)
    hvalues

theorem visitSelection_field_directives_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    visitSelection schema resolvers variableValues depth parentType source
      (.field responseName fieldName arguments directives selectionSet) output =
  output := by
  unfold visitSelection
  simp [hblocked]

theorem visitSelection_field_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    visitSelection schema resolvers variableValues 0 parentType source
      (.field responseName fieldName arguments directives selectionSet) output =
  output := by
  unfold visitSelection
  simp [hallowed]

theorem visitSelection_field_allowed_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    visitSelection schema resolvers variableValues (depth + 1) parentType source
      (.field responseName fieldName arguments directives selectionSet) output =
    mergeResponseFieldIntoObject responseName
      (executeField schema resolvers variableValues depth source output
        (executableField parentType responseName fieldName arguments selectionSet))
      output := by
  unfold visitSelection
  simp [hallowed]

theorem visitSelection_field_allowed_succ_fresh_eq_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst) :
    visitSelection schema resolvers variableValues (depth + 1)
      parentType source
      (.field responseName fieldName arguments directives selectionSet)
      (.object fields) =
    .object
      (fields ++
        [(responseName,
          executeField schema resolvers variableValues depth source
            (.object [])
            (executableField parentType responseName fieldName arguments
              selectionSet))]) := by
  rw [visitSelection_field_allowed_succ schema resolvers variableValues depth
    parentType source responseName fieldName arguments directives selectionSet
    (.object fields) hallowed]
  rw [executeField_object_fresh_eq_empty_output schema resolvers variableValues
    depth source
    (executableField parentType responseName fieldName arguments selectionSet)
    fields hfresh]
  simp [mergeResponseFieldIntoObject,
    mergeResponseField_of_not_mem responseName
      (executeField schema resolvers variableValues depth source (.object [])
        (executableField parentType responseName fieldName arguments
          selectionSet))
      fields hfresh]

theorem visitSubfields_single_field_allowed_succ_fresh_eq_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst) :
    visitSubfields schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (.object fields) =
    .object
      (fields ++
        [(responseName,
          executeField schema resolvers variableValues depth source
            (.object [])
            (executableField parentType responseName fieldName arguments
              selectionSet))]) := by
  simpa [visitSubfields] using
    visitSelection_field_allowed_succ_fresh_eq_append schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfresh

theorem visitSubfields_executableFieldSelections_singleton_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) :
    visitSubfields schema resolvers variableValues (depth + 1) parentType
      source (executableFieldSelections [field]) (.object []) =
    .object
      [(field.responseName,
        executeField schema resolvers variableValues depth source (.object [])
          (executableField parentType field.responseName field.fieldName
            field.arguments field.selectionSet))] := by
  simpa [executableFieldSelections, executableFieldSelection] using
    visitSubfields_single_field_allowed_succ_fresh_eq_append schema resolvers
      variableValues depth parentType source field.responseName field.fieldName
      field.arguments [] field.selectionSet [] rfl (by simp)

theorem executeRootSelectionSet_single_field_allowed_succ_eq_executeField_empty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    [(responseName,
      executeField schema resolvers variableValues depth source (.object [])
        (executableField parentType responseName fieldName arguments
          selectionSet))] := by
  unfold executeRootSelectionSet
  rw [visitSubfields_single_field_allowed_succ_fresh_eq_append schema
    resolvers variableValues depth parentType source responseName fieldName
    arguments directives selectionSet [] hallowed (by simp)]
  simp

theorem visitSubfields_single_field_allowed_succ_fresh_appends_executeRootSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst) :
    visitSubfields schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (.object fields) =
    .object
      (fields ++
        executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]) := by
  rw [visitSubfields_single_field_allowed_succ_fresh_eq_append schema resolvers
    variableValues depth parentType source responseName fieldName arguments
    directives selectionSet fields hallowed hfresh]
  rw [executeRootSelectionSet_single_field_allowed_succ_eq_executeField_empty
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed]

theorem visitSelection_field_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response) :
    visitSelection schema resolvers variableValues depth parentType source
      (.field responseName fieldName arguments directives selectionSet) output =
    visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source
            (.field responseName fieldName arguments directives selectionSet))))
      output := by
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · cases depth with
    | zero =>
        rw [visitSelection_field_depth_zero schema resolvers variableValues
          parentType source responseName fieldName arguments directives
          selectionSet output hallowed]
        simp [visitSubfields, GraphQL.Execution.collectSelection,
          collectedExecutableFields, executableFieldSelections,
          executableFieldSelection, hallowed]
        rw [visitSelection_field_depth_zero schema resolvers variableValues
          parentType source responseName fieldName arguments [] selectionSet
          output (selectionDirectivesAllowBool_empty variableValues)]
    | succ depth =>
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          depth parentType source responseName fieldName arguments directives
          selectionSet output hallowed]
        simp [visitSubfields, visitSelection, executeField,
          GraphQL.Execution.collectSelection, collectedExecutableFields,
          executableFieldSelections, executableFieldSelection, executableField,
          selectionDirectivesAllowBool_empty, hallowed]
  · have hfalse :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hmatch : selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rw [visitSelection_field_directives_blocked schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet output hfalse]
    simp [visitSubfields, GraphQL.Execution.collectSelection,
      collectedExecutableFields, executableFieldSelections, hfalse]

theorem visitSelection_field_allowed_succ_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ResponseMergeReady (.object fields) ->
    ResponseMergeReady
      (executeField schema resolvers variableValues depth source
        (.object fields)
        (executableField parentType responseName fieldName arguments
          selectionSet)) ->
      ResponseMergeReady
        (visitSelection schema resolvers variableValues (depth + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet)
          (.object fields)) := by
  intro hfieldsReady hfieldReady
  rw [visitSelection_field_allowed_succ schema resolvers variableValues depth
    parentType source responseName fieldName arguments directives selectionSet
    (.object fields) hallowed]
  simpa [mergeResponseFieldIntoObject] using
    mergeResponseField_object_ready_of_ready responseName
      (executeField schema resolvers variableValues depth source
        (.object fields)
        (executableField parentType responseName fieldName arguments
          selectionSet))
      fields hfieldsReady hfieldReady

theorem visitSelection_field_allowed_succ_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ResponseMergeReady (.object fields) ->
    (∀ existing,
      (responseName, existing) ∈ fields ->
        ResponseAbsorbs existing
          (mergeResponse existing
            (executeField schema resolvers variableValues depth source
              (.object fields)
              (executableField parentType responseName fieldName arguments
                selectionSet)))) ->
      ResponseAbsorbs (.object fields)
        (visitSelection schema resolvers variableValues (depth + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet)
          (.object fields)) := by
  intro hfieldsReady hcollisionAbsorbs
  rw [visitSelection_field_allowed_succ schema resolvers variableValues depth
    parentType source responseName fieldName arguments directives selectionSet
    (.object fields) hallowed]
  simpa [mergeResponseFieldIntoObject] using
    mergeResponseField_object_absorbs responseName
      (executeField schema resolvers variableValues depth source
        (.object fields)
        (executableField parentType responseName fieldName arguments
          selectionSet))
      fields hfieldsReady hcollisionAbsorbs

theorem visitSelection_field_allowed_succ_absorbs_of_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst) :
    ResponseMergeReady (.object fields) ->
      ResponseAbsorbs (.object fields)
        (visitSelection schema resolvers variableValues (depth + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet)
          (.object fields)) := by
  intro hfieldsReady
  apply visitSelection_field_allowed_succ_absorbs schema resolvers
    variableValues depth parentType source responseName fieldName arguments
    directives selectionSet fields hallowed hfieldsReady
  intro existing hmem
  exact False.elim (hfresh (by
    simpa [List.mem_map] using ⟨existing, hmem⟩))

theorem visitSubfields_single_field_allowed_succ_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ResponseMergeReady (.object fields) ->
    (∀ existing,
      (responseName, existing) ∈ fields ->
        ResponseAbsorbs existing
          (mergeResponse existing
            (executeField schema resolvers variableValues depth source
              (.object fields)
              (executableField parentType responseName fieldName arguments
                selectionSet)))) ->
      ResponseAbsorbs (.object fields)
        (visitSubfields schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]
          (.object fields)) := by
  intro hfieldsReady hcollisionAbsorbs
  simpa [visitSubfields] using
    visitSelection_field_allowed_succ_absorbs schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet fields hallowed hfieldsReady hcollisionAbsorbs

theorem visitSubfields_single_field_allowed_succ_absorbs_of_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst) :
    ResponseMergeReady (.object fields) ->
      ResponseAbsorbs (.object fields)
        (visitSubfields schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]
          (.object fields)) := by
  intro hfieldsReady
  simpa [visitSubfields] using
    visitSelection_field_allowed_succ_absorbs_of_fresh schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfresh hfieldsReady

theorem visitSelection_inline_none_directives_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    visitSelection schema resolvers variableValues depth parentType source
      (.inlineFragment none directives selectionSet) output =
  output := by
  unfold visitSelection
  simp [hblocked]

theorem visitSelection_inline_some_directives_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    visitSelection schema resolvers variableValues depth parentType source
      (.inlineFragment (some typeCondition) directives selectionSet) output =
  output := by
  unfold visitSelection
  simp [hblocked]

theorem visitSelection_inline_some_type_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition = false) :
    visitSelection schema resolvers variableValues depth parentType source
      (.inlineFragment (some typeCondition) directives selectionSet) output =
  output := by
  unfold visitSelection
  simp [hallowed, hnotApply]

theorem visitSelection_inline_none_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hbody :
      selectionDirectivesAllowBool variableValues directives = true ->
        visitSubfields schema resolvers variableValues depth parentType source
          selectionSet output =
        visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet)))
          output) :
    visitSelection schema resolvers variableValues depth parentType source
      (.inlineFragment none directives selectionSet) output =
    visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source (.inlineFragment none directives selectionSet))))
      output := by
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · simp [visitSelection, GraphQL.Execution.collectSelection, hallowed]
    exact hbody hallowed
  · have hfalse :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hmatch : selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rw [visitSelection_inline_none_directives_blocked schema resolvers
      variableValues depth parentType source directives selectionSet output
      hfalse]
    simp [visitSubfields, GraphQL.Execution.collectSelection,
      collectedExecutableFields, executableFieldSelections, hfalse]

theorem visitSelection_inline_some_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hbody :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
        visitSubfields schema resolvers variableValues depth parentType source
          selectionSet output =
        visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet)))
          output) :
    visitSelection schema resolvers variableValues depth parentType source
      (.inlineFragment (some typeCondition) directives selectionSet) output =
    visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source
            (.inlineFragment (some typeCondition) directives selectionSet))))
      output := by
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · simp [visitSelection, GraphQL.Execution.collectSelection, hallowed,
        happly]
      exact hbody hallowed happly
    · have hfalse :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases hmatch :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      rw [visitSelection_inline_some_type_not_apply schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet output hallowed hfalse]
      simp [visitSubfields, GraphQL.Execution.collectSelection,
        collectedExecutableFields, executableFieldSelections, hallowed, hfalse]
  · have hfalse :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hmatch : selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rw [visitSelection_inline_some_directives_blocked schema resolvers
      variableValues depth parentType source typeCondition directives
      selectionSet output hfalse]
    simp [visitSubfields, GraphQL.Execution.collectSelection,
      collectedExecutableFields, executableFieldSelections, hfalse]

theorem visitSelection_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selection : Selection) (output : Response)
    (hbody :
      match selection with
      | .field _responseName _fieldName _arguments _directives
          _selectionSet =>
          True
      | .inlineFragment none directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
            visitSubfields schema resolvers variableValues depth parentType
              source selectionSet output =
            visitSubfields schema resolvers variableValues depth parentType
              source
              (executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source selectionSet)))
              output
      | .inlineFragment (some typeCondition) directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            true ->
            visitSubfields schema resolvers variableValues depth parentType
              source selectionSet output =
            visitSubfields schema resolvers variableValues depth parentType
              source
              (executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source selectionSet)))
              output) :
    visitSelection schema resolvers variableValues depth parentType source
      selection output =
    visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)))
      output := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      exact
        visitSelection_field_eq_visitSubfields_collectedExecutableFields_collectSelection
          schema resolvers variableValues depth parentType source responseName
          fieldName arguments directives selectionSet output
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          exact
            visitSelection_inline_none_eq_visitSubfields_collectedExecutableFields_collectSelection
              schema resolvers variableValues depth parentType source directives
              selectionSet output hbody
      | some typeCondition =>
          exact
            visitSelection_inline_some_eq_visitSubfields_collectedExecutableFields_collectSelection
              schema resolvers variableValues depth parentType source
              typeCondition directives selectionSet output hbody

theorem visitSubfields_single_eq_flattened_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selection : Selection) (output : Response)
    (hbody :
      match selection with
      | .field _responseName _fieldName _arguments _directives
          _selectionSet =>
          True
      | .inlineFragment none directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
            visitSubfields schema resolvers variableValues depth parentType
              source selectionSet output =
            visitSubfields schema resolvers variableValues depth parentType
              source
              (executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source selectionSet)))
              output
      | .inlineFragment (some typeCondition) directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            true ->
            visitSubfields schema resolvers variableValues depth parentType
              source selectionSet output =
            visitSubfields schema resolvers variableValues depth parentType
              source
              (executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source selectionSet)))
              output) :
    visitSubfields schema resolvers variableValues depth parentType source
      [selection] output =
    visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source [selection])))
      output := by
  rw [show
      GraphQL.Execution.collectFields schema variableValues parentType source
          [selection] =
        GraphQL.Execution.collectSelection schema variableValues parentType
          source selection by
    simp [GraphQL.Execution.collectFields,
      GraphQL.Execution.mergeExecutableGroups]]
  simp [visitSubfields]
  exact
    visitSelection_eq_visitSubfields_collectedExecutableFields_collectSelection
      schema resolvers variableValues depth parentType source selection output
      hbody

theorem visitSubfields_nil_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (output : Response) :
    ResponseMergeReady output ->
      ResponseAbsorbs output
        (visitSubfields schema resolvers variableValues depth parentType source
          [] output) := by
  intro hready
  simpa [visitSubfields] using ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_field_blocked_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
      ResponseAbsorbs output
        (visitSelection schema resolvers variableValues depth parentType source
          (.field responseName fieldName arguments directives selectionSet)
          output) := by
  intro hready
  rw [visitSelection_field_directives_blocked schema resolvers variableValues
    depth parentType source responseName fieldName arguments directives
    selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_field_depth_zero_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ResponseMergeReady output ->
      ResponseAbsorbs output
        (visitSelection schema resolvers variableValues 0 parentType source
          (.field responseName fieldName arguments directives selectionSet)
          output) := by
  intro hready
  rw [visitSelection_field_depth_zero schema resolvers variableValues
    parentType source responseName fieldName arguments directives selectionSet
    output hallowed]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_inline_none_blocked_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
      ResponseAbsorbs output
        (visitSelection schema resolvers variableValues depth parentType source
          (.inlineFragment none directives selectionSet) output) := by
  intro hready
  rw [visitSelection_inline_none_directives_blocked schema resolvers
    variableValues depth parentType source directives selectionSet output
    hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_inline_some_blocked_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
      ResponseAbsorbs output
        (visitSelection schema resolvers variableValues depth parentType source
          (.inlineFragment (some typeCondition) directives selectionSet)
          output) := by
  intro hready
  rw [visitSelection_inline_some_directives_blocked schema resolvers
    variableValues depth parentType source typeCondition directives
    selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_inline_some_not_apply_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition = false) :
    ResponseMergeReady output ->
      ResponseAbsorbs output
        (visitSelection schema resolvers variableValues depth parentType source
          (.inlineFragment (some typeCondition) directives selectionSet)
          output) := by
  intro hready
  rw [visitSelection_inline_some_type_not_apply schema resolvers variableValues
    depth parentType source typeCondition directives selectionSet output
    hallowed hnotApply]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSubfields_append_equivalence
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
    ∀ (left right : List Selection) (output : Response),
      visitSubfields schema resolvers variableValues depth parentType source
        (left ++ right) output =
      visitSubfields schema resolvers variableValues depth parentType source
        right
        (visitSubfields schema resolvers variableValues depth parentType source
          left output)
  | [], _right, _output => by
      simp [visitSubfields]
  | _selection :: rest, right, output => by
      simp [visitSubfields,
        visitSubfields_append_equivalence schema resolvers variableValues depth parentType
          source rest right]

theorem visitSubfields_append_eq_flattened_collectFields_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left right : List Selection) (output : Response)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right))
    (hleft :
      visitSubfields schema resolvers variableValues depth parentType source
        left output =
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left)))
        output)
    (hright :
      visitSubfields schema resolvers variableValues depth parentType source
        right
        (visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source left)))
          output) =
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source right)))
        (visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source left)))
          output)) :
    visitSubfields schema resolvers variableValues depth parentType source
      (left ++ right) output =
    visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (left ++ right))))
      output := by
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth parentType
    source left right output]
  rw [hleft]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [collectedExecutableFields_mergeExecutableGroups_eq_append_of_namesDisjoint]
  · rw [show
        executableFieldSelections
            (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source left) ++
              collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source right)) =
          executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source left)) ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source right)) by
      simp [executableFieldSelections]]
    rw [visitSubfields_append_equivalence schema resolvers variableValues depth parentType
      source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source left)))
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source right)))
      output]
    exact hright
  · exact hdisjoint
  · exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source right

def VisitSubfieldsFlatCollects
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (output : Response) : Prop :=
  visitSubfields schema resolvers variableValues depth parentType source
    selectionSet output =
  visitSubfields schema resolvers variableValues depth parentType source
    (executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)))
    output

def VisitSubfieldsFlatCollectsAllOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) : Prop :=
  ∀ output,
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source selectionSet output

theorem VisitSubfieldsFlatCollects_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) (output : Response) :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source [] output := by
  simp [VisitSubfieldsFlatCollects, visitSubfields, GraphQL.Execution.collectFields,
    collectedExecutableFields, executableFieldSelections]

theorem VisitSubfieldsFlatCollectsAllOutputs_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
      parentType source [] := by
  intro output
  exact VisitSubfieldsFlatCollects_nil schema resolvers variableValues depth
    parentType source output

theorem VisitSubfieldsFlatCollects_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selection : Selection) (output : Response)
    (hbody :
      match selection with
      | .field _responseName _fieldName _arguments _directives
          _selectionSet =>
          True
      | .inlineFragment none directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
            VisitSubfieldsFlatCollects schema resolvers variableValues depth
              parentType source selectionSet output
      | .inlineFragment (some typeCondition) directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            true ->
            VisitSubfieldsFlatCollects schema resolvers variableValues depth
              parentType source selectionSet output) :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source [selection] output := by
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  exact visitSubfields_single_eq_flattened_collectFields schema resolvers
    variableValues depth parentType source selection output hbody

theorem VisitSubfieldsFlatCollectsAllOutputs_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selection : Selection)
    (hbody :
      match selection with
      | .field _responseName _fieldName _arguments _directives
          _selectionSet =>
          True
      | .inlineFragment none directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
            VisitSubfieldsFlatCollectsAllOutputs schema resolvers
              variableValues depth parentType source selectionSet
      | .inlineFragment (some typeCondition) directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            true ->
            VisitSubfieldsFlatCollectsAllOutputs schema resolvers
              variableValues depth parentType source selectionSet) :
    VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
      parentType source [selection] := by
  intro output
  apply VisitSubfieldsFlatCollects_single schema resolvers variableValues depth
    parentType source selection output
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      exact trivial
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          intro hallowed
          exact hbody hallowed output
      | some typeCondition =>
          intro hallowed happly
          exact hbody hallowed happly output

theorem VisitSubfieldsFlatCollects_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left right : List Selection) (output : Response)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right))
    (hleft :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source left output)
    (hright :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source right
        (visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source left)))
          output)) :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source (left ++ right) output := by
  unfold VisitSubfieldsFlatCollects at hleft hright ⊢
  exact visitSubfields_append_eq_flattened_collectFields_of_namesDisjoint
    schema resolvers variableValues depth parentType source left right output
    hdisjoint hleft hright

theorem VisitSubfieldsFlatCollectsAllOutputs_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left right : List Selection)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right))
    (hleft :
      VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
        parentType source left)
    (hright :
      VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
        parentType source right) :
    VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
      parentType source (left ++ right) := by
  intro output
  apply VisitSubfieldsFlatCollects_append_of_namesDisjoint schema resolvers
    variableValues depth parentType source left right output hdisjoint
  · exact hleft output
  · exact hright
      (visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left)))
        output)

theorem VisitSubfieldsFlatCollects_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (fields : List ExecutableField)
    (output : Response)
    (hresponse :
      ∀ field, field ∈ fields -> field.responseName = responseName)
    (hparent :
      ∀ field, field ∈ fields -> field.parentType = parentType) :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source (executableFieldSelections fields) output := by
  unfold VisitSubfieldsFlatCollects
  rw [collectFields_executableFieldSelections_same_group schema variableValues
    parentType source responseName fields hresponse hparent]
  cases fields <;> simp [collectedExecutableFields]

theorem VisitSubfieldsFlatCollects_executableFieldSelections_collectedExecutableFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (output : Response)
    (hnodup : PairKeysNodup groups)
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponse : CollectedGroupsResponseName groups)
    (hparent : CollectedGroupsParent parentType groups) :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source (executableFieldSelections (collectedExecutableFields groups))
      output := by
  unfold VisitSubfieldsFlatCollects
  rw [collectFields_executableFieldSelections_collectedExecutableFields schema
    variableValues parentType source groups hnodup hnonempty hresponse hparent]

theorem VisitSubfieldsFlatCollects_executableFieldSelections_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (output : Response) :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet)))
      output := by
  unfold VisitSubfieldsFlatCollects
  rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]

mutual
  theorem visitSelection_responseObjectField?_of_not_mem_collectSelection
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : Value ObjectIdentity)
      (responseName : Name) :
      ∀ (selection : Selection) (output : Response),
        responseName ∉
            (GraphQL.Execution.collectSelection schema variableValues
              parentType source selection).map Prod.fst ->
          responseObjectField? responseName
            (visitSelection schema resolvers variableValues depth parentType
              source selection output) =
          responseObjectField? responseName output
    | .field fieldResponseName fieldName arguments directives selectionSet,
        output => by
        intro hnot
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · have hne : responseName ≠ fieldResponseName := by
            intro heq
            exact hnot (by
              simp [GraphQL.Execution.collectSelection, hallowed, heq])
          cases depth with
          | zero =>
              simp [visitSelection, hallowed]
          | succ completionDepth =>
              cases output with
              | object fields =>
                  simpa [visitSelection, hallowed, executableField] using
                    responseObjectField?_mergeResponseFieldIntoObject_other
                      responseName fieldResponseName
                      (executeField schema resolvers variableValues
                        completionDepth source (.object fields)
                        (executableField parentType fieldResponseName fieldName
                          arguments selectionSet))
                      fields hne
              | null =>
                  simp [visitSelection, hallowed, mergeResponseFieldIntoObject]
              | scalar value =>
                  simp [visitSelection, hallowed, mergeResponseFieldIntoObject]
              | list values =>
                  simp [visitSelection, hallowed, mergeResponseFieldIntoObject]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives <;>
              simp [h] at hallowed ⊢
          cases depth <;> simp [visitSelection, hblocked]
    | .inlineFragment none directives selectionSet, output => by
        intro hnot
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · have hsubfields :
              responseName ∉
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source selectionSet).map Prod.fst := by
            simpa [GraphQL.Execution.collectSelection, hallowed] using hnot
          simpa [visitSelection, hallowed] using
            visitSubfields_responseObjectField?_of_not_mem_collectFields
              schema resolvers variableValues depth parentType source
              responseName selectionSet output hsubfields
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives <;>
              simp [h] at hallowed ⊢
          simp [visitSelection, hblocked]
    | .inlineFragment (some typeCondition) directives selectionSet, output => by
        intro hnot
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · by_cases happly :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                true
          · have hsubfields :
                responseName ∉
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source selectionSet).map Prod.fst := by
              simpa [GraphQL.Execution.collectSelection, hallowed, happly]
                using hnot
            simpa [visitSelection, hallowed, happly] using
              visitSubfields_responseObjectField?_of_not_mem_collectFields
                schema resolvers variableValues depth parentType source
                responseName selectionSet output hsubfields
          · have hnotApply :
                doesFragmentTypeApplyBool schema parentType source
                    typeCondition =
                  false := by
              cases h :
                doesFragmentTypeApplyBool schema parentType source
                  typeCondition <;>
                simp [h] at happly ⊢
            simp [visitSelection, hallowed, hnotApply]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives <;>
              simp [h] at hallowed ⊢
          simp [visitSelection, hblocked]

  theorem visitSubfields_responseObjectField?_of_not_mem_collectFields
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : Value ObjectIdentity)
      (responseName : Name) :
      ∀ (selectionSet : List Selection) (output : Response),
        responseName ∉
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet).map Prod.fst ->
          responseObjectField? responseName
            (visitSubfields schema resolvers variableValues depth parentType
              source selectionSet output) =
          responseObjectField? responseName output
    | [], output => by
        intro _hnot
        simp [visitSubfields]
    | selection :: rest, output => by
        intro hnot
        have hselectionNot :
            responseName ∉
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection).map Prod.fst := by
          intro hmem
          exact hnot
            ((mergeExecutableGroups_key_mem
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest) responseName).mpr (Or.inl hmem))
        have hrestNot :
            responseName ∉
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest).map Prod.fst := by
          intro hmem
          exact hnot
            ((mergeExecutableGroups_key_mem
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest) responseName).mpr (Or.inr hmem))
        simp [visitSubfields]
        rw [visitSubfields_responseObjectField?_of_not_mem_collectFields
          schema resolvers variableValues depth parentType source responseName
          rest
          (visitSelection schema resolvers variableValues depth parentType
            source selection output)
          hrestNot]
        exact
          visitSelection_responseObjectField?_of_not_mem_collectSelection
            schema resolvers variableValues depth parentType source responseName
            selection output hselectionNot
end

theorem mergeResponseFieldIntoObject_commutes_with_appended_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (incoming : Response)
    (fields suffix : List (Name × Response))
    (hpresent : responseName ∈ fields.map Prod.fst)
    (hbase :
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object fields) =
      .object (fields ++ suffix))
    (hmerged :
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet
        (mergeResponseFieldIntoObject responseName incoming (.object fields)) =
      .object (mergeResponseField responseName incoming fields ++ suffix)) :
    mergeResponseFieldIntoObject responseName incoming
        (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object fields)) =
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet
        (mergeResponseFieldIntoObject responseName incoming (.object fields)) := by
  rw [hbase, hmerged]
  simp [mergeResponseFieldIntoObject,
    mergeResponseField_append_of_mem_left responseName incoming fields suffix
      hpresent]

theorem visitSubfields_duplicate_field_commutes_across_appended_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (fields suffix : List (Name × Response))
    (hsameResponse : later.responseName = first.responseName)
    (hfirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first]) (.object []) =
      .object fields)
    (hpresent : first.responseName ∈ fields.map Prod.fst)
    (hlaterStable :
      executeField schema resolvers variableValues completionDepth source
        (.object (fields ++ suffix))
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet) =
      executeField schema resolvers variableValues completionDepth source
        (.object fields)
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet))
    (hmiddleBase :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object fields) =
      .object (fields ++ suffix))
    (hmiddleMerged :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields)) =
      .object
        (mergeResponseField first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          fields ++ suffix)) :
    visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) (.object []) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first, later] ++ middle) (.object []) := by
  have hfirstSelection :
      visitSelection schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelection first) (.object []) =
      .object fields := by
    simpa [executableFieldSelections, executableFieldSelection, visitSubfields]
      using hfirst
  have hfirstSelection' :
      visitSelection schema resolvers variableValues (completionDepth + 1)
        parentType source
        (.field first.responseName first.fieldName first.arguments []
          first.selectionSet) (.object []) =
      .object fields := by
    simpa [executableFieldSelection] using hfirstSelection
  simp [executableFieldSelections, executableFieldSelection, visitSubfields]
  rw [hfirstSelection']
  rw [visitSubfields_append_equivalence]
  rw [hmiddleBase]
  have hlaterStable' :
      executeField schema resolvers variableValues completionDepth source
        (.object (fields ++ suffix))
        (executableField parentType first.responseName later.fieldName
          later.arguments later.selectionSet) =
      executeField schema resolvers variableValues completionDepth source
        (.object fields)
        (executableField parentType first.responseName later.fieldName
          later.arguments later.selectionSet) := by
    simpa [hsameResponse] using hlaterStable
  have hlaterStable'' :
      executeField schema resolvers variableValues completionDepth source
        (.object (fields ++ suffix))
        { parentType := parentType
          responseName := first.responseName
          fieldName := later.fieldName
          arguments := later.arguments
          selectionSet := later.selectionSet } =
      executeField schema resolvers variableValues completionDepth source
        (.object fields)
        { parentType := parentType
          responseName := first.responseName
          fieldName := later.fieldName
          arguments := later.arguments
          selectionSet := later.selectionSet } := by
    simpa [executableField] using hlaterStable'
  have hmiddleMerged' :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            { parentType := parentType
              responseName := first.responseName
              fieldName := later.fieldName
              arguments := later.arguments
              selectionSet := later.selectionSet })
          (.object fields)) =
      .object
        (mergeResponseField first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            { parentType := parentType
              responseName := first.responseName
              fieldName := later.fieldName
              arguments := later.arguments
              selectionSet := later.selectionSet })
          fields ++ suffix) := by
    simpa [hsameResponse, executableField] using hmiddleMerged
  simp [visitSubfields, visitSelection, executableField,
    selectionDirectivesAllowBool_empty, hsameResponse]
  rw [hlaterStable'']
  simp [mergeResponseFieldIntoObject,
    mergeResponseField_append_of_mem_left first.responseName
      (executeField schema resolvers variableValues completionDepth source
        (.object fields)
        { parentType := parentType
          responseName := first.responseName
          fieldName := later.fieldName
          arguments := later.arguments
          selectionSet := later.selectionSet })
      fields suffix hpresent]
  exact hmiddleMerged'.symm

theorem visitSubfields_duplicate_field_commutes_across_appended_middle_of_present
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (fields suffix : List (Name × Response))
    (hsameResponse : later.responseName = first.responseName)
    (hfirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first]) (.object []) =
      .object fields)
    (hpresent : first.responseName ∈ fields.map Prod.fst)
    (hmiddleBase :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object fields) =
      .object (fields ++ suffix))
    (hmiddleMerged :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields)) =
      .object
        (mergeResponseField first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          fields ++ suffix)) :
    visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) (.object []) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first, later] ++ middle) (.object []) := by
  apply visitSubfields_duplicate_field_commutes_across_appended_middle schema
    resolvers variableValues completionDepth parentType source first later
    middle fields suffix hsameResponse hfirst hpresent
  · have hpresentLater :
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet).responseName ∈ fields.map
          Prod.fst := by
      simpa [executableField, hsameResponse] using hpresent
    exact
      executeField_object_append_of_mem_eq schema resolvers variableValues
        completionDepth source
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet)
        fields suffix hpresentLater
  · exact hmiddleBase
  · exact hmiddleMerged

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_appended
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (fields suffix : List (Name × Response))
    (hsameResponse : later.responseName = first.responseName)
    (hfirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first]) (.object []) =
      .object fields)
    (hpresent : first.responseName ∈ fields.map Prod.fst)
    (hlaterStable :
      executeField schema resolvers variableValues completionDepth source
        (.object (fields ++ suffix))
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet) =
      executeField schema resolvers variableValues completionDepth source
        (.object fields)
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet))
    (hmiddleBase :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object fields) =
      .object (fields ++ suffix))
    (hmiddleMerged :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields)) =
      .object
        (mergeResponseField first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          fields ++ suffix))
    (hmiddleFlat :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields)))
    (hflatten :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections [first] ++ middle ++
                executableFieldSelections [later]))) =
        executableFieldSelections [first, later] ++
          executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle))) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  unfold VisitSubfieldsFlatCollects at hmiddleFlat ⊢
  rw [hflatten]
  rw [visitSubfields_duplicate_field_commutes_across_appended_middle schema
    resolvers variableValues completionDepth parentType source first later
    middle fields suffix hsameResponse hfirst hpresent hlaterStable hmiddleBase
    hmiddleMerged]
  have hfirstSelection :
      visitSelection schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelection first) (.object []) =
      .object fields := by
    simpa [executableFieldSelections, executableFieldSelection, visitSubfields]
      using hfirst
  have hfirstSelection' :
      visitSelection schema resolvers variableValues (completionDepth + 1)
        parentType source
        (.field first.responseName first.fieldName first.arguments []
          first.selectionSet) (.object []) =
      .object fields := by
    simpa [executableFieldSelection] using hfirstSelection
  simp [executableFieldSelections, executableFieldSelection, visitSubfields]
  rw [hfirstSelection']
  simp [visitSelection, executableField, selectionDirectivesAllowBool_empty,
    hsameResponse]
  simpa [hsameResponse, executableField] using hmiddleFlat

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_appended_disjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (fields suffix : List (Name × Response))
    (hsameResponse : later.responseName = first.responseName)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hfirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first]) (.object []) =
      .object fields)
    (hpresent : first.responseName ∈ fields.map Prod.fst)
    (hlaterStable :
      executeField schema resolvers variableValues completionDepth source
        (.object (fields ++ suffix))
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet) =
      executeField schema resolvers variableValues completionDepth source
        (.object fields)
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet))
    (hmiddleBase :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object fields) =
      .object (fields ++ suffix))
    (hmiddleMerged :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields)) =
      .object
        (mergeResponseField first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          fields ++ suffix))
    (hmiddleFlat :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields))) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  exact
    VisitSubfieldsFlatCollects_duplicate_field_middle_of_appended schema
      resolvers variableValues completionDepth parentType source first later
      middle fields suffix hsameResponse hfirst hpresent hlaterStable
      hmiddleBase hmiddleMerged hmiddleFlat
      (executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source first later middle
        hsameResponse hnotMiddle)

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_appended_disjoint_of_present
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (fields suffix : List (Name × Response))
    (hsameResponse : later.responseName = first.responseName)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hfirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first]) (.object []) =
      .object fields)
    (hpresent : first.responseName ∈ fields.map Prod.fst)
    (hmiddleBase :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object fields) =
      .object (fields ++ suffix))
    (hmiddleMerged :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields)) =
      .object
        (mergeResponseField first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          fields ++ suffix))
    (hmiddleFlat :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source middle
        (mergeResponseFieldIntoObject first.responseName
          (executeField schema resolvers variableValues completionDepth source
            (.object fields)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
          (.object fields))) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  exact
    VisitSubfieldsFlatCollects_duplicate_field_middle_of_appended_disjoint
      schema resolvers variableValues completionDepth parentType source first
      later middle fields suffix hsameResponse hnotMiddle hfirst hpresent
      (by
        have hpresentLater :
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet).responseName ∈ fields.map
              Prod.fst := by
          simpa [executableField, hsameResponse] using hpresent
        exact
          executeField_object_append_of_mem_eq schema resolvers variableValues
            completionDepth source
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet)
            fields suffix hpresentLater)
      hmiddleBase hmiddleMerged hmiddleFlat

theorem executeRootSelectionSet_eq_spec_of_flatCollects_and_flattened_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source selectionSet (.object []))
    (hflatSpec :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet := by
  apply executeRootSelectionSet_eq_spec_of_flattened_collectFields_eq
  have hflatUngrouped :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) := by
    unfold executeRootSelectionSet
    unfold VisitSubfieldsFlatCollects at hdirect
    rw [hdirect]
  exact hflatUngrouped.trans hflatSpec

def ExecutableFieldsFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (fields : List ExecutableField) : Prop :=
  executeRootSelectionSet schema resolvers variableValues depth parentType source
    (executableFieldSelections fields) =
  GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
    depth parentType source (executableFieldSelections fields)

def ExecutableGroupsFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) : Prop :=
  ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
    parentType source (collectedExecutableFields groups)

def ExecutableFieldsMergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity) : Prop :=
  executeRootSelectionSet schema resolvers variableValues (depth + 1)
    parentType source (executableFieldSelections (field :: fields)) =
  [(responseName,
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
      resolved)]

def ExecutableFieldsMergedResponse
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity) : Prop :=
  visitSubfields schema resolvers variableValues (depth + 1) parentType source
    (executableFieldSelections (field :: fields)) (.object []) =
  .object
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
        resolved)]

theorem visitSubfields_eq_object_singleton_of_executeRootSelectionSet_eq_singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name)
    (response : Response)
    (hroot :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet = [(responseName, response)]) :
    visitSubfields schema resolvers variableValues depth parentType source
      selectionSet (.object []) = .object [(responseName, response)] := by
  unfold executeRootSelectionSet at hroot
  generalize hvisit :
    visitSubfields schema resolvers variableValues depth parentType source
      selectionSet (.object []) = output at hroot ⊢
  cases output with
  | null =>
      simp at hroot
  | scalar value =>
      simp at hroot
  | object fields =>
      simp at hroot
      subst fields
      rfl
  | list values =>
      simp at hroot

theorem ExecutableFieldsMergedComplete_of_MergedResponse
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity) :
    ExecutableFieldsMergedResponse schema resolvers variableValues depth
      parentType source responseName field fields resolved ->
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields resolved := by
  intro hresponse
  unfold ExecutableFieldsMergedResponse at hresponse
  unfold ExecutableFieldsMergedComplete
  unfold executeRootSelectionSet
  rw [hresponse]

theorem ExecutableFieldsMergedResponse_of_MergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields resolved ->
    ExecutableFieldsMergedResponse schema resolvers variableValues depth
      parentType source responseName field fields resolved := by
  intro hmerged
  unfold ExecutableFieldsMergedComplete at hmerged
  unfold ExecutableFieldsMergedResponse
  exact
    visitSubfields_eq_object_singleton_of_executeRootSelectionSet_eq_singleton
      schema resolvers variableValues (depth + 1) parentType source
      (executableFieldSelections (field :: fields)) responseName
      (GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields)) resolved)
      hmerged

theorem executeRootSelectionSet_eq_spec_of_flatCollects_and_flatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source selectionSet (.object []))
    (hflatSpec :
      ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet := by
  unfold ExecutableFieldsFlatSpecEquivalent at hflatSpec
  exact executeRootSelectionSet_eq_spec_of_flatCollects_and_flattened_spec
    schema resolvers variableValues depth parentType source selectionSet
    hdirect hflatSpec

theorem executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source selectionSet (.object []))
    (hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet := by
  unfold ExecutableGroupsFlatSpecEquivalent at hgroups
  exact executeRootSelectionSet_eq_spec_of_flatCollects_and_flatSpecEquivalent
    schema resolvers variableValues depth parentType source selectionSet
    hdirect hgroups

theorem ExecutableFieldsFlatSpecEquivalent_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
      parentType source [] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
    executableFieldSelections, GraphQL.Execution.collectFields,
    GraphQL.Execution.executeCollectedFields, visitSubfields]

theorem ExecutableGroupsFlatSpecEquivalent_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
      parentType source [] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simpa [collectedExecutableFields] using
    ExecutableFieldsFlatSpecEquivalent_nil schema resolvers variableValues depth
      parentType source

theorem executeRootSelectionSet_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source selectionSet (.object [])) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet := by
  have hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    rw [hcollect]
    exact ExecutableGroupsFlatSpecEquivalent_nil schema resolvers variableValues
      depth parentType source
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues depth parentType source selectionSet
      hdirect hgroups

end ExecutionUngrouped
end Algorithms

end GraphQL
