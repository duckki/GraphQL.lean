import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Absorption

/-!
Semantic slice/fold view of ungrouped execution.

The operational algorithm still visits selections directly. This module exposes a
proof-facing fold over field slices, so equivalence proofs can reason about
accumulating response slices and absorption instead of normalizing raw selection
order syntactically.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def visitSelectionFold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (output : Response) : Response :=
  selectionSet.foldl
    (fun output selection =>
      visitSelection schema resolvers variableValues depth parentType source
        selection output)
    output

theorem visitSelectionFold_eq_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
    ∀ (selectionSet : List Selection) (output : Response),
      visitSelectionFold schema resolvers variableValues depth parentType
        source selectionSet output =
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet output
  | [], output => by
      simp [visitSelectionFold, visitSubfields]
  | selection :: rest, output => by
      simpa [visitSelectionFold, visitSubfields] using
        visitSelectionFold_eq_visitSubfields schema resolvers variableValues
          depth parentType source rest
          (visitSelection schema resolvers variableValues depth parentType
            source selection output)

def visitFieldSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (output : Response) : Response :=
  match selectionDepth with
  | 0 => output
  | completionDepth + 1 =>
      mergeResponseFieldIntoObject field.responseName
        (executeField schema resolvers variableValues completionDepth source
          output field)
        output

def visitFieldSliceFold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField) (output : Response) : Response :=
  fields.foldl
    (fun output field =>
      visitFieldSlice schema resolvers variableValues selectionDepth source
        field output)
    output

theorem visitFieldSlice_eq_visitSelection_executableFieldSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (parentType : Name)
    (source : Value ObjectIdentity) (field : ExecutableField)
    (output : Response) :
    field.parentType = parentType ->
      visitFieldSlice schema resolvers variableValues selectionDepth source
        field output =
      visitSelection schema resolvers variableValues selectionDepth parentType
        source (executableFieldSelection field) output := by
  intro hparent
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp at hparent ⊢
      subst fieldParent
      cases selectionDepth with
      | zero =>
          simp [visitFieldSlice, visitSelection, executableFieldSelection,
            selectionDirectivesAllowBool_empty]
      | succ completionDepth =>
          simp [visitFieldSlice, visitSelection, executableFieldSelection,
            executableField, selectionDirectivesAllowBool_empty]

theorem visitFieldSliceFold_eq_visitSubfields_executableFieldSelections
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (parentType : Name)
    (source : Value ObjectIdentity) :
    ∀ (fields : List ExecutableField) (output : Response),
      (∀ field, field ∈ fields -> field.parentType = parentType) ->
        visitFieldSliceFold schema resolvers variableValues selectionDepth
          source fields output =
        visitSubfields schema resolvers variableValues selectionDepth parentType
          source (executableFieldSelections fields) output
  | [], output, _hparents => by
      simp [visitFieldSliceFold, executableFieldSelections, visitSubfields]
  | field :: rest, output, hparents => by
      have hfield : field.parentType = parentType :=
        hparents field (by simp)
      have hrest :
          ∀ candidate, candidate ∈ rest ->
            candidate.parentType = parentType := by
        intro candidate hcandidate
        exact hparents candidate (by simp [hcandidate])
      have hstep :
          visitFieldSlice schema resolvers variableValues selectionDepth source
            field output =
          visitSelection schema resolvers variableValues selectionDepth
            parentType source (executableFieldSelection field) output :=
        visitFieldSlice_eq_visitSelection_executableFieldSelection schema
          resolvers variableValues selectionDepth parentType source field output
          hfield
      simp only [visitFieldSliceFold, executableFieldSelections, List.map_cons,
        List.foldl_cons, visitSubfields]
      rw [hstep]
      simpa [visitFieldSliceFold]
        using
          visitFieldSliceFold_eq_visitSubfields_executableFieldSelections
            schema resolvers variableValues selectionDepth parentType source
            rest
            (visitSelection schema resolvers variableValues selectionDepth
              parentType source (executableFieldSelection field) output)
            hrest

def responseFieldSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) : Response :=
  executeField schema resolvers variableValues completionDepth source
    (.object []) field

def responseObjectSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) : Response :=
  .object
    [(field.responseName,
      responseFieldSlice schema resolvers variableValues completionDepth source
        field)]

theorem ResponseMergeReady_responseFieldSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) :
    ResponseMergeReady
      (responseFieldSlice schema resolvers variableValues completionDepth source
        field) := by
  simpa [responseFieldSlice] using
    executeField_response_ready schema resolvers variableValues completionDepth
      source [] field ResponseMergeReady_empty_object

def responseObjectSlices
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField) : List (Name × Response) :=
  fields.map
    (fun field =>
      (field.responseName,
        responseFieldSlice schema resolvers variableValues completionDepth
          source field))

theorem responseObjectSlices_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField) (responseName : Name) :
    responseName ∈
        (responseObjectSlices schema resolvers variableValues completionDepth
          source fields).map Prod.fst ↔
      responseName ∈ fields.map (fun field => field.responseName) := by
  simp [responseObjectSlices]

theorem responseObjectSlices_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField) :
    (fields.map (fun field => field.responseName)).Nodup ->
      PairKeysNodup
        (responseObjectSlices schema resolvers variableValues completionDepth
          source fields) := by
  intro hnodup
  unfold PairKeysNodup
  simpa [responseObjectSlices] using hnodup

def mergeResponseSliceFold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField) (output : Response) : Response :=
  fields.foldl
    (fun output field =>
      mergeResponse output
        (responseObjectSlice schema resolvers variableValues completionDepth
          source field))
    output

def VisitSubfieldsPopulates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (previous : Response) : Prop :=
  visitSubfields schema resolvers variableValues depth parentType source
    selectionSet previous =
  mergeResponse previous
    (visitSubfields schema resolvers variableValues depth parentType source
      selectionSet (.object []))

namespace VisitSubfieldsPopulates

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (previous : Response) :
    VisitSubfieldsPopulates schema resolvers variableValues depth parentType
      source [] previous := by
  simp [VisitSubfieldsPopulates, visitSubfields,
    mergeResponse_empty_object_right]

end VisitSubfieldsPopulates

def FieldSliceMergeFoldPopulates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField) (previous : Response) : Prop :=
  mergeResponseSliceFold schema resolvers variableValues completionDepth source
    fields previous =
  mergeResponse previous
    (mergeResponseSliceFold schema resolvers variableValues completionDepth
      source fields (.object []))

namespace FieldSliceMergeFoldPopulates

theorem mergeResponseSliceFold_object_append_of_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity) :
    ∀ (fields : List ExecutableField)
      (outputFields : List (Name × Response)),
      (fields.map (fun field => field.responseName)).Nodup ->
      (∀ field, field ∈ fields ->
        field.responseName ∉ outputFields.map Prod.fst) ->
        mergeResponseSliceFold schema resolvers variableValues completionDepth
          source fields (.object outputFields) =
        .object
          (outputFields ++
            responseObjectSlices schema resolvers variableValues
              completionDepth source fields)
  | [], outputFields, _hnodup, _hdisjoint => by
      simp [mergeResponseSliceFold, responseObjectSlices]
  | field :: rest, outputFields, hnodup, hdisjoint => by
      let incoming :=
        responseFieldSlice schema resolvers variableValues completionDepth source
          field
      have hfresh : field.responseName ∉ outputFields.map Prod.fst :=
        hdisjoint field (by simp)
      have hparts :
          field.responseName ∉ rest.map (fun field => field.responseName) ∧
          (rest.map (fun field => field.responseName)).Nodup := by
        simpa using List.nodup_cons.mp hnodup
      have hheadMerge :
          mergeResponse (.object outputFields)
            (responseObjectSlice schema resolvers variableValues completionDepth
              source field) =
          .object (outputFields ++ [(field.responseName, incoming)]) := by
        simpa [responseObjectSlice, incoming] using
          mergeResponse_object_append_of_disjoint outputFields
            [(field.responseName, incoming)]
            (by simp [PairKeysNodup])
            (by
              intro responseName hmem
              simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
              subst responseName
              exact hfresh)
      have hrestDisjoint :
          ∀ candidate, candidate ∈ rest ->
            candidate.responseName ∉
              (outputFields ++ [(field.responseName, incoming)]).map
                Prod.fst := by
        intro candidate hcandidate
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton]
        intro hmem
        rcases hmem with houtput | hhead
        · exact hdisjoint candidate (by simp [hcandidate]) houtput
        · have hcandidateNotHead :
              candidate.responseName ≠ field.responseName := by
            intro heq
            exact hparts.1
              (List.mem_map.mpr ⟨candidate, hcandidate, heq⟩)
          exact hcandidateNotHead hhead
      have hrestFold :=
        mergeResponseSliceFold_object_append_of_responseNamesNodup schema
          resolvers variableValues completionDepth source rest
          (outputFields ++ [(field.responseName, incoming)]) hparts.2
          hrestDisjoint
      simpa [mergeResponseSliceFold, hheadMerge, responseObjectSlices,
        incoming, List.append_assoc] using hrestFold

theorem of_responseNamesNodup_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField) (outputFields : List (Name × Response))
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hdisjoint :
      ∀ field, field ∈ fields ->
        field.responseName ∉ outputFields.map Prod.fst) :
    FieldSliceMergeFoldPopulates schema resolvers variableValues
      completionDepth source fields (.object outputFields) := by
  have hleft :
      mergeResponseSliceFold schema resolvers variableValues completionDepth
        source fields (.object outputFields) =
      .object
        (outputFields ++
          responseObjectSlices schema resolvers variableValues completionDepth
            source fields) :=
    mergeResponseSliceFold_object_append_of_responseNamesNodup schema resolvers
      variableValues completionDepth source fields outputFields hnodup
      hdisjoint
  have hempty :
      mergeResponseSliceFold schema resolvers variableValues completionDepth
        source fields (.object []) =
      .object
        (responseObjectSlices schema resolvers variableValues completionDepth
          source fields) := by
    simpa using
      mergeResponseSliceFold_object_append_of_responseNamesNodup schema
        resolvers variableValues completionDepth source fields [] hnodup
        (by intro field _hmem; simp)
  have hslicesNodup :
      PairKeysNodup
        (responseObjectSlices schema resolvers variableValues completionDepth
          source fields) :=
    responseObjectSlices_pairKeysNodup schema resolvers variableValues
      completionDepth source fields hnodup
  have hslicesDisjoint :
      ∀ responseName,
        responseName ∈
          (responseObjectSlices schema resolvers variableValues
            completionDepth source fields).map Prod.fst ->
        responseName ∉ outputFields.map Prod.fst := by
    intro responseName hmem
    rw [responseObjectSlices_key_mem schema resolvers variableValues
      completionDepth source fields responseName] at hmem
    rcases List.mem_map.mp hmem with ⟨field, hfield, hresponse⟩
    rw [← hresponse]
    exact hdisjoint field hfield
  unfold FieldSliceMergeFoldPopulates
  rw [hleft, hempty]
  rw [mergeResponse_object_append_of_disjoint outputFields
    (responseObjectSlices schema resolvers variableValues completionDepth
      source fields)
    hslicesNodup hslicesDisjoint]

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (previous : Response) :
    FieldSliceMergeFoldPopulates schema resolvers variableValues
      completionDepth source [] previous := by
  simp [FieldSliceMergeFoldPopulates, mergeResponseSliceFold,
    mergeResponse_empty_object_right]

theorem singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (previous : Response) :
    FieldSliceMergeFoldPopulates schema resolvers variableValues
      completionDepth source [field] previous := by
  simp [FieldSliceMergeFoldPopulates, mergeResponseSliceFold,
    responseObjectSlice, mergeResponse, mergeResponseFields,
    mergeResponseField]

theorem cons_of_tail_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (previous : Response)
    (hmerge :
      mergeResponseSliceFold schema resolvers variableValues completionDepth
        source rest
        (mergeResponse previous
          (responseObjectSlice schema resolvers variableValues completionDepth
            source field)) =
      mergeResponse previous
        (mergeResponseSliceFold schema resolvers variableValues completionDepth
          source rest
          (mergeResponse (.object [])
            (responseObjectSlice schema resolvers variableValues
              completionDepth source field)))) :
    FieldSliceMergeFoldPopulates schema resolvers variableValues
      completionDepth source (field :: rest) previous := by
  simpa [FieldSliceMergeFoldPopulates, mergeResponseSliceFold] using hmerge

end FieldSliceMergeFoldPopulates

def CompleteValuePopulates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (selectionSet : List Selection) (value : Value ObjectIdentity)
    (previous : Response) : Prop :=
  completeValue schema resolvers variableValues completionDepth parentType
    selectionSet value previous =
  mergeResponse previous
    (completeValue schema resolvers variableValues completionDepth parentType
      selectionSet value .null)

namespace CompleteValuePopulates

theorem null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (selectionSet : List Selection) :
    CompleteValuePopulates schema resolvers variableValues completionDepth
      parentType selectionSet (.null : Value ObjectIdentity) .null := by
  cases completionDepth <;>
    simp [CompleteValuePopulates, completeValue, shallowResponse,
      mergeResponse]

theorem null_responseFieldSlice
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : Value ObjectIdentity}
    {first later : ExecutableField}
    (hfirstResolve :
      resolvers.resolve first.parentType first.fieldName first.arguments
        source = .null)
    (hlaterResolve :
      resolvers.resolve later.parentType later.fieldName later.arguments
        source = .null) :
    CompleteValuePopulates schema resolvers variableValues completionDepth
      ((schema.fieldReturnType? later.parentType later.fieldName).getD
        later.fieldName)
      later.selectionSet
      (resolvers.resolve later.parentType later.fieldName later.arguments source)
      (responseFieldSlice schema resolvers variableValues completionDepth source
        first) := by
  have hfirstSlice :
      responseFieldSlice schema resolvers variableValues completionDepth source
          first =
        .null := by
    cases completionDepth <;>
      simp [responseFieldSlice, executeField_empty_output, hfirstResolve,
        completeValue, shallowResponse]
  rw [hfirstSlice, hlaterResolve]
  exact null schema resolvers variableValues completionDepth
    ((schema.fieldReturnType? later.parentType later.fieldName).getD
      later.fieldName)
    later.selectionSet

theorem scalar_self
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (selectionSet : List Selection) (value : String) :
    CompleteValuePopulates schema resolvers variableValues completionDepth
      parentType selectionSet (.scalar value : Value ObjectIdentity)
      (.scalar value) := by
  cases completionDepth <;>
    simp [CompleteValuePopulates, completeValue, shallowResponse,
      mergeResponse]

theorem scalar_responseFieldSlice
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : Value ObjectIdentity}
    {first later : ExecutableField} {value : String}
    (hfirstResolve :
      resolvers.resolve first.parentType first.fieldName first.arguments
        source = .scalar value)
    (hlaterResolve :
      resolvers.resolve later.parentType later.fieldName later.arguments
        source = .scalar value) :
    CompleteValuePopulates schema resolvers variableValues completionDepth
      ((schema.fieldReturnType? later.parentType later.fieldName).getD
        later.fieldName)
      later.selectionSet
      (resolvers.resolve later.parentType later.fieldName later.arguments source)
      (responseFieldSlice schema resolvers variableValues completionDepth source
        first) := by
  have hfirstSlice :
      responseFieldSlice schema resolvers variableValues completionDepth source
          first =
        .scalar value := by
    simp [responseFieldSlice, executeField_empty_output, hfirstResolve,
      completeValue_scalar_any_depth_eq_scalar]
  rw [hfirstSlice, hlaterResolve]
  exact scalar_self schema resolvers variableValues completionDepth
    ((schema.fieldReturnType? later.parentType later.fieldName).getD
      later.fieldName)
    later.selectionSet value

theorem object_of_visit_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection) (previousFields : List (Name × Response))
    (hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true)
    (hvisit :
      visitSubfields schema resolvers variableValues completionDepth
        runtimeType (.object runtimeType (some identity)) selectionSet
        (.object previousFields) =
      mergeResponse (.object previousFields)
        (visitSubfields schema resolvers variableValues completionDepth
          runtimeType (.object runtimeType (some identity)) selectionSet
          (.object []))) :
    CompleteValuePopulates schema resolvers variableValues (completionDepth + 1)
      parentType selectionSet (.object runtimeType (some identity))
      (.object previousFields) := by
  simpa [CompleteValuePopulates, completeValue, hincludes] using hvisit

theorem object_of_visit_populates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection) (previousFields : List (Name × Response))
    (hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true)
    (hvisit :
      VisitSubfieldsPopulates schema resolvers variableValues completionDepth
        runtimeType (.object runtimeType (some identity)) selectionSet
        (.object previousFields)) :
    CompleteValuePopulates schema resolvers variableValues (completionDepth + 1)
      parentType selectionSet (.object runtimeType (some identity))
      (.object previousFields) := by
  exact object_of_visit_merge schema resolvers variableValues completionDepth
    parentType runtimeType identity selectionSet previousFields hincludes hvisit

theorem object_responseFieldSlice_of_visit_populates
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : Value ObjectIdentity}
    {first later : ExecutableField}
    {runtimeType : Name} {identity : ObjectIdentity}
    {previousFields : List (Name × Response)}
    (hfirstSlice :
      responseFieldSlice schema resolvers variableValues (completionDepth + 1)
          source first =
        .object previousFields)
    (hlaterResolve :
      resolvers.resolve later.parentType later.fieldName later.arguments
        source = .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? later.parentType later.fieldName).getD
          later.fieldName)
        runtimeType = true)
    (hvisit :
      VisitSubfieldsPopulates schema resolvers variableValues completionDepth
        runtimeType (.object runtimeType (some identity)) later.selectionSet
        (.object previousFields)) :
    CompleteValuePopulates schema resolvers variableValues (completionDepth + 1)
      ((schema.fieldReturnType? later.parentType later.fieldName).getD
        later.fieldName)
      later.selectionSet
      (resolvers.resolve later.parentType later.fieldName later.arguments source)
      (responseFieldSlice schema resolvers variableValues (completionDepth + 1)
        source first) := by
  rw [hfirstSlice, hlaterResolve]
  exact object_of_visit_populates schema resolvers variableValues
    completionDepth
    ((schema.fieldReturnType? later.parentType later.fieldName).getD
      later.fieldName)
    runtimeType identity later.selectionSet previousFields hincludes hvisit

theorem completeValue_list_fold_previous_fn_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (selectionSet : List Selection)
    (previous : Value ObjectIdentity -> Response) :
    ∀ (values : List (Value ObjectIdentity)) (acc : List Response),
      (List.foldl
        (fun (state : List Response × List Response)
            (value : Value ObjectIdentity) =>
          (completeValue schema resolvers variableValues completionDepth
              parentType selectionSet value
              (match state.snd with
              | [] => .null
              | previous :: _rest => previous) ::
            state.fst,
          match state.snd with
          | [] => []
          | _previous :: rest => rest))
        (acc, values.map previous) values).fst =
      (values.map
        (fun value =>
          completeValue schema resolvers variableValues completionDepth
            parentType selectionSet value (previous value))).reverse ++ acc
  | [], acc => by
      simp
  | value :: rest, acc => by
      simp [completeValue_list_fold_previous_fn_eq_map schema resolvers
        variableValues completionDepth parentType selectionSet previous rest
        (completeValue schema resolvers variableValues completionDepth
          parentType selectionSet value (previous value) :: acc),
        List.append_assoc]

theorem completeValue_list_previous_fn_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (selectionSet : List Selection)
    (values : List (Value ObjectIdentity))
    (previous : Value ObjectIdentity -> Response) :
    completeValue schema resolvers variableValues (completionDepth + 1)
      parentType selectionSet (.list values) (.list (values.map previous)) =
    .list
      (values.map
        (fun value =>
          completeValue schema resolvers variableValues completionDepth
            parentType selectionSet value (previous value))) := by
  simpa [completeValue] using
    congrArg List.reverse
      (completeValue_list_fold_previous_fn_eq_map schema resolvers
        variableValues completionDepth parentType selectionSet previous values
        [])

theorem list_of_values
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    (completionDepth : Nat) (parentType : Name)
    (selectionSet : List Selection) (values : List (Value ObjectIdentity))
    (previous : Value ObjectIdentity -> Response)
    (hvalues :
      ∀ value, value ∈ values ->
        CompleteValuePopulates schema resolvers variableValues completionDepth
          parentType selectionSet value (previous value)) :
    CompleteValuePopulates schema resolvers variableValues
      (completionDepth + 1) parentType selectionSet (.list values)
      (.list (values.map previous)) := by
  unfold CompleteValuePopulates
  rw [completeValue_list_previous_fn_eq_map schema resolvers variableValues
    completionDepth parentType selectionSet values previous]
  rw [completeValue_list_empty_previous_eq_map schema resolvers variableValues
    completionDepth parentType selectionSet values]
  simp [mergeResponse]
  exact
    (mergeResponseLists_map_of_forall values previous
      (fun value =>
        completeValue schema resolvers variableValues completionDepth
          parentType selectionSet value .null)
      (fun value =>
        completeValue schema resolvers variableValues completionDepth
          parentType selectionSet value (previous value))
      (by
        intro value hmem
        exact (hvalues value hmem).symm)).symm

theorem list_responseFieldSlice
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : Value ObjectIdentity}
    {first later : ExecutableField} {values : List (Value ObjectIdentity)}
    (hreturn :
      ((schema.fieldReturnType? first.parentType first.fieldName).getD
        first.fieldName) =
      ((schema.fieldReturnType? later.parentType later.fieldName).getD
        later.fieldName))
    (hfirstResolve :
      resolvers.resolve first.parentType first.fieldName first.arguments
        source = .list values)
    (hlaterResolve :
      resolvers.resolve later.parentType later.fieldName later.arguments
        source = .list values)
    (hvalues :
      ∀ value, value ∈ values ->
        CompleteValuePopulates schema resolvers variableValues completionDepth
          ((schema.fieldReturnType? later.parentType later.fieldName).getD
            later.fieldName)
          later.selectionSet value
          (completeValue schema resolvers variableValues completionDepth
            ((schema.fieldReturnType? later.parentType later.fieldName).getD
              later.fieldName)
            first.selectionSet value .null)) :
    CompleteValuePopulates schema resolvers variableValues
      (completionDepth + 1)
      ((schema.fieldReturnType? later.parentType later.fieldName).getD
        later.fieldName)
      later.selectionSet
      (resolvers.resolve later.parentType later.fieldName later.arguments source)
      (responseFieldSlice schema resolvers variableValues (completionDepth + 1)
        source first) := by
  let laterChildType :=
    ((schema.fieldReturnType? later.parentType later.fieldName).getD
      later.fieldName)
  have hfirstSlice :
      responseFieldSlice schema resolvers variableValues (completionDepth + 1)
          source first =
        .list
          (values.map
            (fun value =>
              completeValue schema resolvers variableValues completionDepth
                laterChildType first.selectionSet value .null)) := by
    rw [responseFieldSlice, executeField_empty_output, hfirstResolve]
    rw [hreturn]
    exact
      completeValue_list_empty_previous_eq_map schema resolvers variableValues
        completionDepth laterChildType first.selectionSet values
  rw [hfirstSlice, hlaterResolve]
  exact
    list_of_values completionDepth laterChildType later.selectionSet values
      (fun value =>
        completeValue schema resolvers variableValues completionDepth
          laterChildType first.selectionSet value .null)
      hvalues

end CompleteValuePopulates

theorem mergeResponseField_eq_of_lookup_absorbs
    (responseName : Name) (existing incomingSlice incomingFull : Response)
    (fields : List (Name × Response)) :
    lookupResponseField? responseName fields = some existing ->
    ResponseAbsorbs existing incomingFull ->
    incomingFull = mergeResponse existing incomingSlice ->
      mergeResponseField responseName incomingFull fields =
      mergeResponseField responseName incomingSlice fields := by
  intro hlookup habsorbs hincomingFull
  induction fields with
  | nil =>
      simp [lookupResponseField?] at hlookup
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, fieldResponse⟩
      by_cases hname : fieldResponseName == responseName
      · have hfield : fieldResponseName = responseName := beq_iff_eq.mp hname
        simp [lookupResponseField?, hname] at hlookup
        subst existing
        have hincomingAbsorbed :
            mergeResponse fieldResponse incomingFull = incomingFull := by
          simpa [ResponseAbsorbs] using habsorbs
        simp [mergeResponseField, hname]
        exact hincomingAbsorbed.trans hincomingFull
      · simp [lookupResponseField?, hname] at hlookup
        simp [mergeResponseField, hname, ih hlookup]

theorem visitFieldSlice_succ_object_eq_mergeResponseSlice_of_step
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (fields : List (Name × Response))
    (hstep :
      executeField schema resolvers variableValues completionDepth source
        (.object fields) field =
        match responseObjectField? field.responseName (.object fields) with
        | some existing =>
            mergeResponse existing
              (responseFieldSlice schema resolvers variableValues
                completionDepth source field)
        | none =>
            responseFieldSlice schema resolvers variableValues completionDepth
              source field)
    (habsorbs :
      ∀ existing,
        responseObjectField? field.responseName (.object fields) =
          some existing ->
        ResponseAbsorbs existing
          (executeField schema resolvers variableValues completionDepth source
            (.object fields) field)) :
      visitFieldSlice schema resolvers variableValues (completionDepth + 1)
        source field (.object fields) =
      mergeResponse (.object fields)
        (responseObjectSlice schema resolvers variableValues completionDepth
          source field) := by
  unfold visitFieldSlice responseObjectSlice responseFieldSlice
  simp only [mergeResponseFieldIntoObject, mergeResponse]
  cases hlookup :
      responseObjectField? field.responseName (.object fields) with
  | none =>
      simp [hlookup] at hstep
      rw [hstep]
      simp [mergeResponseFields, responseFieldSlice]
  | some existing =>
      simp [hlookup] at hstep
      rw [hstep]
      have hlookupFields :
          lookupResponseField? field.responseName fields = some existing := by
        simpa [responseObjectField?] using hlookup
      apply congrArg Response.object
      rw [show
          mergeResponseFields fields
            [(field.responseName,
              executeField schema resolvers variableValues completionDepth
                source (.object []) field)] =
          mergeResponseField field.responseName
            (executeField schema resolvers variableValues completionDepth source
              (.object []) field)
            fields by
        simp [mergeResponseFields]]
      exact
        mergeResponseField_eq_of_lookup_absorbs field.responseName existing
          (executeField schema resolvers variableValues completionDepth source
            (.object []) field)
          (mergeResponse existing
            (executeField schema resolvers variableValues completionDepth source
              (.object []) field))
          fields hlookupFields
          (by
            simpa [hstep] using habsorbs existing hlookup)
          rfl

structure FieldSliceMergeStep
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (fields : List (Name × Response)) : Prop where
  step_eq :
    executeField schema resolvers variableValues completionDepth source
      (.object fields) field =
      match responseObjectField? field.responseName (.object fields) with
      | some existing =>
          mergeResponse existing
            (responseFieldSlice schema resolvers variableValues completionDepth
              source field)
      | none =>
          responseFieldSlice schema resolvers variableValues completionDepth
            source field
  absorbs :
    ∀ existing,
      responseObjectField? field.responseName (.object fields) =
        some existing ->
      ResponseAbsorbs existing
        (executeField schema resolvers variableValues completionDepth source
          (.object fields) field)

namespace FieldSliceMergeStep

def of_fresh
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : Value ObjectIdentity}
    {field : ExecutableField} {fields : List (Name × Response)}
    (hfresh : field.responseName ∉ fields.map Prod.fst) :
    FieldSliceMergeStep schema resolvers variableValues completionDepth source
      field fields := by
  have hlookup :
      responseObjectField? field.responseName (.object fields) = none :=
    responseObjectField?_none_of_not_mem field.responseName fields hfresh
  refine
    { step_eq := ?_
      absorbs := ?_ }
  · rw [executeField_object_fresh_eq_empty_output schema resolvers
      variableValues completionDepth source field fields hfresh]
    simp [hlookup, responseFieldSlice]
  · intro existing hsome
    rw [hlookup] at hsome
    contradiction

def of_reentry
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : Value ObjectIdentity}
    {field : ExecutableField} {fields : List (Name × Response)}
    {existing : Response}
    (hlookup :
      responseObjectField? field.responseName (.object fields) =
        some existing)
    (hstep :
      executeField schema resolvers variableValues completionDepth source
        (.object fields) field =
      mergeResponse existing
        (responseFieldSlice schema resolvers variableValues completionDepth
          source field))
    (habsorbs :
      ResponseAbsorbs existing
        (executeField schema resolvers variableValues completionDepth source
          (.object fields) field)) :
    FieldSliceMergeStep schema resolvers variableValues completionDepth source
      field fields := by
  refine
    { step_eq := ?_
      absorbs := ?_ }
  · simp [hlookup, hstep]
  · intro candidate hcandidate
    rw [hlookup] at hcandidate
    injection hcandidate with hcandidateEq
    subst candidate
    exact habsorbs

def of_reentry_populates
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : Value ObjectIdentity}
    {field : ExecutableField} {fields : List (Name × Response)}
    {existing : Response}
    (hlookup :
      responseObjectField? field.responseName (.object fields) =
        some existing)
    (hpopulate :
      CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        existing)
    (hexistingReady : ResponseMergeReady existing) :
    FieldSliceMergeStep schema resolvers variableValues completionDepth source
      field fields := by
  apply FieldSliceMergeStep.of_reentry hlookup
  · rw [executeField_reentry_of_lookup schema resolvers variableValues
      completionDepth source field fields existing hlookup]
    simpa [CompleteValuePopulates, responseFieldSlice, executeField_empty_output]
      using hpopulate
  · have hsliceReady :
        ResponseMergeReady
          (responseFieldSlice schema resolvers variableValues completionDepth
            source field) := by
      exact
        ResponseMergeReady_responseFieldSlice schema resolvers variableValues
          completionDepth source field
    rw [executeField_reentry_of_lookup schema resolvers variableValues
      completionDepth source field fields existing hlookup]
    rw [hpopulate]
    simpa [responseFieldSlice, executeField_empty_output] using
      ResponseAbsorbs_merge_of_ready existing
        (responseFieldSlice schema resolvers variableValues completionDepth
          source field)
        hexistingReady hsliceReady

end FieldSliceMergeStep

def FieldSliceMergeTrace
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity) :
    List ExecutableField -> Response -> Prop
  | [], _output => True
  | field :: rest, .object fields =>
      FieldSliceMergeStep schema resolvers variableValues completionDepth
        source field fields
      ∧
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source rest
        (mergeResponse (.object fields)
          (responseObjectSlice schema resolvers variableValues completionDepth
            source field))
  | _field :: _rest, _output => False

namespace FieldSliceMergeTrace

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (output : Response) :
    FieldSliceMergeTrace schema resolvers variableValues completionDepth source
      [] output := by
  simp [FieldSliceMergeTrace]

theorem cons_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × Response))
    (hstep :
      FieldSliceMergeStep schema resolvers variableValues completionDepth
        source field fields)
    (hrest :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source rest
        (mergeResponse (.object fields)
          (responseObjectSlice schema resolvers variableValues completionDepth
            source field))) :
    FieldSliceMergeTrace schema resolvers variableValues completionDepth source
      (field :: rest) (.object fields) := by
  exact ⟨hstep, hrest⟩

theorem cons_fresh_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × Response))
    (hfresh : field.responseName ∉ fields.map Prod.fst)
    (hrest :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source rest
        (mergeResponse (.object fields)
          (responseObjectSlice schema resolvers variableValues completionDepth
            source field))) :
    FieldSliceMergeTrace schema resolvers variableValues completionDepth source
      (field :: rest) (.object fields) :=
  cons_object schema resolvers variableValues completionDepth source field rest
    fields (FieldSliceMergeStep.of_fresh hfresh) hrest

theorem cons_reentry_populates_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × Response)) (existing : Response)
    (hlookup :
      responseObjectField? field.responseName (.object fields) =
        some existing)
    (hpopulate :
      CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        existing)
    (hexistingReady : ResponseMergeReady existing)
    (hrest :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source rest
        (mergeResponse (.object fields)
          (responseObjectSlice schema resolvers variableValues completionDepth
            source field))) :
    FieldSliceMergeTrace schema resolvers variableValues completionDepth source
      (field :: rest) (.object fields) :=
  cons_object schema resolvers variableValues completionDepth source field rest
    fields
    (FieldSliceMergeStep.of_reentry_populates hlookup hpopulate
      hexistingReady)
    hrest

theorem of_responseNamesNodup_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity) :
    ∀ (fields : List ExecutableField) (outputFields : List (Name × Response)),
      (fields.map (fun field => field.responseName)).Nodup ->
      (∀ field, field ∈ fields ->
        field.responseName ∉ outputFields.map Prod.fst) ->
        FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source fields (.object outputFields)
  | [], outputFields, _hnodup, _hdisjoint => by
      simp [FieldSliceMergeTrace]
  | field :: rest, outputFields, hnodup, hdisjoint => by
      have hfresh : field.responseName ∉ outputFields.map Prod.fst :=
        hdisjoint field (by simp)
      have hparts :
          field.responseName ∉ rest.map (fun field => field.responseName) ∧
          (rest.map (fun field => field.responseName)).Nodup := by
        simpa using List.nodup_cons.mp hnodup
      let incoming :=
        responseFieldSlice schema resolvers variableValues completionDepth source
          field
      have hmerge :
          mergeResponseFields outputFields [(field.responseName, incoming)] =
          outputFields ++ [(field.responseName, incoming)] := by
        apply mergeResponseFields_append_of_disjoint
        · simp [PairKeysNodup]
        · intro responseName hmem
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
          subst responseName
          exact hfresh
      have hrestDisjoint :
          ∀ candidate, candidate ∈ rest ->
            candidate.responseName ∉
              (mergeResponseFields outputFields
                [(field.responseName, incoming)]).map Prod.fst := by
        intro candidate hcandidate
        rw [hmerge]
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton]
        intro hmem
        rcases hmem with houtput | hfield
        · exact hdisjoint candidate (by simp [hcandidate]) houtput
        · have hcandidateNotHead :
              candidate.responseName ≠ field.responseName := by
            intro heq
            exact hparts.1
              (List.mem_map.mpr ⟨candidate, hcandidate, heq⟩)
          exact hcandidateNotHead hfield
      refine
        FieldSliceMergeTrace.cons_object schema resolvers variableValues
          completionDepth source field rest outputFields
          (FieldSliceMergeStep.of_fresh hfresh) ?_
      simpa [responseObjectSlice, responseFieldSlice, incoming, mergeResponse]
        using
          of_responseNamesNodup_object schema resolvers variableValues
            completionDepth source rest
            (mergeResponseFields outputFields
              [(field.responseName, incoming)])
            hparts.2 hrestDisjoint

theorem of_responseNamesNodup_empty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup) :
    FieldSliceMergeTrace schema resolvers variableValues completionDepth source
      fields (.object []) :=
  of_responseNamesNodup_object schema resolvers variableValues completionDepth
    source fields [] hnodup (by intro field _hmem; simp)

theorem two_duplicate_of_first_slice_populates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (first later : ExecutableField) (existing : Response)
    (hsameResponse : later.responseName = first.responseName)
    (hfirstSlice :
      responseFieldSlice schema resolvers variableValues completionDepth source
        first = existing)
    (hpopulate :
      CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD
          later.fieldName)
        later.selectionSet
        (resolvers.resolve later.parentType later.fieldName later.arguments
          source)
        existing)
    (hexistingReady : ResponseMergeReady existing) :
    FieldSliceMergeTrace schema resolvers variableValues completionDepth source
      [first, later] (.object []) := by
  apply FieldSliceMergeTrace.cons_fresh_object schema resolvers variableValues
    completionDepth source first [later] []
  · simp
  · have htail :
        FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source [later] (.object [(first.responseName, existing)]) := by
      apply FieldSliceMergeTrace.cons_reentry_populates_object schema
        resolvers variableValues completionDepth source later []
        [(first.responseName, existing)] existing
      · simp [responseObjectField?, lookupResponseField?, hsameResponse]
      · exact hpopulate
      · exact hexistingReady
      · exact FieldSliceMergeTrace.nil schema resolvers variableValues
          completionDepth source
          (mergeResponse (.object [(first.responseName, existing)])
            (responseObjectSlice schema resolvers variableValues completionDepth
              source later))
    simpa [responseObjectSlice, hfirstSlice, mergeResponse,
      mergeResponseFields, mergeResponseField] using htail

theorem two_scalar_duplicate
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (first later : ExecutableField) (value : String)
    (hsameResponse : later.responseName = first.responseName)
    (hfirstResolve :
      resolvers.resolve first.parentType first.fieldName first.arguments
        source = .scalar value)
    (hlaterResolve :
      resolvers.resolve later.parentType later.fieldName later.arguments
        source = .scalar value) :
    FieldSliceMergeTrace schema resolvers variableValues completionDepth source
      [first, later] (.object []) := by
  apply FieldSliceMergeTrace.cons_fresh_object schema resolvers variableValues
    completionDepth source first [later] []
  · simp
  · have htail :
        FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source [later] (.object [(first.responseName, .scalar value)]) := by
      apply FieldSliceMergeTrace.cons_reentry_populates_object schema
        resolvers variableValues completionDepth source later [] 
        [(first.responseName, .scalar value)] (.scalar value)
      · simp [responseObjectField?, lookupResponseField?, hsameResponse]
      · simpa [hlaterResolve] using
          CompleteValuePopulates.scalar_self schema resolvers variableValues
            completionDepth
            ((schema.fieldReturnType? later.parentType later.fieldName).getD
              later.fieldName)
            later.selectionSet value
      · exact ResponseMergeReady.scalar value
      · exact FieldSliceMergeTrace.nil schema resolvers variableValues
          completionDepth source
          (mergeResponse (.object [(first.responseName, .scalar value)])
            (responseObjectSlice schema resolvers variableValues completionDepth
              source later))
    simpa [responseObjectSlice, responseFieldSlice, executeField_empty_output,
      hfirstResolve, completeValue, mergeResponse, mergeResponseFields,
      mergeResponseField, completeValue_scalar_any_depth_eq_scalar] using htail

end FieldSliceMergeTrace

theorem visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity) :
    ∀ (fields : List ExecutableField) (output : Response),
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source fields output ->
        visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source fields output =
        mergeResponseSliceFold schema resolvers variableValues completionDepth
          source fields output
  | [], output, _htrace => by
      simp [visitFieldSliceFold, mergeResponseSliceFold]
  | field :: rest, output, htrace => by
      cases output with
      | null =>
          simp [FieldSliceMergeTrace] at htrace
      | scalar value =>
          simp [FieldSliceMergeTrace] at htrace
      | list values =>
          simp [FieldSliceMergeTrace] at htrace
      | object fields =>
          rcases htrace with ⟨hstep, hrest⟩
          have hone :
              visitFieldSlice schema resolvers variableValues
                (completionDepth + 1) source field (.object fields) =
              mergeResponse (.object fields)
                (responseObjectSlice schema resolvers variableValues
                  completionDepth source field) :=
            visitFieldSlice_succ_object_eq_mergeResponseSlice_of_step schema
              resolvers variableValues completionDepth source field fields
              hstep.step_eq hstep.absorbs
          simp [visitFieldSliceFold, mergeResponseSliceFold, hone]
          exact
            visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
              resolvers variableValues completionDepth source rest
              (mergeResponse (.object fields)
                (responseObjectSlice schema resolvers variableValues
                  completionDepth source field))
              hrest

theorem visitFieldSliceFold_succ_empty_eq_mergeResponseSliceFold_of_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup) :
    visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
      source fields (.object []) =
    mergeResponseSliceFold schema resolvers variableValues completionDepth
      source fields (.object []) :=
  visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema resolvers
    variableValues completionDepth source fields (.object [])
    (FieldSliceMergeTrace.of_responseNamesNodup_empty schema resolvers
      variableValues completionDepth source fields hnodup)

theorem visitSubfields_executableFieldSelections_succ_empty_eq_mergeResponseSliceFold_of_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : Value ObjectIdentity)
    (fields : List ExecutableField)
    (hparents :
      ∀ field, field ∈ fields -> field.parentType = parentType)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup) :
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections fields) (.object []) =
    mergeResponseSliceFold schema resolvers variableValues completionDepth
      source fields (.object []) := by
  have hvisit :
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source fields (.object []) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections fields) (.object []) :=
    visitFieldSliceFold_eq_visitSubfields_executableFieldSelections schema
      resolvers variableValues (completionDepth + 1) parentType source fields
      (.object []) hparents
  exact hvisit.symm.trans
    (visitFieldSliceFold_succ_empty_eq_mergeResponseSliceFold_of_responseNamesNodup
      schema resolvers variableValues completionDepth source fields hnodup)

theorem VisitSubfieldsPopulates.of_executableFieldSelections_trace_fold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : Value ObjectIdentity)
    (fields : List ExecutableField) (previous : Response)
    (hparents :
      ∀ field, field ∈ fields -> field.parentType = parentType)
    (htracePrevious :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source fields previous)
    (htraceEmpty :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source fields (.object []))
    (hfold :
      FieldSliceMergeFoldPopulates schema resolvers variableValues
        completionDepth source fields previous) :
    VisitSubfieldsPopulates schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections fields) previous := by
  have hpreviousVisit :
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source fields previous =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections fields) previous :=
    visitFieldSliceFold_eq_visitSubfields_executableFieldSelections schema
      resolvers variableValues (completionDepth + 1) parentType source fields
      previous hparents
  have hpreviousFold :
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source fields previous =
      mergeResponseSliceFold schema resolvers variableValues completionDepth
        source fields previous :=
    visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
      resolvers variableValues completionDepth source fields previous
      htracePrevious
  have hemptyVisit :
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source fields (.object []) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections fields) (.object []) :=
    visitFieldSliceFold_eq_visitSubfields_executableFieldSelections schema
      resolvers variableValues (completionDepth + 1) parentType source fields
      (.object []) hparents
  have hemptyFold :
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source fields (.object []) =
      mergeResponseSliceFold schema resolvers variableValues completionDepth
        source fields (.object []) :=
    visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
      resolvers variableValues completionDepth source fields (.object [])
      htraceEmpty
  unfold VisitSubfieldsPopulates
  rw [← hpreviousVisit, hpreviousFold, hfold, ← hemptyFold, hemptyVisit]

theorem VisitSubfieldsPopulates.of_executableFieldSelections_responseNamesNodup_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : Value ObjectIdentity)
    (fields : List ExecutableField)
    (previousFields : List (Name × Response))
    (hparents :
      ∀ field, field ∈ fields -> field.parentType = parentType)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hdisjoint :
      ∀ field, field ∈ fields ->
        field.responseName ∉ previousFields.map Prod.fst) :
    VisitSubfieldsPopulates schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections fields) (.object previousFields) :=
  VisitSubfieldsPopulates.of_executableFieldSelections_trace_fold schema
    resolvers variableValues completionDepth parentType source fields
    (.object previousFields) hparents
    (FieldSliceMergeTrace.of_responseNamesNodup_object schema resolvers
      variableValues completionDepth source fields previousFields hnodup
      hdisjoint)
    (FieldSliceMergeTrace.of_responseNamesNodup_empty schema resolvers
      variableValues completionDepth source fields hnodup)
    (FieldSliceMergeFoldPopulates.of_responseNamesNodup_object schema resolvers
      variableValues completionDepth source fields previousFields hnodup
      hdisjoint)

theorem CompleteValuePopulates.object_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType runtimeType : Name)
    (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (previousFields : List (Name × Response))
    (hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true)
    (hparents :
      ∀ field, field ∈ fields -> field.parentType = runtimeType)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hdisjoint :
      ∀ field, field ∈ fields ->
        field.responseName ∉ previousFields.map Prod.fst) :
    CompleteValuePopulates schema resolvers variableValues (completionDepth + 2)
      parentType (executableFieldSelections fields)
      (.object runtimeType (some identity)) (.object previousFields) :=
  CompleteValuePopulates.object_of_visit_populates schema resolvers
    variableValues (completionDepth + 1) parentType runtimeType identity
    (executableFieldSelections fields) previousFields hincludes
    (VisitSubfieldsPopulates.of_executableFieldSelections_responseNamesNodup_object
      schema resolvers variableValues completionDepth runtimeType
      (.object runtimeType (some identity)) fields previousFields hparents hnodup
      hdisjoint)

theorem CompleteValuePopulates.object_executableFieldSelections_of_trace_fold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType runtimeType : Name)
    (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (previousFields : List (Name × Response))
    (hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true)
    (hparents :
      ∀ field, field ∈ fields -> field.parentType = runtimeType)
    (htracePrevious :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        (.object runtimeType (some identity)) fields (.object previousFields))
    (htraceEmpty :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        (.object runtimeType (some identity)) fields (.object []))
    (hfold :
      FieldSliceMergeFoldPopulates schema resolvers variableValues
        completionDepth (.object runtimeType (some identity)) fields
        (.object previousFields)) :
    CompleteValuePopulates schema resolvers variableValues (completionDepth + 2)
      parentType (executableFieldSelections fields)
      (.object runtimeType (some identity)) (.object previousFields) :=
  CompleteValuePopulates.object_of_visit_populates schema resolvers
    variableValues (completionDepth + 1) parentType runtimeType identity
    (executableFieldSelections fields) previousFields hincludes
    (VisitSubfieldsPopulates.of_executableFieldSelections_trace_fold schema
      resolvers variableValues completionDepth runtimeType
      (.object runtimeType (some identity)) fields (.object previousFields)
      hparents htracePrevious htraceEmpty hfold)

end ExecutionUngrouped
end Algorithms

end GraphQL
