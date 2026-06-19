import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Final
import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Reorder

/-!
Main proof-boundary constructors for reorder-normalized ungrouped execution.

These lemmas lift the local reorder theorem into the final grouped-state proof
API.  A normalized order that already proves grouped/spec equivalence can be
transported back to the original order when a later duplicate field is moved
left across a response-name-fresh middle block after its response key is already
populated by the prefix.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem visitFieldSliceFold_succ_single_empty_eq_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : Value ObjectIdentity)
    (field : ExecutableField) :
    visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source [field] (.object []) =
      .object
        [(field.responseName,
          responseFieldSlice schema resolvers variableValues completionDepth
            source field)] := by
  simp [visitFieldSliceFold, visitFieldSlice, responseFieldSlice,
    mergeResponseFieldIntoObject, mergeResponseField]

namespace ExecutedGroupedSelectionSetState

def of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × Response)}
    (normalized :
      ExecutedGroupedSelectionSetState schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix :
      visitFieldSliceFold schema resolvers variableValues
        (completionDepth + 1) source pre (.object []) =
      .object fields)
    (hparents :
      ∀ field, field ∈ pre ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest) (.object fields))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((later :: middle) ++ rest)))) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) :=
  { groups := normalized.groups
    collect_eq := by
      rw [hcollect]
      exact normalized.collect_eq
    flatCollects :=
      VisitSubfieldsFlatCollects_middle_existing_last_swap_after_prefix_of_traces
        schema resolvers variableValues completionDepth parentType source pre
        middle later rest fields hprefix hparents hlater hnotMiddle hleftTrace
        hrightTrace hcollect normalized.flatCollects
    flatSpec := normalized.flatSpec }

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × Response)}
    (normalized :
      ExecutedGroupedSelectionSetState schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix :
      visitFieldSliceFold schema resolvers variableValues
        (completionDepth + 1) source pre (.object []) =
      .object fields)
    (hparents :
      ∀ field, field ∈ pre ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest) (.object fields))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((later :: middle) ++ rest)))) :
    executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          (pre ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_prefix normalized hprefix hparents hlater
    hnotMiddle hleftTrace hrightTrace hcollect).executeRootSelectionSet_eq_spec

def of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized :
      ExecutedGroupedSelectionSetState schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((later :: middle) ++ rest)))) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections
        ([first] ++ ((middle ++ [later]) ++ rest))) :=
  of_middle_existing_last_swap_after_prefix normalized
    (visitFieldSliceFold_succ_single_empty_eq_object schema resolvers
      variableValues completionDepth source first)
    hparents
    (by simp [hsameResponse])
    hnotMiddle hleftTrace hrightTrace hcollect

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized :
      ExecutedGroupedSelectionSetState schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((later :: middle) ++ rest)))) :
    executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          ([first] ++ ((middle ++ [later]) ++ rest))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          ([first] ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_single_prefix normalized hsameResponse
    hparents hnotMiddle hleftTrace hrightTrace
    hcollect).executeRootSelectionSet_eq_spec

end ExecutedGroupedSelectionSetState

namespace RecursiveGroupedSelectionSetState

def of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × Response)}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix :
      visitFieldSliceFold schema resolvers variableValues
        (completionDepth + 1) source pre (.object []) =
      .object fields)
    (hparents :
      ∀ field, field ∈ pre ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest) (.object fields))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((later :: middle) ++ rest)))) :
    RecursiveGroupedSelectionSetState schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) :=
  { groups := normalized.groups
    collect_eq := by
      rw [hcollect]
      exact normalized.collect_eq
    flatCollects :=
      VisitSubfieldsFlatCollects_middle_existing_last_swap_after_prefix_of_traces
        schema resolvers variableValues completionDepth parentType source pre
        middle later rest fields hprefix hparents hlater hnotMiddle hleftTrace
        hrightTrace hcollect normalized.flatCollects
    collected :=
      { groupedResponseKeysUnique := by
          rw [hcollect]
          exact normalized.collected.groupedResponseKeysUnique
        groupedFieldsResolveStable := by
          rw [hcollect]
          exact normalized.collected.groupedFieldsResolveStable }
    compatible := normalized.compatible
    recursiveAppend := normalized.recursiveAppend }

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × Response)}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix :
      visitFieldSliceFold schema resolvers variableValues
        (completionDepth + 1) source pre (.object []) =
      .object fields)
    (hparents :
      ∀ field, field ∈ pre ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest) (.object fields))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            (pre ++ ((later :: middle) ++ rest)))) :
    executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          (pre ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_prefix normalized hprefix hparents hlater
    hnotMiddle hleftTrace hrightTrace hcollect).executeRootSelectionSet_eq_spec

def of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections
          ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((later :: middle) ++ rest)))) :
    RecursiveGroupedSelectionSetState schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections
        ([first] ++ ((middle ++ [later]) ++ rest))) :=
  of_middle_existing_last_swap_after_prefix normalized
    (visitFieldSliceFold_succ_single_empty_eq_object schema resolvers
      variableValues completionDepth source first)
    hparents
    (by simp [hsameResponse])
    hnotMiddle hleftTrace hrightTrace hcollect

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections
          ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ ((middle ++ [later]) ++ rest) ->
        field.parentType = parentType)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ rest)
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((middle ++ [later]) ++ rest))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections
            ([first] ++ ((later :: middle) ++ rest)))) :
    executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          ([first] ++ ((middle ++ [later]) ++ rest))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          ([first] ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_single_prefix normalized hsameResponse
    hparents hnotMiddle hleftTrace hrightTrace
    hcollect).executeRootSelectionSet_eq_spec

def of_middle_existing_last_swap_after_single_prefix_fresh_middle
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle : List ExecutableField}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections ([first] ++ [later] ++ middle)))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ (middle ++ [later]) ->
        field.parentType = parentType)
    (hmiddleNodup :
      (middle.map (fun field => field.responseName)).Nodup)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hpopulate :
      CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD
          later.fieldName)
        later.selectionSet
        (resolvers.resolve later.parentType later.fieldName later.arguments
          source)
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first))
    (hfirstReady :
      ResponseMergeReady
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ (middle ++ [later]))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ [later] ++ middle))) :
    RecursiveGroupedSelectionSetState schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections ([first] ++ (middle ++ [later]))) := by
  let firstSlice :=
    responseFieldSlice schema resolvers variableValues completionDepth source
      first
  have hlookup :
      responseObjectField? later.responseName
          (.object [(first.responseName, firstSlice)]) =
        some firstSlice := by
    simp [responseObjectField?, lookupResponseField?, hsameResponse]
  have hfreshOutput :
      ∀ field, field ∈ middle ->
        field.responseName ∉ [(first.responseName, firstSlice)].map
          Prod.fst := by
    intro field hfield hmem
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
    have hlaterField : later.responseName = field.responseName :=
      hsameResponse.trans hmem.symm
    exact hnotMiddle (List.mem_map.mpr ⟨field, hfield, hlaterField.symm⟩)
  have hleftTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source (middle ++ [later]) (.object [(first.responseName, firstSlice)]) :=
    FieldSliceMergeTrace.fresh_middle_then_reentry_object schema resolvers
      variableValues completionDepth source middle later
      [(first.responseName, firstSlice)] firstSlice hlookup hmiddleNodup
      hfreshOutput hnotMiddle (by simpa [firstSlice] using hpopulate)
      (by simpa [firstSlice] using hfirstReady)
  have hrightTrace :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source (later :: middle) (.object [(first.responseName, firstSlice)]) :=
    FieldSliceMergeTrace.reentry_then_fresh_middle_object schema resolvers
      variableValues completionDepth source middle later
      [(first.responseName, firstSlice)] firstSlice hlookup hmiddleNodup
      hfreshOutput hnotMiddle (by simpa [firstSlice] using hpopulate)
      (by simpa [firstSlice] using hfirstReady)
  have hleftTrace' :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((middle ++ [later]) ++ ([] : List ExecutableField))
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]) := by
    simpa [firstSlice, List.append_assoc] using hleftTrace
  have hrightTrace' :
      FieldSliceMergeTrace schema resolvers variableValues completionDepth
        source ((later :: middle) ++ ([] : List ExecutableField))
        (.object
          [(first.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source first)]) := by
    simpa [firstSlice, List.append_assoc] using hrightTrace
  have normalized' :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections
          ([first] ++ ((later :: middle) ++ ([] : List ExecutableField)))) := by
    simpa [List.append_assoc] using normalized
  simpa [firstSlice, List.append_assoc] using
    of_middle_existing_last_swap_after_single_prefix
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source) (first := first)
      (later := later) (middle := middle) (rest := []) normalized'
      hsameResponse (by simpa [List.append_assoc] using hparents)
      hnotMiddle hleftTrace' hrightTrace'
      (by simpa [List.append_assoc] using hcollect)

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_single_prefix_fresh_middle
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle : List ExecutableField}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections ([first] ++ [later] ++ middle)))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ (middle ++ [later]) ->
        field.parentType = parentType)
    (hmiddleNodup :
      (middle.map (fun field => field.responseName)).Nodup)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hpopulate :
      CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD
          later.fieldName)
        later.selectionSet
        (resolvers.resolve later.parentType later.fieldName later.arguments
          source)
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first))
    (hfirstReady :
      ResponseMergeReady
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first))
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ (middle ++ [later]))) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ [later] ++ middle))) :
    executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ([first] ++ (middle ++ [later]))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ([first] ++ (middle ++ [later]))) :=
  (of_middle_existing_last_swap_after_single_prefix_fresh_middle normalized
    hsameResponse hparents hmiddleNodup hnotMiddle hpopulate hfirstReady
    hcollect).executeRootSelectionSet_eq_spec

def of_middle_existing_last_swap_after_single_prefix_fresh_middle_collected
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle : List ExecutableField}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections ([first] ++ [later] ++ middle)))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ (middle ++ [later]) ->
        field.parentType = parentType)
    (hmiddleNodup :
      (middle.map (fun field => field.responseName)).Nodup)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hpopulate :
      CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD
          later.fieldName)
        later.selectionSet
        (resolvers.resolve later.parentType later.fieldName later.arguments
          source)
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first))
    (hfirstReady :
      ResponseMergeReady
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first)) :
    RecursiveGroupedSelectionSetState schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections ([first] ++ (middle ++ [later]))) :=
  of_middle_existing_last_swap_after_single_prefix_fresh_middle normalized
    hsameResponse hparents hmiddleNodup hnotMiddle hpopulate hfirstReady
    (collectFields_executableFieldSelections_single_prefix_duplicate_fresh_middle
      schema variableValues parentType source first later middle hsameResponse
      hmiddleNodup
      (by
        intro field hfield
        exact hparents field (by simp [hfield]))
      hnotMiddle)

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_single_prefix_fresh_middle_collected
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : Value ObjectIdentity}
    {first later : ExecutableField} {middle : List ExecutableField}
    (normalized :
      RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections ([first] ++ [later] ++ middle)))
    (hsameResponse : later.responseName = first.responseName)
    (hparents :
      ∀ field, field ∈ [first] ++ (middle ++ [later]) ->
        field.parentType = parentType)
    (hmiddleNodup :
      (middle.map (fun field => field.responseName)).Nodup)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName))
    (hpopulate :
      CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD
          later.fieldName)
        later.selectionSet
        (resolvers.resolve later.parentType later.fieldName later.arguments
          source)
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first))
    (hfirstReady :
      ResponseMergeReady
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first)) :
    executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ([first] ++ (middle ++ [later]))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ([first] ++ (middle ++ [later]))) :=
  (of_middle_existing_last_swap_after_single_prefix_fresh_middle_collected
    normalized hsameResponse hparents hmiddleNodup hnotMiddle hpopulate
    hfirstReady).executeRootSelectionSet_eq_spec

end RecursiveGroupedSelectionSetState

end ExecutionUngrouped
end Algorithms

end GraphQL
