import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.TwoField

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem executeRootSelectionSet_executableFieldSelections_duplicate_eq_spec_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hobjects :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) firstSelectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) secondSelectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) firstSelectionSet
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := firstSelectionSet ++ secondSelectionSet }
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      (executableFieldSelections
        [ executableField parentType responseName fieldName arguments
            firstSelectionSet
        , executableField parentType responseName fieldName arguments
            secondSelectionSet ]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (executableFieldSelections
        [ executableField parentType responseName fieldName arguments
            firstSelectionSet
        , executableField parentType responseName fieldName arguments
            secondSelectionSet ]) := by
  apply
    executeRootSelectionSet_executableFieldSelections_duplicate_eq_spec_of_completeValue_merge
      schema resolvers variableValues depth parentType source responseName
      fieldName arguments firstSelectionSet secondSelectionSet resolved
      hresolve
  exact completeValue_duplicate_merge_eq_spec_of_visit_absorbs schema
    resolvers variableValues depth parentType responseName fieldName arguments
    firstSelectionSet secondSelectionSet resolved hobjects hchildren

theorem completeValue_object_list_single_field_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (fieldParentType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection)
    (objects : List (Name × ObjectIdentity))
    (hchildren :
      ∀ object, object ∈ objects ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := object.fst
              source := .object object.fst object.snd
              selectionSet := selectionSet }
            initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 2)
      ((schema.fieldReturnType? fieldParentType fieldName).getD fieldName)
      selectionSet
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : Value ObjectIdentity))))
      .null =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 2)
      ((schema.fieldReturnType? fieldParentType fieldName).getD fieldName)
      [executableField fieldParentType responseName fieldName arguments
        selectionSet]
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : Value ObjectIdentity)))) := by
  apply completeValue_list_empty_previous_eq_spec_of_values schema resolvers
    variableValues (childDepth + 1)
    ((schema.fieldReturnType? fieldParentType fieldName).getD fieldName)
    selectionSet
    [executableField fieldParentType responseName fieldName arguments
      selectionSet]
  intro value hmem
  rcases List.mem_map.mp hmem with ⟨object, hobject, hvalue⟩
  rw [← hvalue]
  exact completeValue_object_single_field_eq_spec_of_child_state schema
    resolvers variableValues childDepth fieldParentType object.fst object.snd
    responseName fieldName arguments selectionSet
    (hchildren object hobject)

theorem executeRootSelectionSet_single_list_field_succ_eq_spec_of_values
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (values : List (Value ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .list values)
    (hvalues :
      ∀ value, value ∈ values ->
        completeValue schema resolvers variableValues childDepth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          selectionSet value .null =
        GraphQL.Execution.completeValue schema resolvers variableValues childDepth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          [executableField parentType responseName fieldName arguments
            selectionSet]
          value) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues (childDepth + 1) parentType source responseName
    fieldName arguments directives selectionSet hallowed
  rw [hresolve]
  exact completeValue_list_empty_previous_eq_spec_of_values schema resolvers
    variableValues childDepth
    ((schema.fieldReturnType? parentType fieldName).getD fieldName)
    selectionSet
    [executableField parentType responseName fieldName arguments selectionSet]
    values hvalues

theorem executeRootSelectionSet_single_object_list_field_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (objects : List (Name × ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .list
          (objects.map
            (fun object =>
              (.object object.fst object.snd : Value ObjectIdentity))))
    (hchildren :
      ∀ object, object ∈ objects ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := object.fst
              source := .object object.fst object.snd
              selectionSet := selectionSet }
            initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 3)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 3) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues (childDepth + 2) parentType source
    responseName fieldName arguments directives selectionSet hallowed
  rw [hresolve]
  exact completeValue_object_list_single_field_eq_spec_of_child_states schema
    resolvers variableValues childDepth parentType responseName fieldName
    arguments selectionSet objects hchildren

theorem executeRootSelectionSet_single_scalar_field_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (value : String)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .scalar value) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  cases depth <;>
    simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
      completeValue, GraphQL.Execution.executeRootSelectionSet,
      GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      GraphQL.Execution.mergeExecutableGroups,
      GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
      GraphQL.Execution.completeValue, executableField, responseObjectField?,
      lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
      shallowResponse, hallowed, hresolve]

theorem executeRootSelectionSet_duplicate_scalar_field_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (value : String)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .scalar value) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] := by
  apply executeRootSelectionSet_duplicate_field_succ_eq_spec_of_completeValue_merge
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives firstSelectionSet secondSelectionSet
    (.scalar value) hallowed hresolve
  exact completeValue_duplicate_scalar_merge_eq_spec schema resolvers
    variableValues depth
    ((schema.fieldReturnType? parentType fieldName).getD fieldName)
    firstSelectionSet secondSelectionSet
    [ executableField parentType responseName fieldName arguments
        firstSelectionSet
    , executableField parentType responseName fieldName arguments
        secondSelectionSet ]
    value

theorem executeRootSelectionSet_single_null_field_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        (.null : Value ObjectIdentity)) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  cases depth <;>
    simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
      completeValue, GraphQL.Execution.executeRootSelectionSet,
      GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      GraphQL.Execution.mergeExecutableGroups,
      GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
      GraphQL.Execution.completeValue, executableField, responseObjectField?,
      lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
      shallowResponse, hallowed, hresolve]

theorem executeRootSelectionSet_duplicate_null_field_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        (.null : Value ObjectIdentity)) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] := by
  apply executeRootSelectionSet_duplicate_field_succ_eq_spec_of_completeValue_merge
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives firstSelectionSet secondSelectionSet
    .null hallowed hresolve
  exact completeValue_duplicate_null_merge_eq_spec schema resolvers
    variableValues depth
    ((schema.fieldReturnType? parentType fieldName).getD fieldName)
    firstSelectionSet secondSelectionSet
    [ executableField parentType responseName fieldName arguments
        firstSelectionSet
    , executableField parentType responseName fieldName arguments
        secondSelectionSet ]

theorem executeRootSelectionSet_single_empty_list_field_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .list ([] : List (Value ObjectIdentity))) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  cases depth <;>
    simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
      completeValue, GraphQL.Execution.executeRootSelectionSet,
      GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      GraphQL.Execution.mergeExecutableGroups,
      GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
      GraphQL.Execution.completeValue, executableField, responseObjectField?,
      lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
      shallowResponse, hallowed, hresolve]

theorem executeRootSelectionSet_single_scalar_list_field_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (value : String)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .list [(.scalar value : Value ObjectIdentity)]) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  cases depth with
  | zero =>
      simp [executeRootSelectionSet, visitSubfields, visitSelection,
        executeField, completeValue, GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
        GraphQL.Execution.completeValue, executableField, responseObjectField?,
        lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
        hallowed, hresolve]
  | succ depth =>
      simp [executeRootSelectionSet, visitSubfields, visitSelection,
        executeField, completeValue, GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
        GraphQL.Execution.completeValue, executableField, responseObjectField?,
        lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
        hallowed, hresolve]
      exact completeValue_scalar_any_depth_eq_spec schema resolvers
        variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        selectionSet
        [{ parentType := parentType, responseName := responseName,
           fieldName := fieldName, arguments := arguments,
           selectionSet := selectionSet }]
        value .null

theorem executeRootSelectionSet_single_scalar_values_list_field_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (values : List String)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .list (values.map (fun value =>
          (.scalar value : Value ObjectIdentity)))) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  cases depth with
  | zero =>
      simp [executeRootSelectionSet, visitSubfields, visitSelection,
        executeField, completeValue, GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
        GraphQL.Execution.completeValue, executableField, responseObjectField?,
        lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
        hallowed, hresolve]
  | succ depth =>
      simp [executeRootSelectionSet, visitSubfields, visitSelection,
        executeField, GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
        executableField, responseObjectField?, lookupResponseField?,
        mergeResponseFieldIntoObject, mergeResponseField, hallowed, hresolve]
      exact completeValue_scalar_list_eq_spec schema resolvers variableValues
        depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        selectionSet
        [{ parentType := parentType, responseName := responseName,
           fieldName := fieldName, arguments := arguments,
           selectionSet := selectionSet }]
        values .null

theorem duplicate_object_child_merge_of_append_state_and_absorb
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ secondSelectionSet }
          initial := .object [] })
    (habsorb :
      mergeResponse
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object []))) =
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType (some identity)) secondSelectionSet
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))) :
      mergeResponse
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object []))) =
      .object
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues childDepth (.object runtimeType (some identity))
          (GraphQL.Execution.collectSubfields schema variableValues runtimeType
            (.object runtimeType (some identity))
            [ executableField parentType responseName fieldName arguments
                firstSelectionSet
            , executableField parentType responseName fieldName arguments
                secondSelectionSet ])) := by
  unfold ExecutionStateEquivalent ResponseDataEquivalent at hstate
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection,
    mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        childDepth (.object runtimeType (some identity))
        (GraphQL.Execution.collectFields schema variableValues runtimeType
          (.object runtimeType (some identity)) (firstSelectionSet ++ secondSelectionSet)))
      (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
        variableValues childDepth runtimeType (.object runtimeType (some identity))
        (firstSelectionSet ++ secondSelectionSet))] at hstate
  rw [habsorb]
  rw [← visitSubfields_append_equivalence schema resolvers variableValues childDepth
    runtimeType (.object runtimeType (some identity)) firstSelectionSet
    secondSelectionSet (.object [])]
  simpa [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
    GraphQL.Execution.mergedFieldSelectionSet, executableField] using hstate

theorem duplicate_object_child_merge_of_append_state_and_response_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ secondSelectionSet }
          initial := .object [] })
    (hpreviousObject :
      ∃ previousFields,
        visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []) =
        .object previousFields)
    (habsorb :
      ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
      mergeResponse
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object []))) =
      .object
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues childDepth (.object runtimeType (some identity))
          (GraphQL.Execution.collectSubfields schema variableValues runtimeType
            (.object runtimeType (some identity))
            [ executableField parentType responseName fieldName arguments
                firstSelectionSet
            , executableField parentType responseName fieldName arguments
                secondSelectionSet ])) := by
  apply duplicate_object_child_merge_of_append_state_and_absorb
    schema resolvers variableValues childDepth parentType runtimeType identity
    responseName fieldName arguments firstSelectionSet secondSelectionSet hstate
  rcases hpreviousObject with ⟨previousFields, hpreviousObject⟩
  rw [hpreviousObject] at habsorb ⊢
  unfold ResponseAbsorbs at habsorb
  rw [habsorb]
  simp [completeValue, hincludes]

theorem duplicate_object_child_merge_of_append_state_and_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ secondSelectionSet }
          initial := .object [] })
    (hpreviousObject :
      ∃ previousFields,
        visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []) =
        .object previousFields)
    (hvisitAbsorb :
      ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) secondSelectionSet
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
      mergeResponse
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object []))) =
      .object
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues childDepth (.object runtimeType (some identity))
          (GraphQL.Execution.collectSubfields schema variableValues runtimeType
            (.object runtimeType (some identity))
            [ executableField parentType responseName fieldName arguments
                firstSelectionSet
            , executableField parentType responseName fieldName arguments
                secondSelectionSet ])) := by
  apply duplicate_object_child_merge_of_append_state_and_response_absorbs
    schema resolvers variableValues childDepth parentType runtimeType identity
    responseName fieldName arguments firstSelectionSet secondSelectionSet
    hincludes hstate hpreviousObject
  rcases hpreviousObject with ⟨previousFields, hpreviousObject⟩
  rw [hpreviousObject] at hvisitAbsorb ⊢
  simpa [completeValue, hincludes] using hvisitAbsorb

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hchild :
      mergeResponse
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object []))) =
      .object
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues childDepth (.object runtimeType (some identity))
          (GraphQL.Execution.collectSubfields schema variableValues runtimeType
            (.object runtimeType (some identity))
            [ executableField parentType responseName fieldName arguments
                firstSelectionSet
            , executableField parentType responseName fieldName arguments
                secondSelectionSet ]))) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] := by
  apply executeRootSelectionSet_duplicate_field_succ_eq_spec_of_completeValue_merge
    schema resolvers variableValues (childDepth + 1) parentType source
    responseName fieldName arguments directives firstSelectionSet
    secondSelectionSet (.object runtimeType (some identity)) hallowed hresolve
  exact completeValue_duplicate_object_merge_eq_spec_of_child_merge schema
    resolvers variableValues childDepth parentType runtimeType identity
    responseName fieldName arguments firstSelectionSet secondSelectionSet
    hincludes hchild

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ secondSelectionSet }
          initial := .object [] })
    (hpreviousObject :
      ∃ previousFields,
        visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []) =
        .object previousFields)
    (habsorb :
      ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] :=
  executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_merge
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives firstSelectionSet
    secondSelectionSet hallowed hresolve hincludes
    (duplicate_object_child_merge_of_append_state_and_response_absorbs
      schema resolvers variableValues childDepth parentType runtimeType identity
      responseName fieldName arguments firstSelectionSet secondSelectionSet
      hincludes hstate hpreviousObject habsorb)

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ secondSelectionSet }
          initial := .object [] })
    (habsorb :
      ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] :=
  executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_state
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives firstSelectionSet
    secondSelectionSet hallowed hresolve hincludes hstate
    (visitSubfields_preserves_object schema resolvers variableValues childDepth
      runtimeType (.object runtimeType (some identity)) firstSelectionSet [])
    habsorb

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ secondSelectionSet }
          initial := .object [] })
    (hvisitAbsorb :
      ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) secondSelectionSet
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] :=
  executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_merge
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives firstSelectionSet
    secondSelectionSet hallowed hresolve hincludes
    (duplicate_object_child_merge_of_append_state_and_visit_absorbs
      schema resolvers variableValues childDepth parentType runtimeType identity
      responseName fieldName arguments firstSelectionSet secondSelectionSet
      hincludes hstate
      (visitSubfields_preserves_object schema resolvers variableValues
        childDepth runtimeType (.object runtimeType (some identity)) firstSelectionSet [])
      hvisitAbsorb)

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_absorption_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ secondSelectionSet }
          initial := .object [] })
    (hsteps :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        secondSelectionSet
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] :=
  executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_visit_absorbs
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives firstSelectionSet
    secondSelectionSet hallowed hresolve hincludes hstate
    (visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType (some identity))
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType (some identity)) firstSelectionSet (.object []))
      secondSelectionSet
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType (some identity)) firstSelectionSet (.object []))
      hsteps)

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_empty_later_slice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet }
          initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives [] ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives [] ] := by
  apply executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_visit_absorbs
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives firstSelectionSet []
    hallowed hresolve hincludes
  · simpa using hstate
  · apply visitSubfields_nil_absorbs_of_ready
    exact visitSubfields_response_ready schema resolvers variableValues
      childDepth runtimeType (.object runtimeType (some identity)) firstSelectionSet []
      ResponseMergeReady_empty_object

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_empty_first_slice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (secondSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := secondSelectionSet }
          initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives []
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives []
      , .field responseName fieldName arguments directives secondSelectionSet ] := by
  apply executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_visit_absorbs
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives [] secondSelectionSet
    hallowed hresolve hincludes
  · simpa using hstate
  · simp [visitSubfields]
    obtain ⟨outputFields, houtputFields⟩ :=
      visitSubfields_preserves_object schema resolvers variableValues
        childDepth runtimeType (.object runtimeType (some identity))
        secondSelectionSet []
    rw [houtputFields]
    apply ResponseAbsorbs_empty_object_left
    simpa [houtputFields] using
      visitSubfields_pairKeysNodup schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity)) secondSelectionSet []
        (by simp [PairKeysNodup])

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_single_later_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (grandChildDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet : List Selection)
    (childResponseName childFieldName : Name)
    (childArguments : List Argument) (childDirectives : List DirectiveApplication)
    (childSelectionSet : List Selection)
    (previousFields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hchildAllowed :
      selectionDirectivesAllowBool variableValues childDirectives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := grandChildDepth + 1
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet :=
              firstSelectionSet ++
                [.field childResponseName childFieldName childArguments
                  childDirectives childSelectionSet] }
          initial := .object [] })
    (hpreviousObject :
      visitSubfields schema resolvers variableValues (grandChildDepth + 1)
        runtimeType (.object runtimeType (some identity)) firstSelectionSet
        (.object []) =
      .object previousFields)
    (hcollisionAbsorbs :
      ∀ existing,
        (childResponseName, existing) ∈ previousFields ->
          ResponseAbsorbs existing
            (mergeResponse existing
              (executeField schema resolvers variableValues grandChildDepth
                (.object runtimeType (some identity)) (.object previousFields)
                (executableField runtimeType childResponseName childFieldName
                  childArguments childSelectionSet)))) :
    executeRootSelectionSet schema resolvers variableValues (grandChildDepth + 3)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives
          [.field childResponseName childFieldName childArguments
            childDirectives childSelectionSet] ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (grandChildDepth + 3) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives
          [.field childResponseName childFieldName childArguments
            childDirectives childSelectionSet] ] := by
  apply
    executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_absorption_steps
      schema resolvers variableValues (grandChildDepth + 1) parentType
      runtimeType identity source responseName fieldName arguments directives
      firstSelectionSet
      [.field childResponseName childFieldName childArguments childDirectives
        childSelectionSet]
      hallowed hresolve hincludes hstate
  rw [hpreviousObject]
  apply VisitSubfieldsAbsorbsFrom_single_field_allowed_succ
    schema resolvers variableValues grandChildDepth runtimeType
    (.object runtimeType (some identity)) childResponseName childFieldName
    childArguments childDirectives childSelectionSet previousFields
    hchildAllowed
  · simpa [hpreviousObject] using
      visitSubfields_response_ready schema resolvers variableValues
        (grandChildDepth + 1) runtimeType (.object runtimeType (some identity))
        firstSelectionSet [] ResponseMergeReady_empty_object
  · exact hcollisionAbsorbs

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_fresh_later_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (grandChildDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet : List Selection)
    (childResponseName childFieldName : Name)
    (childArguments : List Argument) (childDirectives : List DirectiveApplication)
    (childSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hchildAllowed :
      selectionDirectivesAllowBool variableValues childDirectives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := grandChildDepth + 1
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet :=
              firstSelectionSet ++
                [.field childResponseName childFieldName childArguments
                  childDirectives childSelectionSet] }
          initial := .object [] })
    (hfresh :
      ∀ previousFields,
        visitSubfields schema resolvers variableValues (grandChildDepth + 1)
          runtimeType (.object runtimeType (some identity)) firstSelectionSet
          (.object []) =
        .object previousFields ->
          childResponseName ∉ previousFields.map Prod.fst) :
    executeRootSelectionSet schema resolvers variableValues (grandChildDepth + 3)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives
          [.field childResponseName childFieldName childArguments
            childDirectives childSelectionSet] ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (grandChildDepth + 3) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives
          [.field childResponseName childFieldName childArguments
            childDirectives childSelectionSet] ] := by
  obtain ⟨previousFields, hpreviousObject⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (grandChildDepth + 1) runtimeType (.object runtimeType (some identity))
      firstSelectionSet []
  apply
    executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_absorption_steps
      schema resolvers variableValues (grandChildDepth + 1) parentType
      runtimeType identity source responseName fieldName arguments directives
      firstSelectionSet
      [.field childResponseName childFieldName childArguments childDirectives
        childSelectionSet]
      hallowed hresolve hincludes hstate
  rw [hpreviousObject]
  apply VisitSubfieldsAbsorbsFrom_single_field_allowed_succ_of_fresh
    schema resolvers variableValues grandChildDepth runtimeType
    (.object runtimeType (some identity)) childResponseName childFieldName
    childArguments childDirectives childSelectionSet previousFields
    hchildAllowed
    (hfresh previousFields hpreviousObject)
  simpa [hpreviousObject] using
    visitSubfields_response_ready schema resolvers variableValues
      (grandChildDepth + 1) runtimeType (.object runtimeType (some identity))
      firstSelectionSet [] ResponseMergeReady_empty_object

theorem stateEquivalent_of_duplicate_object_field_succ_of_fresh_later_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (grandChildDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet : List Selection)
    (childResponseName childFieldName : Name)
    (childArguments : List Argument) (childDirectives : List DirectiveApplication)
    (childSelectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hchildAllowed :
      selectionDirectivesAllowBool variableValues childDirectives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := grandChildDepth + 1
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet :=
              firstSelectionSet ++
                [.field childResponseName childFieldName childArguments
                  childDirectives childSelectionSet] }
          initial := .object [] })
    (hfresh :
      ∀ previousFields,
        visitSubfields schema resolvers variableValues (grandChildDepth + 1)
          runtimeType (.object runtimeType (some identity)) firstSelectionSet
          (.object []) =
        .object previousFields ->
          childResponseName ∉ previousFields.map Prod.fst) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := grandChildDepth + 3
          parentType := parentType
          source := source
          selectionSet :=
            [ .field responseName fieldName arguments directives firstSelectionSet
            , .field responseName fieldName arguments directives
                [.field childResponseName childFieldName childArguments
                  childDirectives childSelectionSet] ] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (grandChildDepth + 3) parentType source
    [ .field responseName fieldName arguments directives firstSelectionSet
    , .field responseName fieldName arguments directives
        [.field childResponseName childFieldName childArguments childDirectives
          childSelectionSet] ]
    (executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_fresh_later_field
      schema resolvers variableValues grandChildDepth parentType runtimeType
      identity source responseName fieldName arguments directives
      firstSelectionSet childResponseName childFieldName childArguments
      childDirectives childSelectionSet hallowed hchildAllowed hresolve
      hincludes hstate hfresh)

theorem VisitSubfieldsAbsorbsFrom_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (base : Response) (selection : Selection)
    (rest : List Selection) (current : Response) :
    let next :=
      visitSelection schema resolvers variableValues depth parentType source
        selection current
    ResponseAbsorbs base next ->
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source base rest next ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
        source base (selection :: rest) current := by
  intro next hstep hrest
  exact ⟨hstep, hrest⟩

theorem VisitSubfieldsAbsorbsFrom_cons_field_allowed_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
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
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues (depth + 1)
      parentType source (.object fields) rest
      (visitSelection schema resolvers variableValues (depth + 1)
        parentType source
        (.field responseName fieldName arguments directives selectionSet)
        (.object fields)) ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues (depth + 1)
        parentType source (.object fields)
        (.field responseName fieldName arguments directives selectionSet :: rest)
        (.object fields) := by
  intro hfieldsReady hcollisionAbsorbs hrest
  apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues
    (depth + 1) parentType source (.object fields)
  · exact visitSelection_field_allowed_succ_absorbs schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfieldsReady hcollisionAbsorbs
  · exact hrest

theorem VisitSubfieldsAbsorbsFrom_cons_field_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output rest output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
        source output
        (.field responseName fieldName arguments directives selectionSet :: rest)
        output := by
  intro hready hrest
  apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues depth
    parentType source output
  · exact visitSelection_field_blocked_absorbs_of_ready schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet output hblocked hready
  · simpa [visitSelection_field_directives_blocked schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet output hblocked] using hrest

theorem VisitSubfieldsAbsorbsFrom_cons_inline_none_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output rest output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
        source output (.inlineFragment none directives selectionSet :: rest)
        output := by
  intro hready hrest
  apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues depth
    parentType source output
  · exact visitSelection_inline_none_blocked_absorbs_of_ready schema resolvers
      variableValues depth parentType source directives selectionSet output
      hblocked hready
  · simpa [visitSelection_inline_none_directives_blocked schema resolvers
      variableValues depth parentType source directives selectionSet output
      hblocked] using hrest

theorem VisitSubfieldsAbsorbsFrom_cons_inline_some_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output rest output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
        source output
        (.inlineFragment (some typeCondition) directives selectionSet :: rest)
        output := by
  intro hready hrest
  apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues depth
    parentType source output
  · exact visitSelection_inline_some_blocked_absorbs_of_ready schema resolvers
      variableValues depth parentType source typeCondition directives
      selectionSet output hblocked hready
  · simpa [visitSelection_inline_some_directives_blocked schema resolvers
      variableValues depth parentType source typeCondition directives
      selectionSet output hblocked] using hrest

theorem VisitSubfieldsAbsorbsFrom_cons_inline_none_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output selectionSet output ->
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output rest
      (visitSubfields schema resolvers variableValues depth parentType source
        selectionSet output) ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
        source output (.inlineFragment none directives selectionSet :: rest)
        output := by
  intro hselectionSet hrest
  apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues depth
    parentType source output
  · simpa [visitSelection, hallowed] using
      visitSubfields_absorbs_from_steps schema resolvers variableValues
        depth parentType source output selectionSet output hselectionSet
  · simpa [visitSelection, hallowed] using hrest

theorem VisitSubfieldsAbsorbsFrom_cons_inline_some_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition = false) :
    ResponseMergeReady output ->
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output rest output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
        source output
        (.inlineFragment (some typeCondition) directives selectionSet :: rest)
        output := by
  intro hready hrest
  apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues depth
    parentType source output
  · exact visitSelection_inline_some_not_apply_absorbs_of_ready schema
      resolvers variableValues depth parentType source typeCondition directives
      selectionSet output hallowed hnotApply hready
  · simpa [visitSelection_inline_some_type_not_apply schema resolvers
      variableValues depth parentType source typeCondition directives
      selectionSet output hallowed hnotApply] using hrest

theorem VisitSubfieldsAbsorbsFrom_cons_inline_some_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition = true) :
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output selectionSet output ->
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
      source output rest
      (visitSubfields schema resolvers variableValues depth parentType source
        selectionSet output) ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth parentType
        source output
        (.inlineFragment (some typeCondition) directives selectionSet :: rest)
        output := by
  intro hselectionSet hrest
  apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues depth
    parentType source output
  · simpa [visitSelection, hallowed, happly] using
      visitSubfields_absorbs_from_steps schema resolvers variableValues
        depth parentType source output selectionSet output hselectionSet
  · simpa [visitSelection, hallowed, happly] using hrest

theorem VisitSubfieldsAbsorbsFrom_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (base : Response) :
    ∀ (left right : List Selection) (current : Response),
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source base left current ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source base right
        (visitSubfields schema resolvers variableValues depth parentType source
          left current) ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source base (left ++ right) current
  | [], right, current, _hleft, hright => by
      simpa [visitSubfields] using hright
  | selection :: rest, right, current, hleft, hright => by
      simp [VisitSubfieldsAbsorbsFrom] at hleft
      rcases hleft with ⟨hselection, hrest⟩
      apply VisitSubfieldsAbsorbsFrom_cons schema resolvers variableValues
        depth parentType source base selection (rest ++ right) current
      · exact hselection
      · apply VisitSubfieldsAbsorbsFrom_append schema resolvers variableValues
          depth parentType source base rest right
        · exact hrest
        · simpa [visitSubfields] using hright

theorem executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_later_append_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet laterLeft laterRight : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ (laterLeft ++ laterRight) }
          initial := .object [] })
    (hleft :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterLeft
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object [])))
    (hright :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterRight
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) laterLeft
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives
          (laterLeft ++ laterRight) ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives
          (laterLeft ++ laterRight) ] := by
  apply
    executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_child_absorption_steps
      schema resolvers variableValues childDepth parentType runtimeType
      identity source responseName fieldName arguments directives
      firstSelectionSet (laterLeft ++ laterRight) hallowed hresolve hincludes
      hstate
  apply VisitSubfieldsAbsorbsFrom_append schema resolvers variableValues
    childDepth runtimeType (.object runtimeType (some identity))
    (visitSubfields schema resolvers variableValues childDepth runtimeType
      (.object runtimeType (some identity)) firstSelectionSet (.object []))
    laterLeft laterRight
  · exact hleft
  · exact hright

theorem stateEquivalent_of_duplicate_object_field_succ_of_later_append_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet laterLeft laterRight : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet ++ (laterLeft ++ laterRight) }
          initial := .object [] })
    (hleft :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterLeft
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object [])))
    (hright :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterRight
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) laterLeft
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := childDepth + 2
          parentType := parentType
          source := source
          selectionSet :=
            [ .field responseName fieldName arguments directives firstSelectionSet
            , .field responseName fieldName arguments directives
                (laterLeft ++ laterRight) ] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (childDepth + 2) parentType source
    [ .field responseName fieldName arguments directives firstSelectionSet
    , .field responseName fieldName arguments directives
        (laterLeft ++ laterRight) ]
    (executeRootSelectionSet_duplicate_object_field_succ_eq_spec_of_later_append_steps
      schema resolvers variableValues childDepth parentType runtimeType
      identity source responseName fieldName arguments directives
      firstSelectionSet laterLeft laterRight hallowed hresolve hincludes
      hstate hleft hright)

theorem stateEquivalent_of_duplicate_object_field_succ_of_later_append_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet laterLeft laterRight : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hfirst :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet }
          initial := .object [] })
    (happend :
      AppendSelectionSetState schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity)) firstSelectionSet
        (laterLeft ++ laterRight))
    (hleft :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterLeft
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object [])))
    (hright :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterRight
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) laterLeft
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := childDepth + 2
          parentType := parentType
          source := source
          selectionSet :=
            [ .field responseName fieldName arguments directives firstSelectionSet
            , .field responseName fieldName arguments directives
                (laterLeft ++ laterRight) ] }
        initial := .object [] } :=
  stateEquivalent_of_duplicate_object_field_succ_of_later_append_steps
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives firstSelectionSet
    laterLeft laterRight hallowed hresolve hincludes
    (stateEquivalent_of_append_selectionSet_state firstSelectionSet
      (laterLeft ++ laterRight) hfirst happend)
    hleft hright

theorem stateEquivalent_of_duplicate_object_field_succ_of_later_prefix_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet laterLeft laterRight : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hfirst :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := firstSelectionSet }
          initial := .object [] })
    (happend :
      AppendSelectionSetPrefixState schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity)) firstSelectionSet
        (laterLeft ++ laterRight))
    (hleft :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterLeft
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object [])))
    (hright :
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
        runtimeType (.object runtimeType (some identity))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        laterRight
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) laterLeft
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object [])))) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := childDepth + 2
          parentType := parentType
          source := source
          selectionSet :=
            [ .field responseName fieldName arguments directives firstSelectionSet
            , .field responseName fieldName arguments directives
                (laterLeft ++ laterRight) ] }
        initial := .object [] } :=
  stateEquivalent_of_duplicate_object_field_succ_of_later_append_state
    schema resolvers variableValues childDepth parentType runtimeType identity
    source responseName fieldName arguments directives firstSelectionSet
    laterLeft laterRight hallowed hresolve hincludes hfirst
    (AppendSelectionSetState.of_prefix_state firstSelectionSet
      (laterLeft ++ laterRight) happend)
    hleft hright

theorem executeRootSelectionSet_single_object_field_succ_eq_spec_of_child
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := selectionSet }
          initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  unfold ExecutionStateEquivalent ResponseDataEquivalent at hchild
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection,
    mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        childDepth (.object runtimeType (some identity))
        (GraphQL.Execution.collectFields schema variableValues runtimeType
          (.object runtimeType (some identity)) selectionSet))
      (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
        variableValues childDepth runtimeType (.object runtimeType (some identity))
        selectionSet)] at hchild
  simp [executeRootSelectionSet, visitSubfields, visitSelection,
    executeField, completeValue, GraphQL.Execution.executeRootSelectionSet,
    GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups,
    GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
    GraphQL.Execution.completeValue, executableField, responseObjectField?,
    lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
    hallowed, hresolve, hincludes] at hchild ⊢
  simpa using hchild

theorem executeRootSelectionSet_scalar_then_object_field_succ_eq_spec_of_child
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (scalarResponseName scalarFieldName : Name)
    (scalarArguments : List Argument)
    (scalarDirectives : List DirectiveApplication)
    (scalarSelectionSet : List Selection)
    (scalarValue : String)
    (objectResponseName objectFieldName : Name)
    (objectArguments : List Argument)
    (objectDirectives : List DirectiveApplication)
    (objectSelectionSet : List Selection)
    (hscalarAllowed :
      selectionDirectivesAllowBool variableValues scalarDirectives = true)
    (hobjectAllowed :
      selectionDirectivesAllowBool variableValues objectDirectives = true)
    (hscalarResolve :
      resolvers.resolve parentType scalarFieldName scalarArguments source =
        .scalar scalarValue)
    (hobjectResolve :
      resolvers.resolve parentType objectFieldName objectArguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType objectFieldName).getD
          objectFieldName)
        runtimeType = true)
    (hdistinct : (scalarResponseName == objectResponseName) = false)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := objectSelectionSet }
          initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field scalarResponseName scalarFieldName scalarArguments
          scalarDirectives scalarSelectionSet
      , .field objectResponseName objectFieldName objectArguments
          objectDirectives objectSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field scalarResponseName scalarFieldName scalarArguments
          scalarDirectives scalarSelectionSet
      , .field objectResponseName objectFieldName objectArguments
          objectDirectives objectSelectionSet ] := by
  unfold ExecutionStateEquivalent ResponseDataEquivalent at hchild
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection,
    mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        childDepth (.object runtimeType (some identity))
        (GraphQL.Execution.collectFields schema variableValues runtimeType
          (.object runtimeType (some identity)) objectSelectionSet))
      (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
        variableValues childDepth runtimeType (.object runtimeType (some identity))
        objectSelectionSet)] at hchild
  simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
    completeValue, GraphQL.Execution.executeRootSelectionSet,
    GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups,
    GraphQL.Execution.addExecutableGroup,
    GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
    GraphQL.Execution.completeValue, executableField, responseObjectField?,
    lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
    hscalarAllowed, hobjectAllowed, hscalarResolve, hobjectResolve, hincludes,
    hdistinct] at hchild ⊢
  simpa using hchild

theorem stateEquivalent_of_scalar_then_object_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (scalarResponseName scalarFieldName : Name)
    (scalarArguments : List Argument)
    (scalarDirectives : List DirectiveApplication)
    (scalarSelectionSet : List Selection)
    (scalarValue : String)
    (objectResponseName objectFieldName : Name)
    (objectArguments : List Argument)
    (objectDirectives : List DirectiveApplication)
    (objectSelectionSet : List Selection)
    (hscalarAllowed :
      selectionDirectivesAllowBool variableValues scalarDirectives = true)
    (hobjectAllowed :
      selectionDirectivesAllowBool variableValues objectDirectives = true)
    (hscalarResolve :
      resolvers.resolve parentType scalarFieldName scalarArguments source =
        .scalar scalarValue)
    (hobjectResolve :
      resolvers.resolve parentType objectFieldName objectArguments source =
        .object runtimeType (some identity))
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType objectFieldName).getD
          objectFieldName)
        runtimeType = true)
    (hdistinct : (scalarResponseName == objectResponseName) = false)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := objectSelectionSet }
          initial := .object [] }) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := childDepth + 2
          parentType := parentType
          source := source
          selectionSet :=
            [ .field scalarResponseName scalarFieldName scalarArguments
                scalarDirectives scalarSelectionSet
            , .field objectResponseName objectFieldName objectArguments
                objectDirectives objectSelectionSet ] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (childDepth + 2) parentType source
    [ .field scalarResponseName scalarFieldName scalarArguments
        scalarDirectives scalarSelectionSet
    , .field objectResponseName objectFieldName objectArguments
        objectDirectives objectSelectionSet ]
    (executeRootSelectionSet_scalar_then_object_field_succ_eq_spec_of_child
      schema resolvers variableValues childDepth parentType runtimeType
      identity source scalarResponseName scalarFieldName scalarArguments
      scalarDirectives scalarSelectionSet scalarValue objectResponseName
      objectFieldName objectArguments objectDirectives objectSelectionSet
      hscalarAllowed hobjectAllowed hscalarResolve hobjectResolve hincludes
      hdistinct hchild)

theorem executeRootSelectionSet_object_then_scalar_field_succ_eq_spec_of_child
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (objectResponseName objectFieldName : Name)
    (objectArguments : List Argument)
    (objectDirectives : List DirectiveApplication)
    (objectSelectionSet : List Selection)
    (scalarResponseName scalarFieldName : Name)
    (scalarArguments : List Argument)
    (scalarDirectives : List DirectiveApplication)
    (scalarSelectionSet : List Selection)
    (scalarValue : String)
    (hobjectAllowed :
      selectionDirectivesAllowBool variableValues objectDirectives = true)
    (hscalarAllowed :
      selectionDirectivesAllowBool variableValues scalarDirectives = true)
    (hobjectResolve :
      resolvers.resolve parentType objectFieldName objectArguments source =
        .object runtimeType (some identity))
    (hscalarResolve :
      resolvers.resolve parentType scalarFieldName scalarArguments source =
        .scalar scalarValue)
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType objectFieldName).getD
          objectFieldName)
        runtimeType = true)
    (hdistinct : (objectResponseName == scalarResponseName) = false)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := objectSelectionSet }
          initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field objectResponseName objectFieldName objectArguments
          objectDirectives objectSelectionSet
      , .field scalarResponseName scalarFieldName scalarArguments
          scalarDirectives scalarSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field objectResponseName objectFieldName objectArguments
          objectDirectives objectSelectionSet
      , .field scalarResponseName scalarFieldName scalarArguments
          scalarDirectives scalarSelectionSet ] := by
  unfold ExecutionStateEquivalent ResponseDataEquivalent at hchild
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection,
    mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        childDepth (.object runtimeType (some identity))
        (GraphQL.Execution.collectFields schema variableValues runtimeType
          (.object runtimeType (some identity)) objectSelectionSet))
      (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
        variableValues childDepth runtimeType (.object runtimeType (some identity))
        objectSelectionSet)] at hchild
  simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
    completeValue, GraphQL.Execution.executeRootSelectionSet,
    GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups,
    GraphQL.Execution.addExecutableGroup,
    GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
    GraphQL.Execution.completeValue, executableField, responseObjectField?,
    lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
    hobjectAllowed, hscalarAllowed, hobjectResolve, hscalarResolve, hincludes,
    hdistinct] at hchild ⊢
  simpa using hchild

theorem stateEquivalent_of_object_then_scalar_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (objectResponseName objectFieldName : Name)
    (objectArguments : List Argument)
    (objectDirectives : List DirectiveApplication)
    (objectSelectionSet : List Selection)
    (scalarResponseName scalarFieldName : Name)
    (scalarArguments : List Argument)
    (scalarDirectives : List DirectiveApplication)
    (scalarSelectionSet : List Selection)
    (scalarValue : String)
    (hobjectAllowed :
      selectionDirectivesAllowBool variableValues objectDirectives = true)
    (hscalarAllowed :
      selectionDirectivesAllowBool variableValues scalarDirectives = true)
    (hobjectResolve :
      resolvers.resolve parentType objectFieldName objectArguments source =
        .object runtimeType (some identity))
    (hscalarResolve :
      resolvers.resolve parentType scalarFieldName scalarArguments source =
        .scalar scalarValue)
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType objectFieldName).getD
          objectFieldName)
        runtimeType = true)
    (hdistinct : (objectResponseName == scalarResponseName) = false)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := objectSelectionSet }
          initial := .object [] }) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := childDepth + 2
          parentType := parentType
          source := source
          selectionSet :=
            [ .field objectResponseName objectFieldName objectArguments
                objectDirectives objectSelectionSet
            , .field scalarResponseName scalarFieldName scalarArguments
                scalarDirectives scalarSelectionSet ] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (childDepth + 2) parentType source
    [ .field objectResponseName objectFieldName objectArguments
        objectDirectives objectSelectionSet
    , .field scalarResponseName scalarFieldName scalarArguments
        scalarDirectives scalarSelectionSet ]
    (executeRootSelectionSet_object_then_scalar_field_succ_eq_spec_of_child
      schema resolvers variableValues childDepth parentType runtimeType
      identity source objectResponseName objectFieldName objectArguments
      objectDirectives objectSelectionSet scalarResponseName scalarFieldName
      scalarArguments scalarDirectives scalarSelectionSet scalarValue
      hobjectAllowed hscalarAllowed hobjectResolve hscalarResolve hincludes
      hdistinct hchild)

theorem executeRootSelectionSet_object_then_object_field_succ_eq_spec_of_children
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType firstRuntimeType secondRuntimeType : Name)
    (firstIdentity secondIdentity : Option ObjectIdentity)
    (source : Value ObjectIdentity)
    (firstResponseName firstFieldName : Name)
    (firstArguments : List Argument)
    (firstDirectives : List DirectiveApplication)
    (firstSelectionSet : List Selection)
    (secondResponseName secondFieldName : Name)
    (secondArguments : List Argument)
    (secondDirectives : List DirectiveApplication)
    (secondSelectionSet : List Selection)
    (hfirstAllowed :
      selectionDirectivesAllowBool variableValues firstDirectives = true)
    (hsecondAllowed :
      selectionDirectivesAllowBool variableValues secondDirectives = true)
    (hfirstResolve :
      resolvers.resolve parentType firstFieldName firstArguments source =
        .object firstRuntimeType firstIdentity)
    (hsecondResolve :
      resolvers.resolve parentType secondFieldName secondArguments source =
        .object secondRuntimeType secondIdentity)
    (hfirstIncludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType firstFieldName).getD
          firstFieldName)
        firstRuntimeType = true)
    (hsecondIncludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType secondFieldName).getD
          secondFieldName)
        secondRuntimeType = true)
    (hdistinct : (firstResponseName == secondResponseName) = false)
    (hfirstChild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := firstRuntimeType
            source := .object firstRuntimeType firstIdentity
            selectionSet := firstSelectionSet }
          initial := .object [] })
    (hsecondChild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := secondRuntimeType
            source := .object secondRuntimeType secondIdentity
            selectionSet := secondSelectionSet }
          initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (childDepth + 2)
      parentType source
      [ .field firstResponseName firstFieldName firstArguments
          firstDirectives firstSelectionSet
      , .field secondResponseName secondFieldName secondArguments
          secondDirectives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (childDepth + 2) parentType source
      [ .field firstResponseName firstFieldName firstArguments
          firstDirectives firstSelectionSet
      , .field secondResponseName secondFieldName secondArguments
          secondDirectives secondSelectionSet ] := by
  unfold ExecutionStateEquivalent ResponseDataEquivalent at hfirstChild
  unfold ExecutionStateEquivalent ResponseDataEquivalent at hsecondChild
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection,
    mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        childDepth (.object firstRuntimeType firstIdentity)
        (GraphQL.Execution.collectFields schema variableValues firstRuntimeType
          (.object firstRuntimeType firstIdentity) firstSelectionSet))
      (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
        variableValues childDepth firstRuntimeType
        (.object firstRuntimeType firstIdentity) firstSelectionSet)] at hfirstChild
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection,
    mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        childDepth (.object secondRuntimeType secondIdentity)
        (GraphQL.Execution.collectFields schema variableValues secondRuntimeType
          (.object secondRuntimeType secondIdentity) secondSelectionSet))
      (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
        variableValues childDepth secondRuntimeType
        (.object secondRuntimeType secondIdentity) secondSelectionSet)] at hsecondChild
  simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
    completeValue, GraphQL.Execution.executeRootSelectionSet,
    GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups,
    GraphQL.Execution.addExecutableGroup,
    GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
    GraphQL.Execution.completeValue, executableField, responseObjectField?,
    lookupResponseField?, mergeResponseFieldIntoObject, mergeResponseField,
    hfirstAllowed, hsecondAllowed, hfirstResolve, hsecondResolve,
    hfirstIncludes, hsecondIncludes, hdistinct] at hfirstChild hsecondChild ⊢
  constructor
  · exact hfirstChild
  · exact hsecondChild

theorem stateEquivalent_of_object_then_object_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType firstRuntimeType secondRuntimeType : Name)
    (firstIdentity secondIdentity : ObjectIdentity)
    (source : Value ObjectIdentity)
    (firstResponseName firstFieldName : Name)
    (firstArguments : List Argument)
    (firstDirectives : List DirectiveApplication)
    (firstSelectionSet : List Selection)
    (secondResponseName secondFieldName : Name)
    (secondArguments : List Argument)
    (secondDirectives : List DirectiveApplication)
    (secondSelectionSet : List Selection)
    (hfirstAllowed :
      selectionDirectivesAllowBool variableValues firstDirectives = true)
    (hsecondAllowed :
      selectionDirectivesAllowBool variableValues secondDirectives = true)
    (hfirstResolve :
      resolvers.resolve parentType firstFieldName firstArguments source =
        .object firstRuntimeType firstIdentity)
    (hsecondResolve :
      resolvers.resolve parentType secondFieldName secondArguments source =
        .object secondRuntimeType secondIdentity)
    (hfirstIncludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType firstFieldName).getD
          firstFieldName)
        firstRuntimeType = true)
    (hsecondIncludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType secondFieldName).getD
          secondFieldName)
        secondRuntimeType = true)
    (hdistinct : (firstResponseName == secondResponseName) = false)
    (hfirstChild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := firstRuntimeType
            source := .object firstRuntimeType firstIdentity
            selectionSet := firstSelectionSet }
          initial := .object [] })
    (hsecondChild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := secondRuntimeType
            source := .object secondRuntimeType secondIdentity
            selectionSet := secondSelectionSet }
          initial := .object [] }) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := childDepth + 2
          parentType := parentType
          source := source
          selectionSet :=
            [ .field firstResponseName firstFieldName firstArguments
                firstDirectives firstSelectionSet
            , .field secondResponseName secondFieldName secondArguments
                secondDirectives secondSelectionSet ] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (childDepth + 2) parentType source
    [ .field firstResponseName firstFieldName firstArguments
        firstDirectives firstSelectionSet
    , .field secondResponseName secondFieldName secondArguments
        secondDirectives secondSelectionSet ]
    (executeRootSelectionSet_object_then_object_field_succ_eq_spec_of_children
      schema resolvers variableValues childDepth parentType firstRuntimeType
      secondRuntimeType firstIdentity secondIdentity source firstResponseName
      firstFieldName firstArguments firstDirectives firstSelectionSet
      secondResponseName secondFieldName secondArguments secondDirectives
      secondSelectionSet hfirstAllowed hsecondAllowed hfirstResolve
      hsecondResolve hfirstIncludes hsecondIncludes hdistinct hfirstChild
      hsecondChild)


end ExecutionUngrouped
end Algorithms

end GraphQL
