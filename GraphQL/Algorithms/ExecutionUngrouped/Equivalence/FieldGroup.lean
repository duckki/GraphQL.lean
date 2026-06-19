import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem executeRootSelectionSet_executableFieldSelections_duplicate_eq_spec_of_completeValue_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hcomplete :
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        [ executableField parentType responseName fieldName arguments
            firstSelectionSet
        , executableField parentType responseName fieldName arguments
            secondSelectionSet ]
        resolved) :
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
  simpa [executableFieldSelections, executableFieldSelection, executableField] using
    executeRootSelectionSet_duplicate_field_succ_eq_spec_of_completeValue_merge
      schema resolvers variableValues depth parentType source responseName
      fieldName arguments [] firstSelectionSet secondSelectionSet resolved
      rfl hresolve hcomplete

theorem completeValue_duplicate_merge_eq_spec_of_append_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (happend :
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        (firstSelectionSet ++ secondSelectionSet) resolved .null)
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
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
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        [ executableField parentType responseName fieldName arguments
            firstSelectionSet
        , executableField parentType responseName fieldName arguments
            secondSelectionSet ]
        resolved := by
  rw [happend]
  simpa [GraphQL.Execution.mergedFieldSelectionSet, executableField] using
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues
      [ executableField parentType responseName fieldName arguments
          firstSelectionSet
      , executableField parentType responseName fieldName arguments
          secondSelectionSet ]
      depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      resolved
      (by
        intro childDepth runtimeType identity hlt hincludes
        simpa [GraphQL.Execution.mergedFieldSelectionSet, executableField] using
          hchildren childDepth runtimeType identity hlt hincludes)

theorem completeValue_duplicate_merge_eq_spec_of_append_completeValue_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (happend :
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        (firstSelectionSet ++ secondSelectionSet) resolved .null)
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
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
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        [ executableField parentType responseName fieldName arguments
            firstSelectionSet
        , executableField parentType responseName fieldName arguments
            secondSelectionSet ]
        resolved := by
  rw [happend]
  simpa [GraphQL.Execution.mergedFieldSelectionSet, executableField] using
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues
      [ executableField parentType responseName fieldName arguments
          firstSelectionSet
      , executableField parentType responseName fieldName arguments
          secondSelectionSet ]
      depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        simpa [GraphQL.Execution.mergedFieldSelectionSet, executableField] using
          hchildren childDepth runtimeType identity hlt hcontains hincludes)

theorem executeRootSelectionSet_executableFieldSelections_duplicate_eq_spec_of_append_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (happend :
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        (firstSelectionSet ++ secondSelectionSet) resolved .null)
    (hchildren :
      ∀ childDepth runtimeType identity,
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
  exact completeValue_duplicate_merge_eq_spec_of_append_completeValue schema
    resolvers variableValues depth parentType responseName fieldName arguments
    firstSelectionSet secondSelectionSet resolved happend
    (by
      intro childDepth runtimeType identity hlt _hincludes
      exact hchildren childDepth runtimeType identity hlt)

theorem completeValue_append_slices_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (value : Value ObjectIdentity) :
    mergeResponse
      (completeValue schema resolvers variableValues 0 parentType
        firstSelectionSet value .null)
      (completeValue schema resolvers variableValues 0 parentType
        secondSelectionSet value
        (completeValue schema resolvers variableValues 0 parentType
          firstSelectionSet value .null)) =
    completeValue schema resolvers variableValues 0 parentType
      (firstSelectionSet ++ secondSelectionSet) value .null := by
  simp [completeValue]
  exact mergeResponse_self_of_ready (shallowResponse value)
    (ResponseMergeReady_shallowResponse value)

theorem completeValue_append_slices_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection) :
    mergeResponse
      (completeValue schema resolvers variableValues (depth + 1) parentType
        firstSelectionSet (.null : Value ObjectIdentity) .null)
      (completeValue schema resolvers variableValues (depth + 1) parentType
        secondSelectionSet (.null : Value ObjectIdentity)
        (completeValue schema resolvers variableValues (depth + 1) parentType
          firstSelectionSet (.null : Value ObjectIdentity) .null)) =
    completeValue schema resolvers variableValues (depth + 1) parentType
      (firstSelectionSet ++ secondSelectionSet) (.null : Value ObjectIdentity)
      .null := by
  simp [completeValue, mergeResponse]

theorem completeValue_append_slices_scalar
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (value : String) :
    mergeResponse
      (completeValue schema resolvers variableValues (depth + 1) parentType
        firstSelectionSet (.scalar value : Value ObjectIdentity) .null)
      (completeValue schema resolvers variableValues (depth + 1) parentType
        secondSelectionSet (.scalar value : Value ObjectIdentity)
        (completeValue schema resolvers variableValues (depth + 1) parentType
          firstSelectionSet (.scalar value : Value ObjectIdentity) .null)) =
    completeValue schema resolvers variableValues (depth + 1) parentType
      (firstSelectionSet ++ secondSelectionSet)
      (.scalar value : Value ObjectIdentity) .null := by
  simp [completeValue, mergeResponse]

theorem completeValue_append_slices_empty_list
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection) :
    mergeResponse
      (completeValue schema resolvers variableValues (depth + 1) parentType
        firstSelectionSet (.list ([] : List (Value ObjectIdentity))) .null)
      (completeValue schema resolvers variableValues (depth + 1) parentType
        secondSelectionSet (.list ([] : List (Value ObjectIdentity)))
        (completeValue schema resolvers variableValues (depth + 1) parentType
          firstSelectionSet (.list ([] : List (Value ObjectIdentity))) .null)) =
    completeValue schema resolvers variableValues (depth + 1) parentType
      (firstSelectionSet ++ secondSelectionSet)
      (.list ([] : List (Value ObjectIdentity))) .null := by
  simp [completeValue, mergeResponse, mergeResponseLists]

theorem completeValue_append_slices_singleton_list_of_value
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (value : Value ObjectIdentity)
    (hvalue :
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
        firstSelectionSet (.list [value]) .null)
      (completeValue schema resolvers variableValues (depth + 1) parentType
        secondSelectionSet (.list [value])
        (completeValue schema resolvers variableValues (depth + 1) parentType
          firstSelectionSet (.list [value]) .null)) =
    completeValue schema resolvers variableValues (depth + 1) parentType
      (firstSelectionSet ++ secondSelectionSet) (.list [value]) .null := by
  simpa [completeValue, mergeResponse, mergeResponseLists] using hvalue

theorem completeValue_append_slices_object_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : Option ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hvisitAbsorb :
      ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) firstSelectionSet (.object []))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) secondSelectionSet
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) firstSelectionSet (.object [])))) :
    mergeResponse
      (completeValue schema resolvers variableValues (childDepth + 1)
        parentType firstSelectionSet (.object runtimeType identity) .null)
      (completeValue schema resolvers variableValues (childDepth + 1)
        parentType secondSelectionSet (.object runtimeType identity)
        (completeValue schema resolvers variableValues (childDepth + 1)
          parentType firstSelectionSet (.object runtimeType identity) .null)) =
    completeValue schema resolvers variableValues (childDepth + 1)
      parentType (firstSelectionSet ++ secondSelectionSet)
      (.object runtimeType identity) .null := by
  by_cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true
  · obtain ⟨previousFields, hpreviousFields⟩ :=
      visitSubfields_preserves_object schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) firstSelectionSet
        []
    rw [hpreviousFields] at hvisitAbsorb
    unfold ResponseAbsorbs at hvisitAbsorb
    simp [completeValue, hincludes]
    rw [hpreviousFields]
    simp [completeValue, hincludes]
    rw [hvisitAbsorb]
    rw [visitSubfields_append_equivalence schema resolvers variableValues childDepth
      runtimeType (.object runtimeType identity) firstSelectionSet
      secondSelectionSet (.object [])]
    rw [hpreviousFields]
  · have hnotIncludes :
        schema.typeIncludesObjectBool parentType runtimeType = false := by
      cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
        simp [h] at hincludes ⊢
    simp [completeValue, hnotIncludes, mergeResponse]

theorem completeValue_append_slices_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (firstSelectionSet secondSelectionSet : List Selection) :
    ∀ (depth : Nat) (parentType : Name) (value : Value ObjectIdentity),
      (∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) firstSelectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) secondSelectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) firstSelectionSet
                (.object [])))) ->
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          firstSelectionSet value .null)
        (completeValue schema resolvers variableValues depth parentType
          secondSelectionSet value
          (completeValue schema resolvers variableValues depth parentType
            firstSelectionSet value .null)) =
      completeValue schema resolvers variableValues depth parentType
        (firstSelectionSet ++ secondSelectionSet) value .null := by
  intro depth
  induction depth with
  | zero =>
      intro parentType value _hobjects
      exact completeValue_append_slices_zero schema resolvers variableValues
        parentType firstSelectionSet secondSelectionSet value
  | succ depth ih =>
      intro parentType value hobjects
      cases value with
      | null =>
          exact completeValue_append_slices_null schema resolvers
            variableValues depth parentType firstSelectionSet secondSelectionSet
      | scalar value =>
          exact completeValue_append_slices_scalar schema resolvers
            variableValues depth parentType firstSelectionSet secondSelectionSet
            value
      | object runtimeType identity =>
          exact completeValue_append_slices_object_of_visit_absorbs schema
            resolvers variableValues depth parentType runtimeType identity
            firstSelectionSet secondSelectionSet
            (hobjects depth runtimeType identity (Nat.lt_succ_self depth))
      | list values =>
          apply completeValue_append_slices_list_of_values schema resolvers
            variableValues depth parentType firstSelectionSet secondSelectionSet
            values
          intro childValue hmem
          exact ih parentType childValue
            (by
              intro childDepth runtimeType identity hlt
              exact hobjects childDepth runtimeType identity
                (Nat.lt_trans hlt (Nat.lt_succ_self depth)))

theorem completeValue_append_slices_of_contained_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (firstSelectionSet secondSelectionSet : List Selection) :
    ∀ (depth : Nat) (parentType : Name) (value : Value ObjectIdentity),
      (∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject value runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) firstSelectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) secondSelectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) firstSelectionSet
                (.object [])))) ->
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          firstSelectionSet value .null)
        (completeValue schema resolvers variableValues depth parentType
          secondSelectionSet value
          (completeValue schema resolvers variableValues depth parentType
            firstSelectionSet value .null)) =
      completeValue schema resolvers variableValues depth parentType
        (firstSelectionSet ++ secondSelectionSet) value .null := by
  intro depth
  induction depth with
  | zero =>
      intro parentType value _hobjects
      exact completeValue_append_slices_zero schema resolvers variableValues
        parentType firstSelectionSet secondSelectionSet value
  | succ depth ih =>
      intro parentType value hobjects
      cases value with
      | null =>
          exact completeValue_append_slices_null schema resolvers
            variableValues depth parentType firstSelectionSet secondSelectionSet
      | scalar value =>
          exact completeValue_append_slices_scalar schema resolvers
            variableValues depth parentType firstSelectionSet secondSelectionSet
            value
      | object runtimeType identity =>
          exact completeValue_append_slices_object_of_visit_absorbs schema
            resolvers variableValues depth parentType runtimeType identity
            firstSelectionSet secondSelectionSet
            (hobjects depth runtimeType identity (Nat.lt_succ_self depth)
              ValueContainsObject.here)
      | list values =>
          apply completeValue_append_slices_list_of_values schema resolvers
            variableValues depth parentType firstSelectionSet secondSelectionSet
            values
          intro childValue hmem
          exact ih parentType childValue
            (by
              intro childDepth runtimeType identity hlt hcontains
              exact hobjects childDepth runtimeType identity
                (Nat.lt_trans hlt (Nat.lt_succ_self depth))
                (ValueContainsObject.list hmem hcontains))

theorem completeValue_duplicate_merge_eq_spec_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hobjects :
      ∀ childDepth runtimeType identity,
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
      ∀ childDepth runtimeType identity,
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
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        [ executableField parentType responseName fieldName arguments
            firstSelectionSet
        , executableField parentType responseName fieldName arguments
            secondSelectionSet ]
        resolved := by
  apply completeValue_duplicate_merge_eq_spec_of_append_completeValue schema
    resolvers variableValues depth parentType responseName fieldName arguments
    firstSelectionSet secondSelectionSet resolved
  · exact completeValue_append_slices_of_visit_absorbs schema resolvers
      variableValues firstSelectionSet secondSelectionSet depth
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      resolved hobjects
  · intro childDepth runtimeType identity hlt _hincludes
    exact hchildren childDepth runtimeType identity hlt

theorem completeValue_duplicate_merge_eq_spec_of_visit_absorbs_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
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
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = true ->
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
      mergeResponse
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet resolved .null)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet resolved
          (completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            firstSelectionSet resolved .null)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        [ executableField parentType responseName fieldName arguments
            firstSelectionSet
        , executableField parentType responseName fieldName arguments
            secondSelectionSet ]
        resolved := by
  apply completeValue_duplicate_merge_eq_spec_of_append_completeValue_contained
    schema resolvers variableValues depth parentType responseName fieldName
    arguments firstSelectionSet secondSelectionSet resolved
  · exact completeValue_append_slices_of_contained_visit_absorbs schema resolvers
      variableValues firstSelectionSet secondSelectionSet depth
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      resolved hobjects
  · intro childDepth runtimeType identity hlt hcontains hincludes
    exact hchildren childDepth runtimeType identity hlt hcontains hincludes

theorem completeValue_two_fields_merge_eq_spec_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet ++ later.selectionSet }
              initial := .object [] }) :
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          first.selectionSet resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            first.selectionSet resolved .null)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType [first, later] resolved := by
  have happend :
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          first.selectionSet resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            first.selectionSet resolved .null)) =
      completeValue schema resolvers variableValues depth parentType
        (first.selectionSet ++ later.selectionSet) resolved .null :=
    completeValue_append_slices_of_visit_absorbs schema resolvers variableValues
      first.selectionSet later.selectionSet depth parentType resolved hobjects
  rw [happend]
  simpa [GraphQL.Execution.mergedFieldSelectionSet] using
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues [first, later] depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hincludes
        simpa [GraphQL.Execution.mergedFieldSelectionSet] using
          hchildren childDepth runtimeType identity hlt hincludes)

theorem completeValue_two_fields_merge_eq_spec_of_visit_absorbs_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet ++ later.selectionSet }
              initial := .object [] }) :
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          first.selectionSet resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            first.selectionSet resolved .null)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType [first, later] resolved := by
  have happend :
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          first.selectionSet resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            first.selectionSet resolved .null)) =
      completeValue schema resolvers variableValues depth parentType
        (first.selectionSet ++ later.selectionSet) resolved .null :=
    completeValue_append_slices_of_contained_visit_absorbs schema resolvers
      variableValues
      first.selectionSet later.selectionSet depth parentType resolved hobjects
  rw [happend]
  simpa [GraphQL.Execution.mergedFieldSelectionSet] using
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues [first, later] depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        simpa [GraphQL.Execution.mergedFieldSelectionSet] using
          hchildren childDepth runtimeType identity hlt hcontains hincludes)

theorem completeValue_group_append_one_merge_eq_spec_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : Value ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet prefixFields }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields) (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) }
              initial := .object [] }) :
    mergeResponse
      (GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType prefixFields resolved)
      (completeValue schema resolvers variableValues depth parentType
        later.selectionSet resolved
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType prefixFields resolved)) =
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      parentType (prefixFields ++ [later]) resolved := by
  have hprefix :
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType prefixFields resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues prefixFields depth parentType resolved hprefixChildren
  have happended :
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved .null =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved hchildren
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  have hslice :
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)) =
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved .null := by
    calc
      mergeResponse
          (completeValue schema resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)
          (completeValue schema resolvers variableValues depth parentType
            later.selectionSet resolved
            (completeValue schema resolvers variableValues depth parentType
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
              .null)) =
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
            later.selectionSet)
          resolved .null := by
          exact completeValue_append_slices_of_visit_absorbs schema resolvers
            variableValues (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
            later.selectionSet depth parentType resolved hobjects
      _ =
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
          resolved .null := by
          rw [hmergedAppend]
  calc
    mergeResponse
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType prefixFields resolved)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            parentType prefixFields resolved)) =
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
            .null)) := by
          rw [hprefix]
    _ =
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved .null := hslice
    _ =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType (prefixFields ++ [later]) resolved := happended

theorem completeValue_group_append_one_merge_eq_spec_of_contained_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : Value ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet prefixFields }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields) (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) }
              initial := .object [] }) :
    mergeResponse
      (GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType prefixFields resolved)
      (completeValue schema resolvers variableValues depth parentType
        later.selectionSet resolved
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType prefixFields resolved)) =
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      parentType (prefixFields ++ [later]) resolved := by
  have hprefix :
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType prefixFields resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues prefixFields depth parentType resolved hprefixChildren
  have happended :
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved .null =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved
      hchildren
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  have hslice :
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)) =
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved .null := by
    calc
      mergeResponse
          (completeValue schema resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)
          (completeValue schema resolvers variableValues depth parentType
            later.selectionSet resolved
            (completeValue schema resolvers variableValues depth parentType
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
              .null)) =
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
            later.selectionSet)
          resolved .null := by
          exact
            completeValue_append_slices_of_contained_visit_absorbs schema
              resolvers variableValues
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              later.selectionSet depth parentType resolved hobjects
      _ =
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
          resolved .null := by
          rw [hmergedAppend]
  calc
    mergeResponse
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType prefixFields resolved)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            parentType prefixFields resolved)) =
      mergeResponse
        (completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved .null)
        (completeValue schema resolvers variableValues depth parentType
          later.selectionSet resolved
          (completeValue schema resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
            .null)) := by
          rw [hprefix]
    _ =
      completeValue schema resolvers variableValues depth parentType
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved .null := hslice
    _ =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        parentType (prefixFields ++ [later]) resolved := happended

theorem ExecutableFieldsMergedResponse_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hprefix :
      ExecutableFieldsMergedResponse schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: fields) ++ [later]) }
              initial := .object [] }) :
    ExecutableFieldsMergedResponse schema resolvers variableValues depth
      parentType source responseName field (fields ++ [later]) resolved := by
  unfold ExecutableFieldsMergedResponse at hprefix ⊢
  have hcomplete :
      mergeResponse
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (field :: fields) resolved)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          later.selectionSet resolved
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            (field :: fields) resolved)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        ((field :: fields) ++ [later]) resolved :=
    completeValue_group_append_one_merge_eq_spec_of_visit_absorbs schema
      resolvers variableValues depth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      resolved (field :: fields) later hprefixChildren hobjects hchildren
  rw [show
      executableFieldSelections (field :: (fields ++ [later])) =
        executableFieldSelections (field :: fields) ++
          [executableFieldSelection later] by
    simp [executableFieldSelections]]
  rw [visitSubfields_append_equivalence schema resolvers variableValues (depth + 1)
    parentType source (executableFieldSelections (field :: fields))
    [executableFieldSelection later] (.object [])]
  rw [hprefix]
  cases field with
  | mk fieldParent fieldResponse fieldName fieldArguments fieldSelectionSet =>
      cases later with
      | mk laterParent laterResponse laterFieldName laterArguments
          laterSelectionSet =>
          dsimp at hlaterResponse hfieldParent hlaterParent hfieldName hresolveLater hcomplete ⊢
          subst fieldParent
          subst laterResponse
          subst laterParent
          subst laterFieldName
          simp [GraphQL.NormalForm.completeValue_eq_mergedFieldSelectionSet] at hcomplete
          simpa [visitSubfields, visitSelection, executeField,
            executableFieldSelection, executableField, responseObjectField?,
            lookupResponseField?, mergeResponseFieldIntoObject,
            mergeResponseField, selectionDirectivesAllowBool_empty,
            hresolveLater,
            GraphQL.NormalForm.completeValue_eq_mergedFieldSelectionSet] using
            hcomplete

theorem ExecutableFieldsMergedComplete_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hprefix :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: fields) ++ [later]) }
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedComplete_of_MergedResponse
  apply ExecutableFieldsMergedResponse_append_one_of_prefix schema resolvers
    variableValues depth parentType source responseName field fields later
    resolved
  · exact
      ExecutableFieldsMergedResponse_of_MergedComplete schema resolvers
        variableValues depth parentType source responseName field fields
        resolved hprefix
  · exact hlaterResponse
  · exact hfieldParent
  · exact hlaterParent
  · exact hfieldName
  · exact hresolveLater
  · exact hprefixChildren
  · exact hobjects
  · exact hchildren

theorem ExecutableFieldsMergedResponse_append_one_of_prefix_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hprefix :
      ExecutableFieldsMergedResponse schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: fields) ++ [later]) }
              initial := .object [] }) :
    ExecutableFieldsMergedResponse schema resolvers variableValues depth
      parentType source responseName field (fields ++ [later]) resolved := by
  unfold ExecutableFieldsMergedResponse at hprefix ⊢
  have hcomplete :
      mergeResponse
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (field :: fields) resolved)
        (completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          later.selectionSet resolved
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            (field :: fields) resolved)) =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        ((field :: fields) ++ [later]) resolved :=
    completeValue_group_append_one_merge_eq_spec_of_contained_visit_absorbs
      schema resolvers variableValues depth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      resolved (field :: fields) later hprefixChildren hobjects hchildren
  rw [show
      executableFieldSelections (field :: (fields ++ [later])) =
        executableFieldSelections (field :: fields) ++
          [executableFieldSelection later] by
    simp [executableFieldSelections]]
  rw [visitSubfields_append_equivalence schema resolvers variableValues (depth + 1)
    parentType source (executableFieldSelections (field :: fields))
    [executableFieldSelection later] (.object [])]
  rw [hprefix]
  cases field with
  | mk fieldParent fieldResponse fieldName fieldArguments fieldSelectionSet =>
      cases later with
      | mk laterParent laterResponse laterFieldName laterArguments
          laterSelectionSet =>
          dsimp at hlaterResponse hfieldParent hlaterParent hfieldName hresolveLater hcomplete ⊢
          subst fieldParent
          subst laterResponse
          subst laterParent
          subst laterFieldName
          simp [GraphQL.NormalForm.completeValue_eq_mergedFieldSelectionSet] at hcomplete
          simpa [visitSubfields, visitSelection, executeField,
            executableFieldSelection, executableField, responseObjectField?,
            lookupResponseField?, mergeResponseFieldIntoObject,
            mergeResponseField, selectionDirectivesAllowBool_empty,
            hresolveLater,
            GraphQL.NormalForm.completeValue_eq_mergedFieldSelectionSet] using
            hcomplete

theorem ExecutableFieldsMergedComplete_append_one_of_prefix_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hprefix :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: fields) ++ [later]) }
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedComplete_of_MergedResponse
  apply ExecutableFieldsMergedResponse_append_one_of_prefix_contained
    schema resolvers variableValues depth parentType source responseName field
    fields later resolved
  · exact
      ExecutableFieldsMergedResponse_of_MergedComplete schema resolvers
        variableValues depth parentType source responseName field fields
        resolved hprefix
  · exact hlaterResponse
  · exact hfieldParent
  · exact hlaterParent
  · exact hfieldName
  · exact hresolveLater
  · exact hprefixChildren
  · exact hobjects
  · exact hchildren

def ExecutableFieldsMergedCompleteAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity) :
    List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      later.responseName = responseName ∧
      later.parentType = parentType ∧
      later.fieldName = field.fieldName ∧
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object [])))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) ∧
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved
        (prefixTail ++ [later]) rest

def ExecutableFieldsMergedCompleteContainedAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity) :
    List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      later.responseName = responseName ∧
      later.parentType = parentType ∧
      later.fieldName = field.fieldName ∧
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object [])))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) ∧
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved
        (prefixTail ++ [later]) rest

structure ExecutedFieldAppendStep
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (prefixTail : List ExecutableField) (later : ExecutableField) where
  responseName_eq : later.responseName = responseName
  parent_eq : later.parentType = parentType
  fieldName_eq : later.fieldName = field.fieldName
  resolved_eq :
    resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolved
  prefixChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet :=
                GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail) }
            initial := .object [] }
  absorbs :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
        ResponseAbsorbs
          (visitSubfields schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))
            (.object []))
          (visitSubfields schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
  extendedChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet :=
                GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: prefixTail) ++ [later]) }
            initial := .object [] }

def ExecutedFieldAppendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity) :
    List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      ExecutedFieldAppendStep schema resolvers variableValues depth
        parentType source responseName field resolved prefixTail later ∧
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved (prefixTail ++ [later]) rest

def ExecutedFieldAppendPlanState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (field : ExecutableField) (fields : List ExecutableField) :
    List ExecutableField -> List ExecutableField -> Prop
  | prefixTail, [] =>
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }
  | prefixTail, later :: rest =>
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) ∧
      later ∈ field :: fields ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object [])))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) ∧
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields (prefixTail ++ [later]) rest

theorem ExecutedFieldAppendPlanState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields prefixTail : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail [] :=
  hprefixChildren

theorem ExecutedFieldAppendPlanState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail rest : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] })
    (hrest :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields (prefixTail ++ [later]) rest) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail (later :: rest) :=
  ⟨hprefixChildren, hlater, hobjects, hchildren, hrest⟩

theorem ExecutedFieldAppendPlanState.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail [later] := by
  refine ⟨hprefixChildren, hlater, hobjects, hchildren, ?_⟩
  intro childDepth runtimeType identity hlt hincludes
  simpa using hchildren childDepth runtimeType identity hlt hincludes

theorem ExecutedFieldAppendPlanState.cons_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail rest : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hsteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] })
    (hrest :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields (prefixTail ++ [later]) rest) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail (later :: rest) := by
  apply ExecutedFieldAppendPlanState.cons hprefixChildren hlater
  · intro childDepth runtimeType identity hlt
    exact visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity)
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object []))
      later.selectionSet
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object []))
      (hsteps childDepth runtimeType identity hlt)
  · exact hchildren
  · exact hrest

theorem ExecutedFieldAppendPlanState.singleton_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hsteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail [later] := by
  apply ExecutedFieldAppendPlanState.cons_of_visit_absorbs hprefixChildren
    hlater hsteps hchildren
  intro childDepth runtimeType identity hlt hincludes
  simpa using hchildren childDepth runtimeType identity hlt hincludes

theorem ExecutedFieldAppendPlanState.prefixChildren
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField}
    {fields prefixTail remaining : List ExecutableField} :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail remaining ->
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] } := by
  cases remaining with
  | nil =>
      intro hstate
      exact hstate
  | cons later rest =>
      intro hstate
      exact hstate.1

theorem ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ∀ prefixTail remaining,
      (∀ later, later ∈ remaining -> later ∈ fields) ->
        ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields prefixTail remaining
  | prefixTail, [], _hremaining => by
      exact ExecutedFieldAppendPlanState.nil (hprefixChildren prefixTail)
  | prefixTail, later :: rest, hremaining => by
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons (hprefixChildren prefixTail)
      · exact List.mem_cons_of_mem field hlaterFields
      · exact hobjects prefixTail later hlaterFields
      · exact hchildren prefixTail later hlaterFields
      · apply ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
          hprefixChildren hobjects hchildren (prefixTail ++ [later]) rest
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])

theorem ExecutedFieldAppendPlanState.of_all_prefixes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields := by
  apply ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
    hprefixChildren hobjects hchildren
  intro later hlater
  exact hlater

theorem ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ∀ prefixTail remaining,
      (∀ later, later ∈ remaining -> later ∈ fields) ->
        ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields prefixTail remaining
  | prefixTail, [], _hremaining => by
      exact ExecutedFieldAppendPlanState.nil (hprefixChildren prefixTail)
  | prefixTail, later :: rest, hremaining => by
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons_of_visit_absorbs
        (hprefixChildren prefixTail)
      · exact List.mem_cons_of_mem field hlaterFields
      · exact hsteps prefixTail later hlaterFields
      · exact hchildren prefixTail later hlaterFields
      · apply
          ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
            hprefixChildren hsteps hchildren (prefixTail ++ [later]) rest
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])

theorem ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields := by
  apply
    ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
      hprefixChildren hsteps hchildren
  intro later hlater
  exact hlater

theorem ExecutedFieldAppendPlanState.of_all_prefixes_of_local_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlocal :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields := by
  apply ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
    hprefixChildren
  · intro prefixTail later hlater childDepth runtimeType identity hlt
    let base :=
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object [])
    have hbaseReady : ResponseMergeReady base := by
      exact visitSubfields_response_ready schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) []
        ResponseMergeReady_empty_object
    have hbaseAbsorbs : ResponseAbsorbs base base :=
      ResponseAbsorbs_refl_of_ready base hbaseReady
    exact
      visitSubfields_absorbs_from_local_steps schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) base
        later.selectionSet base hbaseReady hbaseAbsorbs
        (hlocal prefixTail later hlater childDepth runtimeType identity hlt)
  · exact hchildren

theorem ExecutedFieldAppendPlan.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Value ObjectIdentity}
    {prefixTail : List ExecutableField} {later : ExecutableField}
    (step :
      ExecutedFieldAppendStep schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail later) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field resolved prefixTail [later] := by
  exact ⟨step, by simp [ExecutedFieldAppendPlan]⟩

theorem ExecutedFieldAppendPlan.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Value ObjectIdentity}
    {prefixTail : List ExecutableField} :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field resolved prefixTail [] := by
  simp [ExecutedFieldAppendPlan]

theorem ExecutedFieldAppendPlan.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Value ObjectIdentity}
    {prefixTail : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    (step :
      ExecutedFieldAppendStep schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail later)
    (restPlan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved (prefixTail ++ [later]) rest) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field resolved prefixTail (later :: rest) :=
  ⟨step, restPlan⟩

theorem ExecutedFieldAppendPlan.toAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity) :
    ∀ prefixTail rest,
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail rest ->
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved prefixTail rest
  | _prefixTail, [], _plan => by
      simp [ExecutableFieldsMergedCompleteAppendSteps]
  | prefixTail, later :: rest, plan => by
      rcases plan with ⟨step, restPlan⟩
      simp [ExecutableFieldsMergedCompleteAppendSteps]
      exact
        ⟨step.responseName_eq, step.parent_eq, step.fieldName_eq,
          step.resolved_eq, step.prefixChildren, step.absorbs,
          step.extendedChildren,
          ExecutedFieldAppendPlan.toAppendSteps schema resolvers
            variableValues depth parentType source responseName field resolved
            (prefixTail ++ [later]) rest restPlan⟩

structure ExecutedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) where
  resolved : Value ObjectIdentity
  responseName_eq :
    ∀ candidate, candidate ∈ field :: fields ->
      candidate.responseName = responseName
  parent_eq :
    ∀ candidate, candidate ∈ field :: fields ->
      candidate.parentType = parentType
  resolved_eq :
    resolvers.resolve field.parentType field.fieldName field.arguments source =
      resolved
  headChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet := field.selectionSet }
            initial := .object [] }
  appendSteps :
    ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
      depth parentType source responseName field resolved [] fields

theorem ExecutableFieldsMergedComplete_of_appendSteps_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hfieldParent : field.parentType = parentType) :
    ∀ prefixTail remaining,
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field prefixTail resolved ->
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved prefixTail
        remaining ->
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field (prefixTail ++ remaining)
        resolved
  | prefixTail, [], hprefix, _hsteps => by
      simpa using hprefix
  | prefixTail, later :: rest, hprefix, hsteps => by
      simp [ExecutableFieldsMergedCompleteAppendSteps] at hsteps
      rcases hsteps with
        ⟨hlaterResponse, hlaterParent, hfieldName, hresolveLater,
          hprefixChildren, hobjects, hchildren, hrest⟩
      have hnext :
          ExecutableFieldsMergedComplete schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedComplete_append_one_of_prefix schema resolvers
          variableValues depth parentType source responseName field prefixTail
          later resolved hprefix hlaterResponse hfieldParent hlaterParent
          hfieldName hresolveLater hprefixChildren hobjects hchildren
      have htail :=
        ExecutableFieldsMergedComplete_of_appendSteps_from_prefix schema
          resolvers variableValues depth parentType source responseName field
          resolved hfieldParent (prefixTail ++ [later]) rest hnext hrest
      simpa [List.append_assoc] using htail

theorem ExecutableFieldsMergedComplete_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity)
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved [] fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields resolved := by
  have hbase :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedComplete_single_of_guarded_child_states schema resolvers
      variableValues depth parentType source responseName field resolved
      hfieldResponse hfieldParent hresolve hfieldChildren
  simpa using
    ExecutableFieldsMergedComplete_of_appendSteps_from_prefix schema resolvers
      variableValues depth parentType source responseName field resolved
      hfieldParent [] fields hbase hsteps

theorem ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hfieldParent : field.parentType = parentType) :
    ∀ prefixTail remaining,
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field prefixTail resolved ->
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved
        prefixTail remaining ->
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field (prefixTail ++ remaining)
        resolved
  | prefixTail, [], hprefix, _hsteps => by
      simpa using hprefix
  | prefixTail, later :: rest, hprefix, hsteps => by
      simp [ExecutableFieldsMergedCompleteContainedAppendSteps] at hsteps
      rcases hsteps with
        ⟨hlaterResponse, hlaterParent, hfieldName, hresolveLater,
          hprefixChildren, hobjects, hchildren, hrest⟩
      have hnext :
          ExecutableFieldsMergedComplete schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedComplete_append_one_of_prefix_contained schema
          resolvers variableValues depth parentType source responseName field
          prefixTail later resolved hprefix hlaterResponse hfieldParent
          hlaterParent hfieldName hresolveLater hprefixChildren hobjects
          hchildren
      have htail :=
        ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix
          schema resolvers variableValues depth parentType source responseName
          field resolved hfieldParent (prefixTail ++ [later]) rest hnext
          hrest
      simpa [List.append_assoc] using htail

theorem ExecutableFieldsMergedComplete_of_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Value ObjectIdentity)
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved []
        fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields resolved := by
  have hbase :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedComplete_single_of_contained_child_states schema
      resolvers variableValues depth parentType source responseName field
      resolved hfieldResponse hfieldParent hresolve hfieldChildren
  simpa using
    ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix schema
      resolvers variableValues depth parentType source responseName field
      resolved hfieldParent [] fields hbase hsteps

namespace ExecutedFieldGroup

def of_appendPlan
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
        resolved)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields where
  resolved := resolved
  responseName_eq := hresponse
  parent_eq := hparent
  resolved_eq := hresolve
  headChildren := hfieldChildren
  appendSteps :=
    ExecutedFieldAppendPlan.toAppendSteps schema resolvers variableValues
      depth parentType source responseName field resolved [] fields plan

theorem field_responseName
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    field.responseName = responseName :=
  group.responseName_eq field (by simp)

theorem field_parent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    field.parentType = parentType :=
  group.parent_eq field (by simp)

theorem mergedComplete
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields group.resolved :=
  ExecutableFieldsMergedComplete_of_appendSteps schema resolvers variableValues
    depth parentType source responseName field fields group.resolved
    group.field_responseName group.field_parent group.resolved_eq
    group.headChildren group.appendSteps

theorem mergedComplete_resolved
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source) := by
  rw [group.resolved_eq]
  exact group.mergedComplete

theorem flatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) :=
  ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete schema
    resolvers variableValues depth parentType source responseName field fields
    group.resolved group.responseName_eq group.parent_eq group.resolved_eq
    group.mergedComplete

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact group.flatSpecEquivalent

end ExecutedFieldGroup

def ExecutedFieldGroups
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    List (Name × List ExecutableField) -> Type
  | [] => Unit
  | (_responseName, []) :: _rest => Empty
  | (responseName, field :: fields) :: rest =>
      ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields ×
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source rest

def ExecutedFieldGroups.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      [] :=
  ()

def ExecutedFieldGroups.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    (hgroup :
      ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields)
    (hrest :
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source rest) :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, field :: fields) :: rest) :=
  (hgroup, hrest)

def ExecutedFieldGroups.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (hgroup :
      ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields) :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      [(responseName, field :: fields)] :=
  ExecutedFieldGroups.cons hgroup ExecutedFieldGroups.nil

theorem ExecutedFieldGroups.no_empty_head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {rest : List (Name × List ExecutableField)} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, []) :: rest) ->
    False := by
  intro hgroups
  exact nomatch hgroups

def ExecutedFieldGroups.head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, field :: fields) :: rest) ->
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields :=
  fun hgroups => hgroups.1

def ExecutedFieldGroups.tail
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, field :: fields) :: rest) ->
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      rest :=
  fun hgroups => hgroups.2

theorem ExecutedFieldGroups.nil_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [] :=
  ExecutableGroupsFlatSpecEquivalent_nil schema resolvers variableValues
    (depth + 1) parentType source

theorem ExecutedFieldGroups.head_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth parentType source
        ((responseName, field :: fields) :: rest)) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] :=
  (ExecutedFieldGroups.head hgroups).groupFlatSpecEquivalent

def ExecutedFieldGroup.of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields where
  resolved :=
    resolvers.resolve field.parentType field.fieldName field.arguments source
  responseName_eq :=
    hresponses responseName (field :: fields) hgroup
  parent_eq :=
    hparents responseName (field :: fields) hgroup
  resolved_eq := rfl
  headChildren := hfieldChildren
  appendSteps := hsteps

def ExecutedFieldGroup.of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields :=
  ExecutedFieldGroup.of_collected_appendSteps schema resolvers variableValues
    depth parentType source groups responseName field fields hgroup
    hresponses hparents hfieldChildren
    (ExecutedFieldAppendPlan.toAppendSteps schema resolvers variableValues
      depth parentType source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source)
      [] fields plan)

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_appendSteps
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
        resolved)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved [] fields) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved :=
    ExecutableFieldsMergedComplete_of_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields resolved
      hfieldResponse hfieldParent hresolve
      hfieldChildren
      hsteps
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_appendSteps
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
        resolved)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved [] fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hfieldChildren hsteps

theorem ExecutableGroupsFlatSpecEquivalent_collected_nonempty_group_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  exact
    ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hgroupResponses hgroupParents rfl
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      hsteps

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_contained_appendSteps
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
        resolved)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved []
        fields) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved :=
    ExecutableFieldsMergedComplete_of_contained_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields resolved
      hfieldResponse hfieldParent hresolve hfieldChildren hsteps
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_contained_appendSteps
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
        resolved)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved []
        fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_contained_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hfieldChildren hsteps

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source) :=
    ExecutableFieldsMergedComplete_of_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl
      hfieldChildren
      hsteps
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source) :=
    ExecutableFieldsMergedComplete_of_contained_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl hfieldChildren hsteps
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendSteps
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      hsteps

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_contained_appendSteps
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldChildren hsteps

theorem executeQuery_eq_spec_of_exact_nonempty_group_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendSteps schema
      resolvers variableValues operation depth source responseName field fields
      hroot hcollect hdirect hresponse hparent hfieldChildren hsteps

theorem executeQuery_eq_spec_of_exact_nonempty_group_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_contained_appendSteps
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent
      (by
        intro childDepth runtimeType identity hlt hcontains _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt hcontains)
      hsteps

theorem executeRootSelectionSet_eq_spec_of_executedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect group.responseName_eq
      group.parent_eq group.mergedComplete_resolved

theorem executeQueryAtDepth_eq_spec_of_executedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth operation.rootType
        source responseName field fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      responseName field fields hcollect hdirect group

theorem executeQuery_eq_spec_of_executedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth operation.rootType
        source responseName field fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_executedFieldGroup schema resolvers
      variableValues operation depth source responseName field fields hroot
      hcollect hdirect group

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_appendPlan schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        hresponse hparent rfl
        hfieldChildren
        plan)

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth
        operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendPlan schema
      resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldChildren plan

theorem executeQuery_eq_spec_of_exact_nonempty_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth
        operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendPlan schema
      resolvers variableValues operation depth source responseName field fields
      hroot hcollect hdirect hresponse hparent
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      plan

theorem executeRootSelectionSet_eq_spec_of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_appendSteps schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hfieldChildren childDepth runtimeType identity hlt)
        hsteps)

theorem executeQueryAtDepth_eq_spec_of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent operation.rootType groups)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_collected_appendSteps schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      [(responseName, field :: fields)] responseName field fields hcollect
      hgroup hdirect hresponses hparents hfieldChildren hsteps rfl

theorem executeRootSelectionSet_eq_spec_of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_appendPlan schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents
        hfieldChildren
        plan)

theorem executeQueryAtDepth_eq_spec_of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent operation.rootType groups)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth
        operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_collected_appendPlan schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      [(responseName, field :: fields)] responseName field fields hcollect
      hgroup hdirect hresponses hparents
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      plan rfl

structure ExecutedSingleGroupSelectionState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) where
  groups : List (Name × List ExecutableField)
  responseName : Name
  field : ExecutableField
  fields : List ExecutableField
  collect_eq :
    GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet = groups
  group_mem : (responseName, field :: fields) ∈ groups
  exact_groups : groups = [(responseName, field :: fields)]
  direct :
    VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
      parentType source selectionSet (.object [])
  responses : CollectedGroupsResponseName groups
  parents : CollectedGroupsParent parentType groups
  headChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet := field.selectionSet }
            initial := .object [] }
  appendPlan :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source)
      [] fields

namespace ExecutedSingleGroupSelectionState

def of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutedSingleGroupSelectionState schema resolvers variableValues depth
      parentType source selectionSet where
  groups := groups
  responseName := responseName
  field := field
  fields := fields
  collect_eq := hcollect
  group_mem := hgroup
  exact_groups := hexact
  direct := hdirect
  responses :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] }
      groups hcollect
  parents :=
    ExecutionCollectedFieldInvariant.parent_of_collect_eq
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] }
      groups hcollect
  headChildren := hfieldChildren
  appendPlan := plan

def toExecutedFieldGroup
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      state.responseName state.field state.fields :=
  ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
    depth parentType source state.groups state.responseName state.field
    state.fields state.group_mem state.responses state.parents
    state.headChildren state.appendPlan

theorem flatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (state.field :: state.fields) :=
  state.toExecutedFieldGroup.flatSpecEquivalent

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source
      [(state.responseName, state.field :: state.fields)] :=
  state.toExecutedFieldGroup.groupFlatSpecEquivalent

theorem executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_appendPlan schema resolvers
    variableValues depth parentType source selectionSet state.groups
    state.responseName state.field state.fields state.collect_eq
    state.group_mem state.direct state.responses state.parents
    state.headChildren state.appendPlan state.exact_groups

theorem stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source selectionSet
      state.executeRootSelectionSet_eq_spec

theorem executeQueryAtDepth_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : Value ObjectIdentity}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        operation.rootType source operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact state.executeRootSelectionSet_eq_spec

theorem executeQuery_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : Value ObjectIdentity}
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        operation.rootType source operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact state.executeQueryAtDepth_eq_spec hroot

end ExecutedSingleGroupSelectionState

theorem ExecutedFieldAppendStep_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hlaterParent : later.parentType = parentType)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hfirstChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet ++ later.selectionSet }
              initial := .object [] }) :
    ExecutedFieldAppendStep schema resolvers variableValues depth parentType
      source responseName first resolved [] later := by
  refine
    { responseName_eq := hlaterResponse
      parent_eq := hlaterParent
      fieldName_eq := hfieldName
      resolved_eq := hresolveLater
      prefixChildren := ?prefixChildren
      absorbs := ?absorbs
      extendedChildren := ?extendedChildren }
  · intro childDepth runtimeType identity hlt _hincludes
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hfirstChildren childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hobjects childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt _hincludes
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildren childDepth runtimeType identity hlt

theorem ExecutedFieldAppendPlan_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hlaterParent : later.parentType = parentType)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hfirstChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet ++ later.selectionSet }
              initial := .object [] }) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName first resolved [] [later] :=
  ExecutedFieldAppendPlan.singleton
    (ExecutedFieldAppendStep_two_of_visit_absorbs schema resolvers
      variableValues depth parentType source responseName first later resolved
      hlaterParent hlaterResponse hfieldName hresolveLater hfirstChildren
      hobjects hchildren)

theorem ExecutedFieldAppendStep.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) (later : ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hlater : later ∈ field :: fields)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object []))))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) :
    ExecutedFieldAppendStep schema resolvers variableValues depth parentType
      source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source)
      prefixTail later := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible (field :: fields) :=
    hcompatible responseName (field :: fields) hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable resolvers source (field :: fields) :=
    hstable responseName (field :: fields) hgroup
  have hfieldResponse : field.responseName = responseName :=
    hgroupResponses field (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later hlater
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later hlater
  have hsameResponse : field.responseName = later.responseName := by
    rw [hfieldResponse, hlaterResponse]
  have hfieldName : later.fieldName = field.fieldName :=
    (hgroupCompatible field later (by simp) hlater hsameResponse).1.symm
  have hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve field.parentType field.fieldName field.arguments
        source :=
    (hgroupStable field later (by simp) hlater hsameResponse).symm
  refine
    { responseName_eq := hlaterResponse
      parent_eq := hlaterParent
      fieldName_eq := hfieldName
      resolved_eq := hresolveLater
      prefixChildren := hprefixChildren
      absorbs := hobjects
      extendedChildren := hchildren }

theorem ExecutedFieldAppendPlan.of_collected_group_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups) :
    ∀ prefixTail remaining,
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail remaining ->
        ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          prefixTail remaining
  | _prefixTail, [], _hstate => by
      exact ExecutedFieldAppendPlan.nil
  | prefixTail, later :: rest, hstate => by
      rcases hstate with
        ⟨hprefixChildren, hlater, hobjects, hchildren, hrest⟩
      apply ExecutedFieldAppendPlan.cons
      · exact
          ExecutedFieldAppendStep.of_collected_group schema resolvers
            variableValues depth parentType source groups responseName field
            fields prefixTail later hgroup hlater hresponses hparents
            hcompatible hstable hprefixChildren hobjects hchildren
      · exact
          ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
            variableValues depth parentType source groups responseName field
            fields hgroup hresponses hparents hcompatible hstable
            (prefixTail ++ [later]) rest hrest

theorem ExecutedFieldAppendPlan.of_collected_group_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ∀ prefixTail remaining,
      (∀ later, later ∈ remaining -> later ∈ fields) ->
        ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          prefixTail remaining
  | prefixTail, remaining, hremaining => by
      exact
        ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
          variableValues depth parentType source groups responseName field fields
          hgroup hresponses hparents hcompatible hstable prefixTail remaining
          (ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
            (by
              intro prefixTail childDepth runtimeType identity hlt _hincludes
              exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
            hobjects
            (by
              intro prefixTail later hlater childDepth runtimeType identity hlt
                _hincludes
              exact hchildren prefixTail later hlater childDepth runtimeType
                identity hlt)
            prefixTail remaining hremaining)

theorem ExecutedFieldAppendPlan.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      [] fields := by
  apply ExecutedFieldAppendPlan.of_collected_group_from_prefix schema resolvers
    variableValues depth parentType source groups responseName field fields
    hgroup hresponses hparents hcompatible hstable hprefixChildren hobjects
    hchildren
  intro later hlater
  exact hlater

def ExecutedFieldGroup.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields := by
  let hstate :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields :=
    ExecutedFieldAppendPlanState.of_all_prefixes
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hobjects
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt)
  exact
    ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
      depth parentType source groups responseName field fields hgroup hresponses
      hparents
      (by
        intro childDepth runtimeType identity hlt
        simpa [GraphQL.Execution.mergedFieldSelectionSet] using
          ExecutedFieldAppendPlanState.prefixChildren hstate childDepth
            runtimeType identity hlt)
      (ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
        variableValues depth parentType source groups responseName field fields
        hgroup hresponses hparents hcompatible hstable [] fields hstate)

def ExecutedFieldGroup.of_collected_group_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hstate :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields :=
  ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
    depth parentType source groups responseName field fields hgroup hresponses
    hparents
    (by
      intro childDepth runtimeType identity hlt
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        ExecutedFieldAppendPlanState.prefixChildren hstate childDepth
          runtimeType identity hlt)
    (ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
      variableValues depth parentType source groups responseName field fields
      hgroup hresponses hparents hcompatible hstable [] fields hstate)

theorem stateEquivalent_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  let state : ExecutionEquivalenceState ObjectIdentity :=
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := parentType
        source := source
        selectionSet := selectionSet }
      initial := .object [] }
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hstable : CollectedGroupsResolveStable resolvers source groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
        hinvariant hcollect
  apply stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_group schema resolvers variableValues
        depth parentType source [(responseName, field :: fields)] responseName
      field fields hgroup hresponses hparents hcompatible hstable
      hprefixChildren hobjects hchildren)

theorem stateEquivalent_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  let state : ExecutionEquivalenceState ObjectIdentity :=
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := parentType
        source := source
        selectionSet := selectionSet }
      initial := .object [] }
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hstable : CollectedGroupsResolveStable resolvers source groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
        hinvariant hcollect
  apply stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_group_state schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents hcompatible
        hstable hplanState)

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet := selectionSet }
    (stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName field fields hcollect hgroup hexact hdirect hinvariant
      hcompatible hplanState)

theorem executeQueryAtDepth_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth operation.rootType source
      operation.selectionSet groups responseName field fields hcollect hgroup
      hexact hdirect hinvariant hcompatible hplanState

theorem executeQuery_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_field_group_state_of_invariant
      schema resolvers variableValues operation depth source groups responseName
      field fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hplanState

theorem stateEquivalent_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } :=
  stateEquivalent_of_collected_field_group_state_of_invariant schema
    resolvers variableValues depth parentType source selectionSet groups
    responseName field fields hcollect hgroup hexact hdirect hinvariant
    hcompatible
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_field_group_state_of_invariant
    schema resolvers variableValues depth parentType source selectionSet groups
    responseName field fields hcollect hgroup hexact hdirect hinvariant
    hcompatible
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeQueryAtDepth_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  executeQueryAtDepth_eq_spec_of_collected_field_group_state_of_invariant
    schema resolvers variableValues operation depth source groups responseName
    field fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeQuery_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source :=
  executeQuery_eq_spec_of_collected_field_group_state_of_invariant schema
    resolvers variableValues operation depth source groups responseName field
    fields hdepth hroot hcollect hgroup hexact hdirect hinvariant hcompatible
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet := selectionSet }
    (stateEquivalent_of_collected_field_group_of_invariant schema resolvers
      variableValues depth parentType source selectionSet groups responseName
      field fields hcollect hgroup hexact hdirect hinvariant hcompatible
      hprefixChildren hobjects hchildren)

theorem executeQueryAtDepth_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_field_group_of_invariant schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      groups responseName field fields hcollect hgroup hexact hdirect
      hinvariant hcompatible hprefixChildren hobjects hchildren

theorem executeQuery_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_field_group_of_invariant schema
      resolvers variableValues operation depth source groups responseName field
      fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hprefixChildren hobjects hchildren

end ExecutionUngrouped
end Algorithms

end GraphQL
