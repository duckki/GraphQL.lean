import GraphQL.NormalForm.GroundTypeLifting.ScopedSelections
import GraphQL.Execution.FieldCollection
import GraphQL.NormalForm.GroundTypeNormalization.FieldSemantics
import GraphQL.NormalForm.GroundTypeNormalization.RuntimeFragmentSemantics

/-!
Execution-group bridge lemmas for ground-type lifting proofs.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeLifting

variable {ObjectRef : Type}

open GroundTypeNormalization

private theorem executeCollectedFields_append
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
    ∀ left right : List (Name × List Execution.ExecutableField),
      Execution.executeCollectedFields schema resolvers variableValues depth
        source (left ++ right)
      =
      Execution.executeCollectedFields schema resolvers variableValues depth
        source left
        ++
      Execution.executeCollectedFields schema resolvers variableValues depth
        source right
  | [], right => by
      simp [Execution.executeCollectedFields]
  | (responseName, fields) :: rest, right => by
      simp [Execution.executeCollectedFields,
        executeCollectedFields_append schema resolvers variableValues depth
          source rest right, List.append_assoc]

theorem executeSelectionSet_append_eq_of_parts_namesDisjoint
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (normalizedLeft left normalizedRight right : List Selection) :
    executableGroupNamesDisjoint
      (Execution.collectFields schema variableValues parentType source
        normalizedLeft)
      (Execution.collectFields schema variableValues parentType source
        normalizedRight) ->
    executableGroupNamesDisjoint
      (Execution.collectFields schema variableValues parentType source left)
      (Execution.collectFields schema variableValues parentType source right) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source normalizedLeft
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source left ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source normalizedRight
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source right ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source (normalizedLeft ++ normalizedRight)
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source (left ++ right) := by
  intro hnormalizedDisjoint horiginalDisjoint hleft hright
  have hleftCollected :
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues parentType source
          normalizedLeft)
      =
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues parentType source
          left) := by
    simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
      using hleft
  have hrightCollected :
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues parentType source
          normalizedRight)
      =
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues parentType source
          right) := by
    simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
      using hright
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
  rw [collectFields_append]
  rw [collectFields_append]
  rw [mergeExecutableGroups_eq_append_of_namesDisjoint]
  · rw [mergeExecutableGroups_eq_append_of_namesDisjoint]
    · rw [executeCollectedFields_append]
      rw [executeCollectedFields_append]
      rw [hleftCollected, hrightCollected]
    · exact horiginalDisjoint
    · exact collectFields_namesNodup schema variableValues parentType source
        right
  · exact hnormalizedDisjoint
  · exact collectFields_namesNodup schema variableValues parentType source
      normalizedRight
theorem collectFields_namesDisjoint_of_responseNameFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.Value ObjectRef)
    (left right : List Selection) :
    objectTypeNameBool schema parentType = true ->
    (∃ runtimeType ref,
      source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
    selectionSetDirectiveFree right ->
    (∀ responseName,
      responseName ∈
        (Execution.collectFields schema variableValues parentType source
          left).map Prod.fst ->
        selectionSetResponseNameFree schema parentType responseName right) ->
      executableGroupNamesDisjoint
        (Execution.collectFields schema variableValues parentType source left)
        (Execution.collectFields schema variableValues parentType source right) := by
  intro hobject hsource hrightFree hrightResponseFree
  have hsourceValue :
      ∃ runtimeType ref,
        source = .object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    rcases hsource with ⟨runtimeType, ref, hsourceEq, hinclude⟩
    subst source
    exact ⟨runtimeType, ref, by simp [], hinclude⟩
  intro responseName hleft hright
  exact
    (collectFields_responseName_not_mem_of_responseNameFree schema
      variableValues parentType source responseName hobject hsourceValue right
      hrightFree (hrightResponseFree responseName hleft)) hright

theorem executeSelectionSet_inlineFragment_none_groundLift_disjoint
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType liftParent : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet rest : List Selection) :
    executableGroupNamesDisjoint
      (Execution.collectFields schema variableValues parentType source
        (groundLiftSelectionSet schema liftParent selectionSet))
      (Execution.collectFields schema variableValues parentType source
        (groundLiftSelectionSet schema liftParent rest)) ->
    executableGroupNamesDisjoint
      (Execution.collectFields schema variableValues parentType source
        selectionSet)
      (Execution.collectFields schema variableValues parentType source rest) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (groundLiftSelectionSet schema liftParent selectionSet)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source selectionSet ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (groundLiftSelectionSet schema liftParent rest)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source rest ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (groundLiftSelectionSet schema liftParent
          (Selection.inlineFragment none [] selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment none [] selectionSet :: rest) := by
  intro hnormalizedDisjoint horiginalDisjoint hselection hrest
  rw [groundLiftSelectionSet, groundLiftSelection]
  rw [executeSelectionSet_inlineFragment_none_directiveFree_flatten]
  rw [executeSelectionSet_inlineFragment_none_directiveFree_flatten]
  exact executeSelectionSet_append_eq_of_parts_namesDisjoint schema resolvers
    variableValues depth parentType source
    (groundLiftSelectionSet schema liftParent selectionSet) selectionSet
    (groundLiftSelectionSet schema liftParent rest) rest
    hnormalizedDisjoint horiginalDisjoint hselection hrest

theorem executeSelectionSet_inlineFragment_none_groundLift_scoped_flatten
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType liftParent : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) (rest : List ScopedSelection) :
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (groundLiftScopedSelectionSet schema
        (scopedSelectionSet liftParent selectionSet ++ rest))
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (eraseScopedSelectionSet
        (scopedSelectionSet liftParent selectionSet ++ rest)) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection := Selection.inlineFragment none [] selectionSet }
            :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (eraseScopedSelectionSet
          ({ liftParent := liftParent,
             selection := Selection.inlineFragment none [] selectionSet }
            :: rest)) := by
  intro hflatten
  simp [groundLiftScopedSelectionSet, groundLiftScopedSelection,
    groundLiftSelection, eraseScopedSelectionSet, eraseScopedSelection]
  rw [executeSelectionSet_inlineFragment_none_directiveFree_flatten]
  rw [executeSelectionSet_inlineFragment_none_directiveFree_flatten]
  simpa [groundLiftScopedSelectionSet_append,
    groundLiftScopedSelectionSet_scopedSelectionSet,
    eraseScopedSelectionSet_append,
    eraseScopedSelectionSet_scopedSelectionSet] using hflatten

theorem executeSelectionSet_inlineFragment_some_groundLift_skip
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType liftParent typeCondition : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source
      typeCondition = false ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (groundLiftSelectionSet schema liftParent rest)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source rest ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (groundLiftSelectionSet schema liftParent
          (Selection.inlineFragment (some typeCondition) [] selectionSet
            :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet
          :: rest) := by
  intro hskip hrest
  rw [groundLiftSelectionSet, groundLiftSelection]
  rw [executeSelectionSet_inlineFragment_some_directiveFree_skip]
  · rw [executeSelectionSet_inlineFragment_some_directiveFree_skip]
    · exact hrest
    · exact hskip
  · exact hskip

theorem executeSelectionSet_inlineFragment_some_groundLift_scoped_skip
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType liftParent typeCondition : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) (rest : List ScopedSelection) :
    Execution.doesFragmentTypeApplyBool schema parentType source
      typeCondition = false ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (groundLiftScopedSelectionSet schema rest)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (eraseScopedSelectionSet rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection :=
              Selection.inlineFragment (some typeCondition) [] selectionSet }
            :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (eraseScopedSelectionSet
          ({ liftParent := liftParent,
             selection :=
              Selection.inlineFragment (some typeCondition) [] selectionSet }
            :: rest)) := by
  intro hskip hrest
  simp [groundLiftScopedSelectionSet, groundLiftScopedSelection,
    groundLiftSelection, eraseScopedSelectionSet, eraseScopedSelection]
  rw [executeSelectionSet_inlineFragment_some_directiveFree_skip]
  · rw [executeSelectionSet_inlineFragment_some_directiveFree_skip]
    · exact hrest
    · exact hskip
  · exact hskip

theorem executeSelectionSet_inlineFragment_some_groundLift_scoped_apply_flatten
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType liftParent typeCondition : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) (rest : List ScopedSelection) :
    Execution.doesFragmentTypeApplyBool schema parentType source
      typeCondition = true ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (groundLiftScopedSelectionSet schema
        (scopedSelectionSet typeCondition selectionSet ++ rest))
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (eraseScopedSelectionSet
        (scopedSelectionSet typeCondition selectionSet ++ rest)) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection :=
              Selection.inlineFragment (some typeCondition) [] selectionSet }
            :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (eraseScopedSelectionSet
          ({ liftParent := liftParent,
             selection :=
              Selection.inlineFragment (some typeCondition) [] selectionSet }
            :: rest)) := by
  intro happly hflatten
  simp [groundLiftScopedSelectionSet, groundLiftScopedSelection,
    groundLiftSelection, eraseScopedSelectionSet, eraseScopedSelection]
  rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten]
  · rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten]
    · simpa [groundLiftScopedSelectionSet_append,
        groundLiftScopedSelectionSet_scopedSelectionSet,
        eraseScopedSelectionSet_append,
        eraseScopedSelectionSet_scopedSelectionSet] using hflatten
    · exact happly
  · exact happly

theorem executeSelectionSet_inlineFragment_some_groundLift_apply_disjoint
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType liftParent typeCondition : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source
      typeCondition = true ->
    executableGroupNamesDisjoint
      (Execution.collectFields schema variableValues parentType source
        (groundLiftSelectionSet schema typeCondition selectionSet))
      (Execution.collectFields schema variableValues parentType source
        (groundLiftSelectionSet schema liftParent rest)) ->
    executableGroupNamesDisjoint
      (Execution.collectFields schema variableValues parentType source
        selectionSet)
      (Execution.collectFields schema variableValues parentType source rest) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (groundLiftSelectionSet schema typeCondition selectionSet)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source selectionSet ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (groundLiftSelectionSet schema liftParent rest)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source rest ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (groundLiftSelectionSet schema liftParent
          (Selection.inlineFragment (some typeCondition) [] selectionSet
            :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet
          :: rest) := by
  intro happly hnormalizedDisjoint horiginalDisjoint hselection hrest
  rw [groundLiftSelectionSet, groundLiftSelection]
  rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten]
  · rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten]
    · exact executeSelectionSet_append_eq_of_parts_namesDisjoint schema
        resolvers variableValues depth parentType source
        (groundLiftSelectionSet schema typeCondition selectionSet)
        selectionSet
        (groundLiftSelectionSet schema liftParent rest) rest
        hnormalizedDisjoint horiginalDisjoint hselection hrest
    · exact happly
  · exact happly

theorem mergedFieldSelectionSet_field_head_eq_validFieldsWithResponseName
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.Value ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField)) :
    let sourceField : Execution.ExecutableField :=
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
    }
    objectTypeNameBool schema parentType = true ->
    (∃ runtimeType ref,
      source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
    selectionSetDirectiveFree
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    Execution.collectFields schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      =
    (responseName, sourceField :: sourceFields) :: sourceRest ->
      Execution.mergedFieldSelectionSet (sourceField :: sourceFields)
        =
      subselections
        ++ mergeSelectionSets
          (validFieldsWithResponseName schema parentType responseName rest) := by
  intro sourceField hobject hsource hfree hsourceCollect
  have hsourceValue :
      ∃ runtimeType ref,
        source = .object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    rcases hsource with ⟨runtimeType, ref, hsourceEq, hinclude⟩
    subst source
    exact ⟨runtimeType, ref, by simp [], hinclude⟩
  have hprojection :=
    collectFields_validFieldsWithResponseName_responseSelection schema
      variableValues parentType source responseName
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hobject hsourceValue hfree
  simp [collectedResponseSelectionSet, hsourceCollect,
    validFieldsWithResponseName, mergeSelectionSets,
    Selection.subselections] at hprojection
  simpa [sourceField] using hprojection

theorem mergedFieldSelectionSet_groundLift_field_head_eq_scopedValidFields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (execParent liftParent : Name)
    (source : Execution.Value ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection)
    (liftedFields : List Execution.ExecutableField)
    (liftedRestGroups : List (Name × List Execution.ExecutableField))
    (liftFieldDefinition : FieldDefinition) :
    let liftedSelectionSet :=
      if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
        []
      else if objectTypeNameBool schema liftFieldDefinition.outputType.namedType
      then
        groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
          subselections
      else
        (groundObjectTypesForType schema
          liftFieldDefinition.outputType.namedType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType subselections))
    let liftedField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := liftedSelectionSet
    }
    objectTypeNameBool schema execParent = true ->
    (∃ runtimeType ref,
      source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool execParent runtimeType = true) ->
    selectionSetDirectiveFree
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    Execution.collectFields schema variableValues execParent source
      (groundLiftSelectionSet schema liftParent
        (Selection.field responseName fieldName arguments [] subselections
          :: rest))
      =
    (responseName, liftedField :: liftedFields) :: liftedRestGroups ->
      Execution.mergedFieldSelectionSet (liftedField :: liftedFields)
        =
      liftedSelectionSet
        ++ mergeSelectionSets
          (groundLiftScopedSelectionSet schema
            (scopedValidFieldsWithResponseName schema execParent
              responseName liftParent rest)) := by
  intro liftedSelectionSet liftedField hobject hsource hfree hlookup
    hliftCollect
  have hliftFree :
      selectionSetDirectiveFree
        (groundLiftSelectionSet schema liftParent
          (Selection.field responseName fieldName arguments [] subselections
            :: rest)) :=
    groundLiftSelectionSet_directiveFree schema liftParent
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hfree
  have hliftCollectHead :
      Execution.collectFields schema variableValues execParent source
        (Selection.field responseName fieldName arguments []
          liftedSelectionSet
          :: groundLiftSelectionSet schema liftParent rest)
      =
      (responseName, liftedField :: liftedFields) :: liftedRestGroups := by
    simpa [groundLiftSelectionSet, groundLiftSelection, hlookup,
      liftedSelectionSet, liftedField] using hliftCollect
  have hprojection :=
    mergedFieldSelectionSet_field_head_eq_validFieldsWithResponseName schema
      variableValues execParent source responseName fieldName arguments
      liftedSelectionSet (groundLiftSelectionSet schema liftParent rest)
      liftedFields liftedRestGroups hobject hsource
      (by
        simpa [groundLiftSelectionSet, groundLiftSelection, hlookup,
          liftedSelectionSet] using hliftFree)
      hliftCollectHead
  have hprojection' := hprojection
  rw [validFieldsWithResponseName_groundLiftSelectionSet_scoped schema
    execParent responseName liftParent rest] at hprojection'
  simpa [liftedField] using hprojection'

theorem mergedFieldSelectionSet_groundLift_scoped_field_head_eq_validFields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (execParent liftParent : Name)
    (source : Execution.Value ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection)
    (liftedFields : List Execution.ExecutableField)
    (liftedRestGroups : List (Name × List Execution.ExecutableField))
    (liftFieldDefinition : FieldDefinition) :
    let liftedSelectionSet :=
      if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
        []
      else if objectTypeNameBool schema liftFieldDefinition.outputType.namedType
      then
        groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
          subselections
      else
        (groundObjectTypesForType schema
          liftFieldDefinition.outputType.namedType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType subselections))
    let liftedField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := liftedSelectionSet
    }
    objectTypeNameBool schema execParent = true ->
    (∃ runtimeType ref,
      source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool execParent runtimeType = true) ->
    scopedSelectionSetDirectiveFree
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    Execution.collectFields schema variableValues execParent source
      (groundLiftScopedSelectionSet schema
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] subselections }
          :: rest))
      =
    (responseName, liftedField :: liftedFields) :: liftedRestGroups ->
      Execution.mergedFieldSelectionSet (liftedField :: liftedFields)
        =
      liftedSelectionSet
        ++ mergeSelectionSets
          (groundLiftScopedSelectionSet schema
            (scopedSelectionSetValidFieldsWithResponseName schema execParent
              responseName rest)) := by
  intro liftedSelectionSet liftedField hobject hsource hfree hlookup
    hliftCollect
  have hliftFree :
      selectionSetDirectiveFree
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments [] subselections }
            :: rest)) :=
    groundLiftScopedSelectionSet_directiveFree schema
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest)
      hfree
  have hliftCollectHead :
      Execution.collectFields schema variableValues execParent source
        (Selection.field responseName fieldName arguments []
          liftedSelectionSet
          :: groundLiftScopedSelectionSet schema rest)
      =
      (responseName, liftedField :: liftedFields) :: liftedRestGroups := by
    simpa [groundLiftScopedSelectionSet, groundLiftScopedSelection,
      groundLiftSelection, hlookup, liftedSelectionSet, liftedField]
      using hliftCollect
  have hprojection :=
    mergedFieldSelectionSet_field_head_eq_validFieldsWithResponseName schema
      variableValues execParent source responseName fieldName arguments
      liftedSelectionSet (groundLiftScopedSelectionSet schema rest)
      liftedFields liftedRestGroups hobject hsource
      (by
        simpa [groundLiftScopedSelectionSet, groundLiftScopedSelection,
          groundLiftSelection, hlookup, liftedSelectionSet] using hliftFree)
      hliftCollectHead
  have hprojection' := hprojection
  rw [validFieldsWithResponseName_groundLiftScopedSelectionSet schema
    execParent responseName rest] at hprojection'
  simpa [liftedField] using hprojection'

theorem completeValue_groundLift_scopedMerged_eq_of_child_lt
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (fieldDepth : Nat) (execParent _liftParent runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection)
    (liftFieldDefinition : FieldDefinition) :
    let liftedSelectionSet :=
      if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
        []
      else if objectTypeNameBool schema liftFieldDefinition.outputType.namedType
      then
        groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
          subselections
      else
        (groundObjectTypesForType schema
          liftFieldDefinition.outputType.namedType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType subselections))
    (∀ childDepth childRuntimeType ref,
      childDepth < fieldDepth ->
      schema.typeIncludesObjectBool
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          childRuntimeType = true ->
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth childRuntimeType
          (.object childRuntimeType ref)
          (liftedSelectionSet
            ++ mergeSelectionSets
              (groundLiftScopedSelectionSet schema
                (scopedSelectionSetValidFieldsWithResponseName schema
                  execParent responseName rest)))
        =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth childRuntimeType
          (.object childRuntimeType ref)
          (subselections
            ++ mergeSelectionSets
              (eraseScopedSelectionSet
                (scopedSelectionSetValidFieldsWithResponseName schema
                  execParent responseName rest)))) ->
      Execution.completeValue schema (store.resolvers schema) variableValues
        fieldDepth
        ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        [completeValueSelectionSetField
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          (liftedSelectionSet
            ++ mergeSelectionSets
              (groundLiftScopedSelectionSet schema
                (scopedSelectionSetValidFieldsWithResponseName schema execParent
                  responseName rest)))]
        ((store.resolvers schema).resolve execParent fieldName arguments
          (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
            runtimeType))
      =
      Execution.completeValue schema (store.resolvers schema) variableValues
        fieldDepth
        ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        [completeValueSelectionSetField
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          (subselections
            ++ mergeSelectionSets
              (eraseScopedSelectionSet
                (scopedSelectionSetValidFieldsWithResponseName schema execParent
                  responseName rest)))]
        ((store.resolvers schema).resolve execParent fieldName arguments
          (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
            runtimeType)) := by
  intro liftedSelectionSet hrecursive
  apply completeValue_eq_of_child_object_lt_includes schema
    (store.resolvers schema) variableValues fieldDepth
    ((schema.fieldReturnType? execParent fieldName).getD fieldName)
    [completeValueSelectionSetField
      ((schema.fieldReturnType? execParent fieldName).getD fieldName)
      (liftedSelectionSet
        ++ mergeSelectionSets
          (groundLiftScopedSelectionSet schema
            (scopedSelectionSetValidFieldsWithResponseName schema execParent
              responseName rest)))]
    [completeValueSelectionSetField
      ((schema.fieldReturnType? execParent fieldName).getD fieldName)
      (subselections
        ++ mergeSelectionSets
          (eraseScopedSelectionSet
            (scopedSelectionSetValidFieldsWithResponseName schema execParent
              responseName rest)))]
        ((store.resolvers schema).resolve execParent fieldName arguments
      (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
        runtimeType))
  intro childDepth childRuntimeType ref hlt hinclude
  simpa [Execution.mergedFieldSelectionSet,
    completeValueSelectionSetField] using
    hrecursive childDepth childRuntimeType ref hlt hinclude

theorem executeSelectionSet_field_head_groundLift_scoped_sameGroup_of_completeValue
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (fieldDepth : Nat) (execParent liftParent runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection)
    (liftedFields sourceFields : List Execution.ExecutableField)
    (liftedRestGroups sourceRest : List (Name × List Execution.ExecutableField))
    (execFieldDefinition liftFieldDefinition : FieldDefinition)
    (ref : Option DataModel.ObjectRef := none) :
    let liftedSelectionSet :=
      if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
        []
      else if objectTypeNameBool schema liftFieldDefinition.outputType.namedType
      then
        groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
          subselections
      else
        (groundObjectTypesForType schema
          liftFieldDefinition.outputType.namedType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType subselections))
    let liftedField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := liftedSelectionSet
      }
    let sourceField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
    objectTypeNameBool schema execParent = true ->
    schema.typeIncludesObjectBool execParent runtimeType = true ->
    scopedSelectionSetDirectiveFree
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    Execution.collectFields schema variableValues execParent
      (Execution.Value.object runtimeType ref)
      (groundLiftScopedSelectionSet schema
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] subselections }
          :: rest))
      =
    (responseName, liftedField :: liftedFields) :: liftedRestGroups ->
    Execution.collectFields schema variableValues execParent
      (Execution.Value.object runtimeType ref)
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest)
      =
    (responseName, sourceField :: sourceFields) :: sourceRest ->
    Execution.completeValue schema (store.resolvers schema) variableValues
      fieldDepth
      ((schema.fieldReturnType? execParent fieldName).getD fieldName)
      (liftedField :: liftedFields)
      ((store.resolvers schema).resolve execParent fieldName arguments
        (Execution.Value.object runtimeType ref))
      =
    Execution.completeValue schema (store.resolvers schema) variableValues
      fieldDepth
      ((schema.fieldReturnType? execParent fieldName).getD fieldName)
      (sourceField :: sourceFields)
      ((store.resolvers schema).resolve execParent fieldName arguments
        (Execution.Value.object runtimeType ref)) ->
    Execution.executeCollectedFields schema (store.resolvers schema)
      variableValues (fieldDepth + 1) (.object runtimeType ref)
      liftedRestGroups
      =
    Execution.executeCollectedFields schema (store.resolvers schema)
      variableValues (fieldDepth + 1) (.object runtimeType ref)
      sourceRest ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues (fieldDepth + 1) execParent
        (Execution.Value.object runtimeType ref)
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments []
                subselections }
            :: rest))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues (fieldDepth + 1) execParent
        (Execution.Value.object runtimeType ref)
        (Selection.field responseName fieldName arguments [] subselections
          :: eraseScopedSelectionSet rest) := by
  intro liftedSelectionSet liftedField sourceField hobject hinclude hfree
    _hexecLookup hliftLookup hliftCollect hsourceCollect hcomplete htail
  have hsource :
      ∃ runtimeType' objectRef,
        Execution.Value.object runtimeType ref
          = .object runtimeType' objectRef
          ∧ schema.typeIncludesObjectBool execParent runtimeType' = true :=
    ⟨runtimeType, ref, rfl, hinclude⟩
  have hsourceFree :
      selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments [] subselections
          :: eraseScopedSelectionSet rest) := by
    simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet,
      eraseScopedSelection] using hfree
  have hliftProjection :=
    mergedFieldSelectionSet_groundLift_scoped_field_head_eq_validFields schema
      variableValues execParent liftParent
      (Execution.Value.object runtimeType ref)
      responseName fieldName arguments subselections rest liftedFields
      liftedRestGroups liftFieldDefinition hobject hsource hfree hliftLookup
      (by simpa [liftedField] using hliftCollect)
  have hsourceProjection :=
    mergedFieldSelectionSet_field_head_eq_validFieldsWithResponseName schema
      variableValues execParent (Execution.Value.object runtimeType ref)
      responseName
      fieldName arguments subselections (eraseScopedSelectionSet rest)
      sourceFields sourceRest hobject hsource hsourceFree
      (by simpa [sourceField] using hsourceCollect)
  apply Execution.executeSelectionSet_field_head_same_group_eq_of_completeValue schema
    (store.resolvers schema) variableValues fieldDepth execParent
    (Execution.Value.object runtimeType ref) responseName fieldName
    arguments
    liftedSelectionSet subselections
    (groundLiftScopedSelectionSet schema
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest))
    (Selection.field responseName fieldName arguments [] subselections
      :: eraseScopedSelectionSet rest)
    liftedFields sourceFields liftedRestGroups sourceRest
  · simpa [liftedField] using hliftCollect
  · simpa [sourceField] using hsourceCollect
  · exact hcomplete
  · exact htail

theorem executeCollectedFields_groundLift_scoped_fieldHead_tail_eq_of_withoutFields
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (execParent liftParent runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection)
    (liftedFields sourceFields : List Execution.ExecutableField)
    (liftedRestGroups sourceRest : List (Name × List Execution.ExecutableField))
    (liftFieldDefinition : FieldDefinition)
    (ref : Option DataModel.ObjectRef := none) :
    let liftedSelectionSet :=
      if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
        []
      else if objectTypeNameBool schema liftFieldDefinition.outputType.namedType
      then
        groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
          subselections
      else
        (groundObjectTypesForType schema
          liftFieldDefinition.outputType.namedType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType subselections))
    let liftedField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := liftedSelectionSet
      }
    let sourceField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
    objectTypeNameBool schema execParent = true ->
    schema.typeIncludesObjectBool execParent runtimeType = true ->
    scopedSelectionSetDirectiveFree
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    Execution.collectFields schema variableValues execParent
      (Execution.Value.object runtimeType ref)
      (groundLiftScopedSelectionSet schema
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] subselections }
          :: rest))
      =
    (responseName, liftedField :: liftedFields) :: liftedRestGroups ->
    Execution.collectFields schema variableValues execParent
      (Execution.Value.object runtimeType ref)
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest)
      =
    (responseName, sourceField :: sourceFields) :: sourceRest ->
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent
      (Execution.Value.object runtimeType ref)
      (groundLiftScopedSelectionSet schema
        (scopedSelectionSetWithoutFieldsWithResponseName schema responseName
          rest))
      =
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent
      (Execution.Value.object runtimeType ref)
      (eraseScopedSelectionSet
        (scopedSelectionSetWithoutFieldsWithResponseName schema responseName
          rest)) ->
      Execution.executeCollectedFields schema (store.resolvers schema)
        variableValues depth (Execution.Value.object runtimeType ref)
        liftedRestGroups
      =
      Execution.executeCollectedFields schema (store.resolvers schema)
        variableValues depth (Execution.Value.object runtimeType ref)
        sourceRest := by
  intro liftedSelectionSet liftedField sourceField hobject hinclude hfree
    hliftLookup hliftCollect hsourceCollect htailSelection
  have hsource :
      ∃ runtimeType' objectRef,
        Execution.Value.object runtimeType ref
          = .object runtimeType' objectRef
          ∧ schema.typeIncludesObjectBool execParent runtimeType' = true :=
    ⟨runtimeType, ref, rfl, hinclude⟩
  have hsourceValue :
      ∃ runtimeType' objectRef,
        Execution.Value.object runtimeType ref = .object runtimeType' objectRef
          ∧ schema.typeIncludesObjectBool execParent runtimeType' = true :=
    ⟨runtimeType, ref, rfl, hinclude⟩
  have hsourceFree :
      selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments [] subselections
          :: eraseScopedSelectionSet rest) := by
    simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet,
      eraseScopedSelection] using hfree
  have hsourceRestCollect :
      Execution.collectFields schema variableValues execParent
        (Execution.Value.object runtimeType ref)
        (withoutFieldsWithResponseName schema responseName
          (eraseScopedSelectionSet rest))
      =
      sourceRest := by
    simpa [sourceField] using
      collectFields_withoutFieldsWithResponseName_fieldHead_rest_eq_sourceRest
        schema variableValues execParent (Execution.Value.object runtimeType ref)
        responseName fieldName arguments subselections
        (eraseScopedSelectionSet rest) sourceFields sourceRest hobject
        hsourceValue hsourceFree hsourceCollect
  have hliftFullFree :
      selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments [] liftedSelectionSet
          :: groundLiftScopedSelectionSet schema rest) := by
    have hliftFullFreeRaw :
        selectionSetDirectiveFree
          (groundLiftScopedSelectionSet schema
            ({ liftParent := liftParent,
               selection :=
                Selection.field responseName fieldName arguments []
                  subselections }
              :: rest)) :=
      groundLiftScopedSelectionSet_directiveFree schema
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] subselections }
          :: rest)
        hfree
    simpa [groundLiftScopedSelectionSet, groundLiftScopedSelection,
      groundLiftSelection, hliftLookup, liftedSelectionSet] using
      hliftFullFreeRaw
  have hliftCollectHead :
      Execution.collectFields schema variableValues execParent
        (Execution.Value.object runtimeType ref)
        (Selection.field responseName fieldName arguments [] liftedSelectionSet
          :: groundLiftScopedSelectionSet schema rest)
      =
      (responseName, liftedField :: liftedFields) :: liftedRestGroups := by
    simpa [groundLiftScopedSelectionSet, groundLiftScopedSelection,
      groundLiftSelection, hliftLookup, liftedSelectionSet, liftedField]
      using hliftCollect
  have hliftRestCollectRaw :
      Execution.collectFields schema variableValues execParent
        (Execution.Value.object runtimeType ref)
        (withoutFieldsWithResponseName schema responseName
          (groundLiftScopedSelectionSet schema rest))
      =
      liftedRestGroups := by
    simpa [liftedField] using
      collectFields_withoutFieldsWithResponseName_fieldHead_rest_eq_sourceRest
        schema variableValues execParent (Execution.Value.object runtimeType ref)
        responseName fieldName arguments liftedSelectionSet
        (groundLiftScopedSelectionSet schema rest) liftedFields
        liftedRestGroups hobject hsourceValue hliftFullFree hliftCollectHead
  have hliftRestCollect :
      Execution.collectFields schema variableValues execParent
        (Execution.Value.object runtimeType ref)
        (groundLiftScopedSelectionSet schema
          (scopedSelectionSetWithoutFieldsWithResponseName schema responseName
            rest))
      =
      liftedRestGroups := by
    simpa [groundLiftScopedSelectionSet_withoutFieldsWithResponseName schema
      responseName rest] using hliftRestCollectRaw
  have hsourceRestCollectScoped :
      Execution.collectFields schema variableValues execParent
        (Execution.Value.object runtimeType ref)
        (eraseScopedSelectionSet
          (scopedSelectionSetWithoutFieldsWithResponseName schema responseName
            rest))
      =
      sourceRest := by
    simpa [eraseScopedSelectionSet_withoutFieldsWithResponseName schema
      responseName rest] using hsourceRestCollect
  simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hliftRestCollect,
    hsourceRestCollectScoped] using htailSelection

theorem executeSelectionSet_field_head_groundLift_scoped_sameGroup_of_child_lt
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (fieldDepth : Nat) (execParent liftParent runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection)
    (liftedFields sourceFields : List Execution.ExecutableField)
    (liftedRestGroups sourceRest : List (Name × List Execution.ExecutableField))
    (execFieldDefinition liftFieldDefinition : FieldDefinition) :
    let liftedSelectionSet :=
      if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
        []
      else if objectTypeNameBool schema liftFieldDefinition.outputType.namedType
      then
        groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
          subselections
      else
        (groundObjectTypesForType schema
          liftFieldDefinition.outputType.namedType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType subselections))
    let liftedField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := liftedSelectionSet
      }
    let sourceField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
    objectTypeNameBool schema execParent = true ->
    schema.typeIncludesObjectBool execParent runtimeType = true ->
    scopedSelectionSetDirectiveFree
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    Execution.collectFields schema variableValues execParent
      (Execution.Value.object (ObjectRef := DataModel.ObjectRef) runtimeType)
      (groundLiftScopedSelectionSet schema
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] subselections }
          :: rest))
      =
    (responseName, liftedField :: liftedFields) :: liftedRestGroups ->
    Execution.collectFields schema variableValues execParent
      (Execution.Value.object (ObjectRef := DataModel.ObjectRef) runtimeType)
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest)
      =
    (responseName, sourceField :: sourceFields) :: sourceRest ->
    (∀ childDepth childRuntimeType ref,
      childDepth < fieldDepth ->
      schema.typeIncludesObjectBool
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          childRuntimeType = true ->
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth childRuntimeType
          (.object childRuntimeType ref)
          (liftedSelectionSet
            ++ mergeSelectionSets
              (groundLiftScopedSelectionSet schema
                (scopedSelectionSetValidFieldsWithResponseName schema
                  execParent responseName rest)))
        =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth childRuntimeType
          (.object childRuntimeType ref)
          (subselections
            ++ mergeSelectionSets
              (eraseScopedSelectionSet
                (scopedSelectionSetValidFieldsWithResponseName schema
                  execParent responseName rest)))) ->
    Execution.executeCollectedFields schema (store.resolvers schema)
      variableValues (fieldDepth + 1)
      (Execution.Value.object (ObjectRef := DataModel.ObjectRef) runtimeType)
      liftedRestGroups
      =
    Execution.executeCollectedFields schema (store.resolvers schema)
      variableValues (fieldDepth + 1)
      (Execution.Value.object (ObjectRef := DataModel.ObjectRef) runtimeType)
      sourceRest ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues (fieldDepth + 1) execParent
        (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
          runtimeType)
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments []
                subselections }
            :: rest))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues (fieldDepth + 1) execParent
        (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
          runtimeType)
        (Selection.field responseName fieldName arguments [] subselections
          :: eraseScopedSelectionSet rest) := by
  intro liftedSelectionSet liftedField sourceField hobject hinclude hfree
    hexecLookup hliftLookup hliftCollect hsourceCollect hrecursive htail
  apply executeSelectionSet_field_head_groundLift_scoped_sameGroup_of_completeValue
    schema store variableValues fieldDepth execParent liftParent runtimeType
    responseName fieldName arguments subselections rest liftedFields
    sourceFields liftedRestGroups sourceRest execFieldDefinition
    liftFieldDefinition (ref := (none : Option DataModel.ObjectRef))
      hobject hinclude hfree hexecLookup hliftLookup
    hliftCollect hsourceCollect
  · exact
      completeValue_eq_of_child_object_lt_includes schema
        (store.resolvers schema) variableValues fieldDepth
        ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        (liftedField :: liftedFields) (sourceField :: sourceFields)
          ((store.resolvers schema).resolve execParent fieldName arguments
          (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
            runtimeType))
        (by
          intro childDepth childRuntimeType ref hlt hincludeChild
          have hsource :
              ∃ runtimeType' ref,
                Execution.Value.object (ObjectRef := DataModel.ObjectRef)
                  runtimeType
                  = .object runtimeType' ref
                  ∧ schema.typeIncludesObjectBool execParent runtimeType' = true :=
            ⟨runtimeType, (none : Option DataModel.ObjectRef), rfl, hinclude⟩
          have hsourceFree :
              selectionSetDirectiveFree
                (Selection.field responseName fieldName arguments []
                  subselections :: eraseScopedSelectionSet rest) := by
            simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet,
              eraseScopedSelection] using hfree
          have hliftProjection :=
            mergedFieldSelectionSet_groundLift_scoped_field_head_eq_validFields
              schema variableValues execParent liftParent
              (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
                runtimeType) responseName
              fieldName arguments
              subselections rest liftedFields liftedRestGroups
              liftFieldDefinition hobject hsource hfree hliftLookup
              (by
                simpa [liftedField]
                  using hliftCollect)
          have hsourceProjection :=
            mergedFieldSelectionSet_field_head_eq_validFieldsWithResponseName
              schema variableValues execParent
              (Execution.Value.object (ObjectRef := DataModel.ObjectRef)
                runtimeType)
              responseName fieldName arguments subselections
              (eraseScopedSelectionSet rest) sourceFields sourceRest hobject
              hsource hsourceFree
              (by
                simpa [sourceField]
                  using hsourceCollect)
          rw [hliftProjection, hsourceProjection]
          simpa [eraseScopedSelectionSet_validFieldsWithResponseName schema
            execParent responseName rest] using
            hrecursive childDepth childRuntimeType ref hlt
              hincludeChild)
  · exact htail

end GroundTypeLifting

end NormalForm

end GraphQL
