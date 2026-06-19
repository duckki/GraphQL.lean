import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Core
import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Validation
import GraphQL.NormalForm.GroundTypeNormalization.Validity.Support.FieldHeads
import GraphQL.NormalForm.Shared.LookupValidity
import GraphQL.NormalForm.Shared.SemanticReadiness

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def collectedExecutableFields :
    List (Name × List ExecutableField) -> List ExecutableField
  | [] => []
  | (_responseName, fields) :: rest =>
      fields ++ collectedExecutableFields rest

theorem collectedExecutableFields_append
    (left right : List (Name × List ExecutableField)) :
    collectedExecutableFields (left ++ right) =
      collectedExecutableFields left ++ collectedExecutableFields right := by
  induction left with
  | nil =>
      simp [collectedExecutableFields]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [collectedExecutableFields, ih, List.append_assoc]

theorem collectedExecutableFields_addExecutableGroup_length
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    (collectedExecutableFields
      (GraphQL.Execution.addExecutableGroup group groups)).length =
      group.snd.length + (collectedExecutableFields groups).length := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hname, List.length_append]
        omega
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hfalse, ih, List.length_append]
        omega

theorem collectedExecutableFields_mergeExecutableGroups_length
    (left right : List (Name × List ExecutableField)) :
    (collectedExecutableFields
      (GraphQL.Execution.mergeExecutableGroups left right)).length =
      (collectedExecutableFields left).length +
        (collectedExecutableFields right).length := by
  induction right generalizing left with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      change
        (collectedExecutableFields
          (GraphQL.Execution.mergeExecutableGroups
            (GraphQL.Execution.addExecutableGroup (responseName, fields) left)
            rest)).length =
          (collectedExecutableFields left).length +
            (fields ++ collectedExecutableFields rest).length
      rw [ih]
      rw [collectedExecutableFields_addExecutableGroup_length]
      simp [List.length_append]
      omega

theorem addExecutableGroup_key_mem
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) (responseName : Name) :
    responseName ∈
        (GraphQL.Execution.addExecutableGroup group groups).map Prod.fst ↔
      responseName = group.fst ∨ responseName ∈ groups.map Prod.fst := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have hcurrent : currentName = groupName := beq_iff_eq.mp hname
        simp [GraphQL.Execution.addExecutableGroup, hcurrent]
      · have hfalse : (currentName == groupName) = false := by
          cases h : currentName == groupName
          · rfl
          · contradiction
        simp [GraphQL.Execution.addExecutableGroup, hfalse, ih]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hgroupOrRest
          · exact Or.inr (by simp [hcurrent])
          · rcases hgroupOrRest with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (by simp [hrest])
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (Or.inl hgroup)
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (Or.inr hrest)

theorem mergeExecutableGroups_key_mem
    (left right : List (Name × List ExecutableField)) (responseName : Name) :
    responseName ∈
        (GraphQL.Execution.mergeExecutableGroups left right).map Prod.fst ↔
      responseName ∈ left.map Prod.fst ∨ responseName ∈ right.map Prod.fst := by
  induction right generalizing left with
  | nil =>
      simp [GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change
        responseName ∈
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.addExecutableGroup group left) rest).map
              Prod.fst ↔
          responseName ∈ left.map Prod.fst ∨
            responseName ∈ (group :: rest).map Prod.fst
      rw [ih]
      rw [addExecutableGroup_key_mem group left responseName]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · intro hmem
        rcases hmem with hgroupOrLeft | hrest
        · rcases hgroupOrLeft with hgroup | hleft
          · exact Or.inr (Or.inl hgroup)
          · exact Or.inl hleft
        · exact Or.inr (Or.inr hrest)
      · intro hmem
        rcases hmem with hleft | hgroupOrRest
        · exact Or.inl (Or.inr hleft)
        · rcases hgroupOrRest with hgroup | hrest
          · exact Or.inl (Or.inl hgroup)
          · exact Or.inr hrest

theorem collectedExecutableFields_mergeExecutableGroups_eq_append_of_namesDisjoint
    (left right : List (Name × List ExecutableField)) :
    GraphQL.NormalForm.executableGroupNamesDisjoint left right ->
    GraphQL.NormalForm.executableGroupNamesNodup right ->
      collectedExecutableFields
          (GraphQL.Execution.mergeExecutableGroups left right) =
        collectedExecutableFields left ++ collectedExecutableFields right := by
  intro hdisjoint hnodup
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
    left right hdisjoint hnodup]
  exact collectedExecutableFields_append left right

theorem collectedExecutableFields_merge_single_duplicate_around_disjoint
    (responseName : Name) (first later : ExecutableField)
    (middleGroups : List (Name × List ExecutableField)) :
    responseName ∉ middleGroups.map Prod.fst ->
    GraphQL.NormalForm.executableGroupNamesNodup middleGroups ->
      collectedExecutableFields
          (GraphQL.Execution.mergeExecutableGroups
            [(responseName, [first])]
            (middleGroups ++ [(responseName, [later])])) =
        [first, later] ++ collectedExecutableFields middleGroups := by
  intro hnotMiddle hmiddleNodup
  have hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        [(responseName, [first])] middleGroups := by
    intro candidate hleft hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  unfold GraphQL.Execution.mergeExecutableGroups
  rw [List.foldl_append]
  change
    collectedExecutableFields
        (GraphQL.Execution.addExecutableGroup (responseName, [later])
          (GraphQL.Execution.mergeExecutableGroups [(responseName, [first])]
            middleGroups)) =
      [first, later] ++ collectedExecutableFields middleGroups
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
    [(responseName, [first])] middleGroups hdisjoint hmiddleNodup]
  simp [GraphQL.Execution.addExecutableGroup, collectedExecutableFields]

theorem collectedExecutableFields_merge_group_duplicate_around_disjoint
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (middleGroups : List (Name × List ExecutableField)) :
    responseName ∉ middleGroups.map Prod.fst ->
    GraphQL.NormalForm.executableGroupNamesNodup middleGroups ->
      collectedExecutableFields
          (GraphQL.Execution.mergeExecutableGroups
            [(responseName, prefixFields)]
            (middleGroups ++ [(responseName, [later])])) =
        (prefixFields ++ [later]) ++ collectedExecutableFields middleGroups := by
  intro hnotMiddle hmiddleNodup
  have hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        [(responseName, prefixFields)] middleGroups := by
    intro candidate hleft hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  unfold GraphQL.Execution.mergeExecutableGroups
  rw [List.foldl_append]
  change
    collectedExecutableFields
        (GraphQL.Execution.addExecutableGroup (responseName, [later])
          (GraphQL.Execution.mergeExecutableGroups [(responseName, prefixFields)]
            middleGroups)) =
      (prefixFields ++ [later]) ++ collectedExecutableFields middleGroups
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
    [(responseName, prefixFields)] middleGroups hdisjoint hmiddleNodup]
  simp [GraphQL.Execution.addExecutableGroup, collectedExecutableFields,
    List.append_assoc]

theorem executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection) :
    later.responseName = first.responseName ->
    first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType source
          middle).map Prod.fst ->
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
                source middle)) := by
  intro hsame hnotMiddle
  let firstCollected : ExecutableField :=
    executableField parentType first.responseName first.fieldName
      first.arguments first.selectionSet
  let laterCollected : ExecutableField :=
    executableField parentType later.responseName later.fieldName
      later.arguments later.selectionSet
  let middleGroups :=
    GraphQL.Execution.collectFields schema variableValues parentType source
      middle
  have hfirstCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections [first]) =
      [(first.responseName, [firstCollected])] := by
    simp [executableFieldSelections, executableFieldSelection, firstCollected,
      executableField, GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      selectionDirectivesAllowBool_empty]
  have hlaterCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections [later]) =
      [(later.responseName, [laterCollected])] := by
    simp [executableFieldSelections, executableFieldSelection, laterCollected,
      executableField, GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      selectionDirectivesAllowBool_empty]
  have hmiddleLater :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (middle ++ executableFieldSelections [later]) =
        middleGroups ++ [(later.responseName, [laterCollected])] := by
    rw [GraphQL.NormalForm.collectFields_append]
    rw [hlaterCollect]
    have hdisjoint :
        GraphQL.NormalForm.executableGroupNamesDisjoint middleGroups
          [(later.responseName, [laterCollected])] := by
      intro responseName hmiddle hsingle
      simp at hsingle
      exact hnotMiddle (by simpa [middleGroups, hsingle, hsame] using hmiddle)
    rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
      middleGroups [(later.responseName, [laterCollected])] hdisjoint
      (by simp [GraphQL.NormalForm.executableGroupNamesNodup])]
  rw [show
      executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later] =
        executableFieldSelections [first] ++
          (middle ++ executableFieldSelections [later]) by
    simp [List.append_assoc]]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [hfirstCollect, hmiddleLater]
  have hmiddleNodup :
      GraphQL.NormalForm.executableGroupNamesNodup middleGroups := by
    exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source middle
  have hnotMiddle' :
      first.responseName ∉ middleGroups.map Prod.fst := by
    simpa [middleGroups] using hnotMiddle
  rw [hsame]
  rw [collectedExecutableFields_merge_single_duplicate_around_disjoint
    first.responseName firstCollected laterCollected middleGroups hnotMiddle'
    hmiddleNodup]
  simp [executableFieldSelections, executableFieldSelection, firstCollected,
    laterCollected, executableField, middleGroups, hsame]

theorem executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle : List Selection) :
    prefixFields ≠ [] ->
    (∀ field, field ∈ prefixFields -> field.responseName = responseName) ->
    later.responseName = responseName ->
    responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType source
          middle).map Prod.fst ->
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++ middle ++
                executableFieldSelections [later]))) =
        executableFieldSelections (prefixFields ++ [later]) ++
          executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle)) := by
  intro hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  cases prefixFields with
  | nil =>
      exact False.elim (hprefixNonempty rfl)
  | cons firstPrefix restPrefix =>
      let collectedField : ExecutableField -> ExecutableField :=
        fun field =>
          executableField parentType field.responseName field.fieldName
            field.arguments field.selectionSet
      let collectedPrefix : List ExecutableField :=
        (firstPrefix :: restPrefix).map collectedField
      let laterCollected : ExecutableField :=
        executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet
      let middleGroups :=
        GraphQL.Execution.collectFields schema variableValues parentType source
          middle
      have hprefixSelections :
          executableFieldSelections collectedPrefix =
            executableFieldSelections (firstPrefix :: restPrefix) := by
        simp [collectedPrefix, collectedField, executableFieldSelections,
          executableFieldSelection, executableField, List.map_map]
      have hcollectedPrefixResponse :
          ∀ field, field ∈ collectedPrefix ->
            field.responseName = responseName := by
        intro field hfield
        rcases List.mem_map.mp hfield with ⟨sourceField, hsource, hfieldEq⟩
        subst field
        exact hprefixResponse sourceField hsource
      have hcollectedPrefixParent :
          ∀ field, field ∈ collectedPrefix -> field.parentType = parentType := by
        intro field hfield
        rcases List.mem_map.mp hfield with ⟨sourceField, _hsource, hfieldEq⟩
        subst field
        rfl
      have hprefixCollect :
          GraphQL.Execution.collectFields schema variableValues parentType source
              (executableFieldSelections (firstPrefix :: restPrefix)) =
            [(responseName, collectedPrefix)] := by
        rw [← hprefixSelections]
        simpa [collectedPrefix] using
          collectFields_executableFieldSelections_same_group schema
            variableValues parentType source responseName collectedPrefix
            hcollectedPrefixResponse hcollectedPrefixParent
      have hlaterCollect :
          GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [later]) =
          [(later.responseName, [laterCollected])] := by
        simp [executableFieldSelections, executableFieldSelection,
          laterCollected, executableField, GraphQL.Execution.collectFields,
          GraphQL.Execution.collectSelection,
          GraphQL.Execution.mergeExecutableGroups,
          selectionDirectivesAllowBool_empty]
      have hmiddleLater :
          GraphQL.Execution.collectFields schema variableValues parentType source
              (middle ++ executableFieldSelections [later]) =
            middleGroups ++ [(later.responseName, [laterCollected])] := by
        rw [GraphQL.NormalForm.collectFields_append]
        rw [hlaterCollect]
        have hdisjoint :
            GraphQL.NormalForm.executableGroupNamesDisjoint middleGroups
              [(later.responseName, [laterCollected])] := by
          intro candidate hmiddle hsingle
          simp at hsingle
          exact hnotMiddle (by
            simpa [middleGroups, hsingle, hlaterResponse] using hmiddle)
        rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
          middleGroups [(later.responseName, [laterCollected])] hdisjoint
          (by simp [GraphQL.NormalForm.executableGroupNamesNodup])]
      rw [show
          executableFieldSelections (firstPrefix :: restPrefix) ++ middle ++
              executableFieldSelections [later] =
            executableFieldSelections (firstPrefix :: restPrefix) ++
              (middle ++ executableFieldSelections [later]) by
        simp [List.append_assoc]]
      rw [GraphQL.NormalForm.collectFields_append]
      rw [hprefixCollect, hmiddleLater]
      have hmiddleNodup :
          GraphQL.NormalForm.executableGroupNamesNodup middleGroups := by
        exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
          parentType source middle
      have hnotMiddle' :
          responseName ∉ middleGroups.map Prod.fst := by
        simpa [middleGroups] using hnotMiddle
      rw [hlaterResponse]
      rw [collectedExecutableFields_merge_group_duplicate_around_disjoint
        responseName collectedPrefix laterCollected middleGroups hnotMiddle'
        hmiddleNodup]
      simp [executableFieldSelections, executableFieldSelection,
        collectedPrefix, collectedField, laterCollected, executableField,
        middleGroups, hlaterResponse, List.map_map, List.append_assoc]

theorem collectFields_executableFieldSelections_collectedExecutableFields
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) :
    PairKeysNodup groups ->
    CollectedGroupsFieldsNonempty groups ->
    CollectedGroupsResponseName groups ->
    CollectedGroupsParent parentType groups ->
      GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections (collectedExecutableFields groups)) =
      groups := by
  induction groups with
  | nil =>
      intro _hnodup _hnonempty _hresponse _hparent
      simp [collectedExecutableFields, executableFieldSelections,
        GraphQL.Execution.collectFields]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      intro hnodup hnonempty hresponse hparent
      have hrestNodup : PairKeysNodup rest :=
        PairKeysNodup.tail hnodup
      have hfieldsNonempty : fields ≠ [] :=
        hnonempty responseName fields (by simp)
      have hfieldsResponse :
          ExecutableFieldsResponseName responseName fields :=
        hresponse responseName fields (by simp)
      have hfieldsParent :
          ExecutableFieldsParent parentType fields :=
        hparent responseName fields (by simp)
      have hrestResponse : CollectedGroupsResponseName rest :=
        CollectedGroupsResponseName_tail hresponse
      have hrestParent : CollectedGroupsParent parentType rest :=
        CollectedGroupsParent_tail hparent
      have hrestNonempty : CollectedGroupsFieldsNonempty rest := by
        intro restResponseName restFields hmem
        exact hnonempty restResponseName restFields (by simp [hmem])
      cases fields with
      | nil =>
          exact False.elim (hfieldsNonempty rfl)
      | cons field fieldsTail =>
          rw [show
              executableFieldSelections
                  (collectedExecutableFields
                    ((responseName, field :: fieldsTail) :: rest)) =
                executableFieldSelections (field :: fieldsTail) ++
                  executableFieldSelections (collectedExecutableFields rest) by
            simp [collectedExecutableFields, executableFieldSelections]]
          rw [GraphQL.NormalForm.collectFields_append]
          rw [collectFields_executableFieldSelections_same_group schema
            variableValues parentType source responseName (field :: fieldsTail)
            hfieldsResponse hfieldsParent]
          rw [ih hrestNodup hrestNonempty hrestResponse hrestParent]
          have hdisjoint :
              GraphQL.NormalForm.executableGroupNamesDisjoint
                [(responseName, field :: fieldsTail)] rest := by
            exact executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
              hnodup
          have hrestNamesNodup :
              GraphQL.NormalForm.executableGroupNamesNodup rest :=
            executableGroupNamesNodup_of_pairKeysNodup rest hrestNodup
          rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
            [(responseName, field :: fieldsTail)] rest hdisjoint
            hrestNamesNodup]
          simp

theorem collectFields_executableFieldSelections_collectedExecutableFields_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    GraphQL.Execution.collectFields schema variableValues parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) =
    GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet := by
  apply collectFields_executableFieldSelections_collectedExecutableFields
  · exact PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet)
  · exact collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  · exact collectFields_responseName schema variableValues parentType source
      selectionSet
  · exact collectFields_parent schema variableValues parentType source
      selectionSet

theorem collectedExecutableFields_collectFields_executableFieldSelections_length
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (fields : List ExecutableField) :
    (collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections fields))).length =
      fields.length := by
  induction fields with
  | nil =>
      simp [executableFieldSelections, GraphQL.Execution.collectFields,
        collectedExecutableFields]
  | cons field rest ih =>
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection field) =
            [(field.responseName,
              [executableField parentType field.responseName field.fieldName
                field.arguments field.selectionSet])] := by
        simp [executableFieldSelection, executableField,
          GraphQL.Execution.collectSelection, selectionDirectivesAllowBool_empty]
      simp only [executableFieldSelections, List.map_cons,
        GraphQL.Execution.collectFields]
      rw [hhead]
      rw [collectedExecutableFields_mergeExecutableGroups_length]
      simp [collectedExecutableFields]
      rw [show
          List.map executableFieldSelection rest =
            executableFieldSelections rest by
        rfl]
      rw [ih]
      omega

theorem specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) :
    PairKeysNodup groups ->
    CollectedGroupsFieldsNonempty groups ->
    CollectedGroupsResponseName groups ->
    CollectedGroupsParent parentType groups ->
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (executableFieldSelections (collectedExecutableFields groups)) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        depth source groups := by
  intro hnodup hnonempty hresponse hparent
  simp [GraphQL.Execution.executeRootSelectionSet,
    collectFields_executableFieldSelections_collectedExecutableFields schema
      variableValues parentType source groups hnodup hnonempty hresponse
      hparent]

theorem specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet := by
  simp [GraphQL.Execution.executeRootSelectionSet,
    collectFields_executableFieldSelections_collectedExecutableFields_collectFields
      schema variableValues parentType source selectionSet]

theorem executeRootSelectionSet_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (hflat :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet :=
  hflat.trans
    (specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields_collectFields
      schema resolvers variableValues depth parentType source selectionSet)

theorem collectedExecutableFields_mem_of_group_mem
    {groups : List (Name × List ExecutableField)}
    {responseName : Name} {fields : List ExecutableField}
    {field : ExecutableField} :
    (responseName, fields) ∈ groups ->
      field ∈ fields ->
        field ∈ collectedExecutableFields groups := by
  intro hgroup hfield
  induction groups with
  | nil =>
      simp at hgroup
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, groupFields⟩
      simp [collectedExecutableFields] at hgroup ⊢
      rcases hgroup with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        cases hfields
        exact Or.inl hfield
      · exact Or.inr (ih htail)

theorem CollectedGroupsFieldValidationMergeCompatible.of_collectedExecutableFields
    (groups : List (Name × List ExecutableField)) :
    ExecutableFieldsFieldValidationMergeCompatible
      (collectedExecutableFields groups) ->
        CollectedGroupsFieldValidationMergeCompatible groups := by
  intro hflat responseName fields hgroup first later hfirst hlater hresponse
  exact hflat first later
    (collectedExecutableFields_mem_of_group_mem hgroup hfirst)
    (collectedExecutableFields_mem_of_group_mem hgroup hlater)
    hresponse

theorem CollectedGroupsValidationMergeCompatible.of_collectedExecutableFields
    (groups : List (Name × List ExecutableField)) :
    ExecutableFieldsSameParentValidationMergeCompatible
      (collectedExecutableFields groups) ->
        CollectedGroupsValidationMergeCompatible groups := by
  intro hflat responseName fields hgroup first later hfirst hlater hresponse
    hparent
  exact hflat first later
    (collectedExecutableFields_mem_of_group_mem hgroup hfirst)
    (collectedExecutableFields_mem_of_group_mem hgroup hlater)
    hresponse hparent

theorem ExecutableFieldsFieldValidationMergeCompatible.mono
    (source target : List ExecutableField) :
    (∀ field, field ∈ target -> field ∈ source) ->
      ExecutableFieldsFieldValidationMergeCompatible source ->
        ExecutableFieldsFieldValidationMergeCompatible target := by
  intro hsubset hcompatible first later hfirst hlater hresponse
  exact hcompatible first later (hsubset first hfirst)
    (hsubset later hlater) hresponse

theorem ExecutableFieldsSameParentValidationMergeCompatible.mono
    (source target : List ExecutableField) :
    (∀ field, field ∈ target -> field ∈ source) ->
      ExecutableFieldsSameParentValidationMergeCompatible source ->
        ExecutableFieldsSameParentValidationMergeCompatible target := by
  intro hsubset hcompatible first later hfirst hlater hresponse hparent
  exact hcompatible first later (hsubset first hfirst)
    (hsubset later hlater) hresponse hparent

theorem collectedExecutableFields_mem_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (field : ExecutableField) :
    field ∈
        collectedExecutableFields
          (GraphQL.Execution.addExecutableGroup group groups)
      ↔
    field ∈ group.snd ∨ field ∈ collectedExecutableFields groups := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hname, List.mem_append]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hgroupOrRest
          · exact Or.inr (Or.inl hcurrent)
          · rcases hgroupOrRest with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (Or.inr hrest)
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (Or.inl hgroup)
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (Or.inr hrest)
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hfalse, List.mem_append]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hadded
          · exact Or.inr (Or.inl hcurrent)
          · rcases ih.mp hadded with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (Or.inr hrest)
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (ih.mpr (Or.inl hgroup))
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (ih.mpr (Or.inr hrest))

theorem collectedExecutableFields_mem_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    (field : ExecutableField) :
    field ∈
        collectedExecutableFields
          (GraphQL.Execution.mergeExecutableGroups left right)
      ↔
    field ∈ collectedExecutableFields left
      ∨ field ∈ collectedExecutableFields right := by
  induction right generalizing left with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      change
        field ∈
            collectedExecutableFields
              (GraphQL.Execution.mergeExecutableGroups
                (GraphQL.Execution.addExecutableGroup (responseName, fields)
                  left) rest)
          ↔
        field ∈ collectedExecutableFields left
          ∨ field ∈ collectedExecutableFields ((responseName, fields) :: rest)
      constructor
      · intro hmem
        rcases
            (ih
              (GraphQL.Execution.addExecutableGroup (responseName, fields)
                left)).mp hmem with hadded | hrest
        · rcases
            (collectedExecutableFields_mem_addExecutableGroup
              (responseName, fields) left field).mp hadded with
            hfield | hleft
          · exact Or.inr (by simp [collectedExecutableFields, hfield])
          · exact Or.inl hleft
        · exact Or.inr (by simp [collectedExecutableFields, hrest])
      · intro hmem
        rcases hmem with hleft | hright
        · exact
            (ih
              (GraphQL.Execution.addExecutableGroup (responseName, fields)
                left)).mpr
              (Or.inl
                ((collectedExecutableFields_mem_addExecutableGroup
                  (responseName, fields) left field).mpr (Or.inr hleft)))
        · have hfieldsOrRest :
              field ∈ fields ∨ field ∈ collectedExecutableFields rest := by
            simpa [collectedExecutableFields, List.mem_append] using hright
          rcases hfieldsOrRest with hfield | hrest
          · exact
              (ih
                (GraphQL.Execution.addExecutableGroup (responseName, fields)
                  left)).mpr
                (Or.inl
                  ((collectedExecutableFields_mem_addExecutableGroup
                    (responseName, fields) left field).mpr (Or.inl hfield)))
          · exact
              (ih
                (GraphQL.Execution.addExecutableGroup (responseName, fields)
                  left)).mpr (Or.inr hrest)

theorem collectedExecutableFields_addExecutableGroup_subset_append
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    ∀ field,
      field ∈
          collectedExecutableFields
            (GraphQL.Execution.addExecutableGroup group groups) ->
        field ∈ group.snd ++ collectedExecutableFields groups := by
  intro field hmem
  rcases
      (collectedExecutableFields_mem_addExecutableGroup group groups field).mp
        hmem with hgroup | hgroups
  · exact List.mem_append.mpr (Or.inl hgroup)
  · exact List.mem_append.mpr (Or.inr hgroups)

theorem collectedExecutableFields_mergeExecutableGroups_subset_append
    (left right : List (Name × List ExecutableField)) :
    ∀ field,
      field ∈
          collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups left right) ->
        field ∈ collectedExecutableFields left ++ collectedExecutableFields right := by
  intro field hmem
  rcases
      (collectedExecutableFields_mem_mergeExecutableGroups left right field).mp
        hmem with hleft | hright
  · exact List.mem_append.mpr (Or.inl hleft)
  · exact List.mem_append.mpr (Or.inr hright)

theorem collectedExecutableFields_addExecutableGroup_fieldCompatible_of_append
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    ExecutableFieldsFieldValidationMergeCompatible
      (group.snd ++ collectedExecutableFields groups) ->
        ExecutableFieldsFieldValidationMergeCompatible
          (collectedExecutableFields
            (GraphQL.Execution.addExecutableGroup group groups)) := by
  intro hcompatible
  exact ExecutableFieldsFieldValidationMergeCompatible.mono
    (group.snd ++ collectedExecutableFields groups)
    (collectedExecutableFields
      (GraphQL.Execution.addExecutableGroup group groups))
    (collectedExecutableFields_addExecutableGroup_subset_append group groups)
    hcompatible

theorem collectedExecutableFields_mergeExecutableGroups_fieldCompatible_of_append
    (left right : List (Name × List ExecutableField)) :
    ExecutableFieldsFieldValidationMergeCompatible
      (collectedExecutableFields left ++ collectedExecutableFields right) ->
        ExecutableFieldsFieldValidationMergeCompatible
          (collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups left right)) := by
  intro hcompatible
  exact ExecutableFieldsFieldValidationMergeCompatible.mono
    (collectedExecutableFields left ++ collectedExecutableFields right)
    (collectedExecutableFields
      (GraphQL.Execution.mergeExecutableGroups left right))
    (collectedExecutableFields_mergeExecutableGroups_subset_append left right)
    hcompatible

theorem executableFieldSelections_selectionSetValid_field
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) :
    ∀ fields : List ExecutableField,
      Validation.selectionSetValid schema variableDefinitions parentType
        (executableFieldSelections fields) ->
      ExecutableFieldsParent parentType fields ->
      ∀ field, field ∈ fields ->
        Validation.selectionSetValid schema variableDefinitions
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet
  | [], _hvalid, _hparents, field, hfield => by
      simp at hfield
  | head :: rest, hvalid, hparents, field, hfield => by
      have hvalidCons :
          Validation.selectionSetValid schema variableDefinitions parentType
            (executableFieldSelection head ::
              executableFieldSelections rest) := by
        simpa [executableFieldSelections] using hvalid
      rcases List.mem_cons.mp hfield with hhead | hrest
      · subst field
        rcases Validation.selectionSetValid_field_head_lookup hvalidCons with
          ⟨fieldDefinition, hlookup, _harguments, hselectionSet⟩
        have hparent : head.parentType = parentType :=
          hparents head (by simp)
        have hreturn :
            ((schema.fieldReturnType? head.parentType head.fieldName).getD
              head.fieldName) =
            fieldDefinition.outputType.namedType := by
          subst hparent
          simp [Schema.fieldReturnType?, hlookup]
        simpa [hreturn] using
          Validation.fieldSelectionSetValid_selectionSetValid schema
            variableDefinitions fieldDefinition head.selectionSet hselectionSet
      · have htailValid :
            Validation.selectionSetValid schema variableDefinitions parentType
              (executableFieldSelections rest) :=
          Validation.selectionSetValid_tail hvalidCons
        have htailParents : ExecutableFieldsParent parentType rest := by
          intro candidate hcandidate
          exact hparents candidate (by simp [hcandidate])
        exact
          executableFieldSelections_selectionSetValid_field schema
            variableDefinitions parentType rest htailValid htailParents field
            hrest

theorem executableFieldsScopedBy_selectionSetValid_field
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (fields : List ExecutableField) :
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    ExecutableFieldsScopedBy
      (FieldMerge.collectFields schema parentType selectionSet) fields ->
      ∀ field, field ∈ fields ->
        Validation.selectionSetValid schema variableDefinitions
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet := by
  intro hvalid hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch⟩
  rcases hmatch with
    ⟨hparent, _hresponse, hfieldName, _harguments, hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid schema
        variableDefinitions parentType selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, hlookup, houtput, hfieldSelectionSet⟩
  have hlookupField :
      schema.lookupField field.parentType field.fieldName =
        some fieldDefinition := by
    simpa [hparent, hfieldName] using hlookup
  have hreturn :
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName) =
        fieldDefinition.outputType.namedType := by
    simp [Schema.fieldReturnType?, hlookupField]
  have hselectionSetValid :
      Validation.selectionSetValid schema variableDefinitions
        fieldDefinition.outputType.namedType scopedField.selectionSet :=
    Validation.fieldSelectionSetValid_selectionSetValid schema
      variableDefinitions fieldDefinition scopedField.selectionSet
      hfieldSelectionSet
  simpa [hreturn, hselectionSet] using hselectionSetValid

theorem executableFieldsScopedBy_lookupField
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (fields : List ExecutableField) :
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    ExecutableFieldsScopedBy
      (FieldMerge.collectFields schema parentType selectionSet) fields ->
      ∀ field, field ∈ fields ->
        ∃ fieldDefinition,
          schema.lookupField field.parentType field.fieldName =
            some fieldDefinition := by
  intro hvalid hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch⟩
  rcases hmatch with
    ⟨hparent, _hresponse, hfieldName, _harguments, _hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid schema
        variableDefinitions parentType selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, hlookup, _houtput, _hfieldSelectionSet⟩
  refine ⟨fieldDefinition, ?_⟩
  simpa [hparent, hfieldName] using hlookup

theorem executableFieldsRuntimeScopedBy_scopedSelectionSetValid_field
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (validParent runtimeType : Name) (selectionSet : List Selection)
    (fields : List ExecutableField) :
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    ExecutableFieldsRuntimeScopedBy schema runtimeType
      (FieldMerge.collectFields schema validParent selectionSet) fields ->
      ∀ field, field ∈ fields ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema validParent
            selectionSet
            ∧ ScopedFieldMatchesExecutableIdentity scopedField field
            ∧ ScopedFieldRuntimeApplies schema runtimeType scopedField
            ∧ Validation.selectionSetValid schema variableDefinitions
              scopedField.outputType.namedType field.selectionSet := by
  intro hvalid hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch, hruntime⟩
  rcases hmatch with
    ⟨hresponse, hfieldName, harguments, hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid schema
        variableDefinitions validParent selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, _hlookup, houtput, hfieldSelectionSet⟩
  have hselectionSetValid :
      Validation.selectionSetValid schema variableDefinitions
        scopedField.outputType.namedType scopedField.selectionSet := by
    simpa [← houtput] using
      Validation.fieldSelectionSetValid_selectionSetValid schema
        variableDefinitions fieldDefinition scopedField.selectionSet
        hfieldSelectionSet
  refine
    ⟨scopedField, hscopedMem, ?_, hruntime, ?_⟩
  · exact ⟨hresponse, hfieldName, harguments, hselectionSet⟩
  · simpa [hselectionSet] using hselectionSetValid

theorem selectionSetSemanticsReady_mergedFieldSelectionSet
    (schema : Schema) (parentType : Name) :
    ∀ fields : List ExecutableField,
      (∀ field, field ∈ fields ->
        NormalForm.selectionSetSemanticsReady schema parentType
          field.selectionSet) ->
        NormalForm.selectionSetSemanticsReady schema parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields)
  | [], _hready => by
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetSemanticsReady_nil schema parentType
  | field :: rest, hready => by
      have hfield :
          NormalForm.selectionSetSemanticsReady schema parentType
            field.selectionSet :=
        hready field (by simp)
      have hrest :
          NormalForm.selectionSetSemanticsReady schema parentType
            (GraphQL.Execution.mergedFieldSelectionSet rest) :=
        selectionSetSemanticsReady_mergedFieldSelectionSet schema parentType
          rest
          (by
            intro candidate hcandidate
            exact hready candidate (by simp [hcandidate]))
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetSemanticsReady_append hfield hrest

theorem selectionSetLookupValid_mergedFieldSelectionSet_of_semanticsReady
    (schema : Schema) (parentType : Name)
    (fields : List ExecutableField) :
    (∀ field, field ∈ fields ->
      NormalForm.selectionSetSemanticsReady schema parentType
        field.selectionSet) ->
      NormalForm.selectionSetLookupValid schema parentType
        (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hready
  exact
    NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady
      (GraphQL.Execution.mergedFieldSelectionSet fields)
      (selectionSetSemanticsReady_mergedFieldSelectionSet schema parentType
        fields hready)

theorem selectionSetLookupValid_mergedFieldSelectionSet
    (schema : Schema) (parentType : Name) :
    ∀ fields : List ExecutableField,
      (∀ field, field ∈ fields ->
        NormalForm.selectionSetLookupValid schema parentType
          field.selectionSet) ->
        NormalForm.selectionSetLookupValid schema parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields)
  | [], _hlookup => by
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetLookupValid_nil schema parentType
  | field :: rest, hlookup => by
      have hfield :
          NormalForm.selectionSetLookupValid schema parentType
            field.selectionSet :=
        hlookup field (by simp)
      have hrest :
          NormalForm.selectionSetLookupValid schema parentType
            (GraphQL.Execution.mergedFieldSelectionSet rest) :=
        selectionSetLookupValid_mergedFieldSelectionSet schema parentType rest
          (by
            intro candidate hcandidate
            exact hlookup candidate (by simp [hcandidate]))
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetLookupValid_append hfield hrest

theorem selectionSetImplementationValidInScope_mergedFieldSelectionSet
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) :
    ∀ fields : List ExecutableField,
      (∀ field, field ∈ fields ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType field.selectionSet) ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields)
  | [], _hvalid => by
      simp [GraphQL.Execution.mergedFieldSelectionSet,
        Validation.selectionSetImplementationValidInScope]
  | field :: rest, hvalid => by
      have hfield :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType field.selectionSet :=
        hvalid field (by simp)
      have hrest :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType
            (GraphQL.Execution.mergedFieldSelectionSet rest) :=
        selectionSetImplementationValidInScope_mergedFieldSelectionSet schema
          variableDefinitions parentType rest
          (by
            intro candidate hcandidate
            exact hvalid candidate (by simp [hcandidate]))
      have happend :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType
            (field.selectionSet ++
              GraphQL.Execution.mergedFieldSelectionSet rest) := by
        revert hfield
        induction field.selectionSet with
        | nil =>
            intro _hfield
            simpa using hrest
        | cons selection tail ih =>
            intro hfield
            change
              Validation.selectionImplementationValid schema variableDefinitions
                  parentType selection
                ∧ Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions parentType tail at hfield
            change
              Validation.selectionImplementationValid schema variableDefinitions
                  parentType selection
                ∧ Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions parentType
                  (tail ++ GraphQL.Execution.mergedFieldSelectionSet rest)
            exact ⟨hfield.1, ih hfield.2⟩
      change
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType
          (field.selectionSet ++
            GraphQL.Execution.mergedFieldSelectionSet rest)
      exact happend

mutual
  theorem collectSelection_identityScopedBy_of_selectionValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : Value ObjectIdentity)
      (selection : Selection) :
      Validation.selectionValid schema variableDefinitions validParent
        selection ->
        ExecutableFieldsIdentityScopedBy
          (FieldMerge.collectFields schema validParent [selection])
          (collectedExecutableFields
            (GraphQL.Execution.collectSelection schema variableValues
              collectParent source selection)) := by
    intro hvalid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := validParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_identityScopedBy_of_selectionSetValid schema
                  variableDefinitions variableValues collectParent validParent
                  source selectionSet hselectionSet
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent source
                    typeCondition = true
              · have hrecursive :=
                  collectFields_identityScopedBy_of_selectionSetValid schema
                    variableDefinitions variableValues collectParent typeCondition
                    source selectionSet hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_identityScopedBy_of_selectionSetValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : Value ObjectIdentity)
      (selectionSet : List Selection) :
      Validation.selectionSetValid schema variableDefinitions validParent
        selectionSet ->
        ExecutableFieldsIdentityScopedBy
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              source selectionSet)) := by
    intro hvalid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hleft :=
          collectSelection_identityScopedBy_of_selectionValid schema
            variableDefinitions variableValues collectParent validParent source
            selection hhead
        have hright :=
          collectFields_identityScopedBy_of_selectionSetValid schema
            variableDefinitions variableValues collectParent validParent source
            rest htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent source selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                source rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch⟩
          refine ⟨scopedField, ?_, hmatch⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch⟩
          refine ⟨scopedField, ?_, hmatch⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionValid schema variableDefinitions validParent
        selection ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent [selection])
          (collectedExecutableFields
            (GraphQL.Execution.collectSelection schema variableValues
              collectParent (.object runtimeType (some identity)) selection)) := by
    intro hparentRuntime hvalid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := validParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies] using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetValid schema
                  variableDefinitions variableValues collectParent validParent
                  runtimeType identity selectionSet hparentRuntime hselectionSet
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType (some identity)) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetValid schema
                    variableDefinitions variableValues collectParent typeCondition
                    runtimeType identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType (some identity)) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType (some identity)) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionSetValid schema variableDefinitions validParent
        selectionSet ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType (some identity)) selectionSet)) := by
    intro hparentRuntime hvalid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionValid schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetValid schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity rest hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType (some identity)) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType (some identity)) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selection : Selection) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionValid schema variableDefinitions validParent
        selection ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent [selection])
          (collectedExecutableFields
            (GraphQL.Execution.collectSelection schema variableValues
              collectParent (.object runtimeType identity) selection)) := by
    intro hparentRuntime hvalid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := validParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies] using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetValid_object schema
                  variableDefinitions variableValues collectParent validParent
                  runtimeType identity selectionSet hparentRuntime hselectionSet
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetValid_object schema
                    variableDefinitions variableValues collectParent typeCondition
                    runtimeType identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selectionSet : List Selection) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionSetValid schema variableDefinitions validParent
        selectionSet ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet)) := by
    intro hparentRuntime hvalid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionValid_object schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetValid_object schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity rest hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionLookupValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection) :
      ScopedParentRuntimeApplies schema runtimeType scopedParent ->
      NormalForm.selectionLookupValid schema scopedParent selection ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema scopedParent [selection])
          (collectedExecutableFields
            (GraphQL.Execution.collectSelection schema variableValues
              collectParent (.object runtimeType (some identity)) selection)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldLookup :
            ∃ fieldDefinition,
              schema.lookupField scopedParent fieldName =
                some fieldDefinition := by
          simpa [NormalForm.selectionLookupValid] using hlookupValid
        rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := scopedParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies] using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
                  variableValues collectParent scopedParent runtimeType identity
                  selectionSet hparentRuntime
                  (by simpa [NormalForm.selectionLookupValid] using hlookupValid)
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                NormalForm.selectionSetLookupValid schema typeCondition
                  selectionSet := by
              simpa [NormalForm.selectionLookupValid] using hlookupValid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType (some identity)) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
                    variableValues collectParent typeCondition runtimeType
                    identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType (some identity)) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType (some identity)) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetLookupValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection) :
      ScopedParentRuntimeApplies schema runtimeType scopedParent ->
      NormalForm.selectionSetLookupValid schema scopedParent selectionSet ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema scopedParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType (some identity)) selectionSet)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hlookupValid' :
            ∀ candidate, candidate ∈ selection :: rest ->
              NormalForm.selectionLookupValid schema scopedParent candidate := by
          simpa [NormalForm.selectionSetLookupValid] using hlookupValid
        have hhead :
            NormalForm.selectionLookupValid schema scopedParent selection := by
          exact hlookupValid' selection (by simp)
        have htail :
            NormalForm.selectionSetLookupValid schema scopedParent rest := by
          have htailFunction :
              ∀ candidate, candidate ∈ rest ->
                NormalForm.selectionLookupValid schema scopedParent candidate := by
            intro candidate hcandidate
            exact hlookupValid' candidate
              (List.mem_cons_of_mem selection hcandidate)
          simpa [NormalForm.selectionSetLookupValid] using htailFunction
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionLookupValid schema
            variableValues collectParent scopedParent runtimeType identity
            selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
            variableValues collectParent scopedParent runtimeType identity rest
            hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType (some identity)) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType (some identity)) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionLookupValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selection : Selection) :
      ScopedParentRuntimeApplies schema runtimeType scopedParent ->
      NormalForm.selectionLookupValid schema scopedParent selection ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema scopedParent [selection])
          (collectedExecutableFields
            (GraphQL.Execution.collectSelection schema variableValues
              collectParent (.object runtimeType identity) selection)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldLookup :
            ∃ fieldDefinition,
              schema.lookupField scopedParent fieldName =
                some fieldDefinition := by
          simpa [NormalForm.selectionLookupValid] using hlookupValid
        rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := scopedParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies] using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
                  schema variableValues collectParent scopedParent runtimeType
                  identity selectionSet hparentRuntime
                  (by simpa [NormalForm.selectionLookupValid] using
                    hlookupValid)
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField,
                by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                NormalForm.selectionSetLookupValid schema typeCondition
                  selectionSet := by
              simpa [NormalForm.selectionLookupValid] using hlookupValid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using
                    happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
                    schema variableValues collectParent typeCondition runtimeType
                    identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField,
                    by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selectionSet : List Selection) :
      ScopedParentRuntimeApplies schema runtimeType scopedParent ->
      NormalForm.selectionSetLookupValid schema scopedParent selectionSet ->
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema scopedParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hlookupValid' :
            ∀ candidate, candidate ∈ selection :: rest ->
              NormalForm.selectionLookupValid schema scopedParent candidate := by
          simpa [NormalForm.selectionSetLookupValid] using hlookupValid
        have hhead :
            NormalForm.selectionLookupValid schema scopedParent selection := by
          exact hlookupValid' selection (by simp)
        have htail :
            NormalForm.selectionSetLookupValid schema scopedParent rest := by
          have htailFunction :
              ∀ candidate, candidate ∈ rest ->
                NormalForm.selectionLookupValid schema scopedParent candidate := by
            intro candidate hcandidate
            exact hlookupValid' candidate
              (List.mem_cons_of_mem selection hcandidate)
          simpa [NormalForm.selectionSetLookupValid] using htailFunction
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionLookupValid_object schema
            variableValues collectParent scopedParent runtimeType identity
            selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
            variableValues collectParent scopedParent runtimeType identity rest
            hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

theorem collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType (some identity)) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) := by
  intro hparentRuntime hvalid hgroup hprefix
  have hscopedAll :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType (some identity)) selectionSet)) :=
    collectFields_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent runtimeType
      identity selectionSet hparentRuntime hvalid
  apply
    ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
      (FieldMerge.collectFields schema validParent selectionSet)
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType (some identity)) selectionSet))
      (field :: prefixTail)
  · intro candidate hcandidate
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  · exact hscopedAll

theorem collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) := by
  intro hparentRuntime hvalid hgroup hprefix
  have hscopedAll :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet)) :=
    collectFields_runtimeScopedBy_of_selectionSetValid_object schema
      variableDefinitions variableValues collectParent validParent runtimeType
      identity selectionSet hparentRuntime hvalid
  apply
    ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
      (FieldMerge.collectFields schema validParent selectionSet)
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet))
      (field :: prefixTail)
  · intro candidate hcandidate
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  · exact hscopedAll

theorem collectFields_group_prefix_responseName
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType (some identity)) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ candidate, candidate ∈ field :: prefixTail ->
        candidate.responseName = responseName := by
  intro hgroup hprefix candidate hcandidate
  apply
    collectFields_responseName schema variableValues collectParent
      (.object runtimeType (some identity)) selectionSet responseName
      (field :: fields) hgroup candidate
  rcases List.mem_cons.mp hcandidate with hhead | htail
  · subst candidate
    simp
  · exact List.mem_cons_of_mem field (hprefix candidate htail)

theorem collectFields_group_prefix_childFieldSemanticsReady_of_selectionSetValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType (some identity)) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    (∀ candidate, candidate ∈ field :: prefixTail ->
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent
          selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
      ∀ candidate, candidate ∈ field :: prefixTail ->
        NormalForm.selectionSetSemanticsReady schema childRuntime
          candidate.selectionSet := by
  intro hschema hparentRuntime hvalid hgroup hprefix hcompatible candidate
    hcandidate
  have hscopedPrefix :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) :=
    collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent runtimeType
      identity selectionSet responseName field fields prefixTail
      hparentRuntime hvalid hgroup hprefix
  rcases
      executableFieldsRuntimeScopedBy_scopedSelectionSetValid_field schema
        variableDefinitions validParent runtimeType selectionSet
        (field :: prefixTail) hvalid hscopedPrefix candidate hcandidate with
    ⟨scopedField, hscopedMem, hmatch, hruntime, hselectionSetValid⟩
  exact
    NormalForm.selectionSetSemanticsReady_of_selectionSetValid_possibleObject
      schema variableDefinitions scopedField.outputType.namedType
      childRuntime hschema
      (List.contains_iff_mem.mp
        (hcompatible candidate hcandidate scopedField hscopedMem hmatch
          hruntime))
      candidate.selectionSet hselectionSetValid

theorem collectFields_group_prefix_childFieldSemanticsReady_of_selectionSetValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    (∀ candidate, candidate ∈ field :: prefixTail ->
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent
          selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
      ∀ candidate, candidate ∈ field :: prefixTail ->
        NormalForm.selectionSetSemanticsReady schema childRuntime
          candidate.selectionSet := by
  intro hschema hparentRuntime hvalid hgroup hprefix hcompatible candidate
    hcandidate
  have hscopedPrefix :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) :=
    collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet responseName field fields prefixTail
      hparentRuntime hvalid hgroup hprefix
  rcases
      executableFieldsRuntimeScopedBy_scopedSelectionSetValid_field schema
        variableDefinitions validParent runtimeType selectionSet
        (field :: prefixTail) hvalid hscopedPrefix candidate hcandidate with
    ⟨scopedField, hscopedMem, hmatch, hruntime, hselectionSetValid⟩
  exact
    NormalForm.selectionSetSemanticsReady_of_selectionSetValid_possibleObject
      schema variableDefinitions scopedField.outputType.namedType
      childRuntime hschema
      (List.contains_iff_mem.mp
        (hcompatible candidate hcandidate scopedField hscopedMem hmatch
          hruntime))
      candidate.selectionSet hselectionSetValid

theorem collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    (∀ candidate, candidate ∈ field :: prefixTail ->
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent
          selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
      NormalForm.selectionSetLookupValid schema childRuntime
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hschema hparentRuntime hvalid hgroup hprefix hcompatible
  apply selectionSetLookupValid_mergedFieldSelectionSet_of_semanticsReady
  intro candidate hcandidate
  exact
    collectFields_group_prefix_childFieldSemanticsReady_of_selectionSetValid_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet responseName childRuntime field fields
      prefixTail hschema hparentRuntime hvalid hgroup hprefix hcompatible
      candidate hcandidate

mutual
  theorem collectSelection_childLookupValid_of_selectionImplementationValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selection : Selection)
      (candidate : ExecutableField) (childRuntime : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionImplementationValid schema variableDefinitions
        validParent selection ->
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent (.object runtimeType identity) selection) ->
      (∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent [selection] ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
        NormalForm.selectionSetLookupValid schema childRuntime
          candidate.selectionSet := by
    intro hschema hparentRuntime himplementation hcandidate hcompatible
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · have hcandidateEq :
              candidate =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa [GraphQL.Execution.collectSelection, hallows,
              collectedExecutableFields] using hcandidate
          subst candidate
          have hvalid :
              Validation.selectionValid schema variableDefinitions validParent
                (Selection.field responseName fieldName arguments directives
                  selectionSet) := by
            simpa [Validation.selectionImplementationValid] using
              himplementation.1
          rcases Validation.selectionValid_field_lookup hvalid with
            ⟨fieldDefinition, hlookup, _harguments, hchild⟩
          let scopedField : FieldMerge.ScopedField :=
            { parentType := validParent
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              outputType := fieldDefinition.outputType
              selectionSet := selectionSet }
          have hscopedMem :
              scopedField ∈
                FieldMerge.collectFields schema validParent
                  [Selection.field responseName fieldName arguments directives
                    selectionSet] := by
            simp [scopedField, FieldMerge.collectFields, hlookup]
          have hmatch :
              ScopedFieldMatchesExecutableIdentity scopedField
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simp [scopedField, ScopedFieldMatchesExecutableIdentity]
          have hinclude :
              schema.typeIncludesObjectBool
                  scopedField.outputType.namedType childRuntime =
                true :=
            hcompatible scopedField hscopedMem hmatch
              (by simpa [scopedField, ScopedFieldRuntimeApplies] using
                hparentRuntime)
          have hchildValid :
              Validation.selectionSetValid schema variableDefinitions
                fieldDefinition.outputType.namedType selectionSet :=
            NormalForm.fieldSelectionSetValid_child_of_possibleType hchild
              (List.contains_iff_mem.mp hinclude)
          exact
            NormalForm.selectionSetLookupValid_of_selectionSetValid_possibleObject
              schema variableDefinitions fieldDefinition.outputType.namedType
              childRuntime hschema (List.contains_iff_mem.mp hinclude)
              selectionSet hchildValid
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            collectedExecutableFields] at hcandidate
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hbody :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions validParent selectionSet := by
              simpa [Validation.selectionImplementationValid] using
                himplementation
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows] at hcandidate
              exact
                collectFields_childLookupValid_of_selectionSetImplementationValidInScope_object
                  schema variableDefinitions variableValues collectParent
                  validParent runtimeType identity selectionSet candidate
                  childRuntime hschema hparentRuntime hbody hcandidate
                  (by
                    intro scopedField hscoped hmatch hruntime
                    exact hcompatible scopedField
                      (by
                        simpa [FieldMerge.collectFields] using hscoped)
                      hmatch hruntime)
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have hcondition :
                    schema.typeIncludesObjectBool typeCondition runtimeType =
                      true := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using
                    happly
                have hoverlap :
                    schema.typesOverlapBool validParent typeCondition =
                      true := by
                  unfold Schema.typesOverlapBool
                  exact List.any_eq_true.mpr
                    ⟨runtimeType, List.contains_iff_mem.mp hparentRuntime,
                      hcondition⟩
                have hbody :
                    Validation.selectionSetImplementationValidInScope schema
                      variableDefinitions typeCondition selectionSet :=
                  (himplementation hoverlap).1
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hcandidate
                exact
                  collectFields_childLookupValid_of_selectionSetImplementationValidInScope_object
                    schema variableDefinitions variableValues collectParent
                    typeCondition runtimeType identity selectionSet candidate
                    childRuntime hschema
                    (ScopedParentRuntimeApplies.of_typeIncludesObjectBool
                      schema runtimeType typeCondition hcondition)
                    hbody hcandidate
                    (by
                      intro scopedField hscoped hmatch hruntime
                      exact hcompatible scopedField
                        (by
                          simpa [FieldMerge.collectFields] using hscoped)
                        hmatch hruntime)
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  collectedExecutableFields] at hcandidate
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate

  theorem collectFields_childLookupValid_of_selectionSetImplementationValidInScope_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selectionSet : List Selection)
      (candidate : ExecutableField) (childRuntime : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions validParent selectionSet ->
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) ->
      (∀ scopedField,
        scopedField ∈
          FieldMerge.collectFields schema validParent selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
        NormalForm.selectionSetLookupValid schema childRuntime
          candidate.selectionSet := by
    intro hschema hparentRuntime himplementation hcandidate hcompatible
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hcandidate
    | cons selection rest =>
        have hhead :
            Validation.selectionImplementationValid schema variableDefinitions
              validParent selection := by
          simpa [Validation.selectionSetImplementationValidInScope] using
            himplementation.1
        have htail :
            Validation.selectionSetImplementationValidInScope schema
              variableDefinitions validParent rest := by
          simpa [Validation.selectionSetImplementationValidInScope] using
            himplementation.2
        simp [GraphQL.Execution.collectFields] at hcandidate
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              candidate).mp hcandidate with hselection | hrest
        · exact
            collectSelection_childLookupValid_of_selectionImplementationValid_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity selection candidate childRuntime hschema
              hparentRuntime hhead hselection
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inl hscoped))
                  hmatch hruntime)
        · exact
            collectFields_childLookupValid_of_selectionSetImplementationValidInScope_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity rest candidate childRuntime hschema
              hparentRuntime htail hrest
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inr hscoped))
                  hmatch hruntime)
end

theorem collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetImplementationValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      validParent selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    (∀ candidate, candidate ∈ field :: prefixTail ->
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent
          selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
      NormalForm.selectionSetLookupValid schema childRuntime
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hschema hparentRuntime himplementation hgroup hprefix hcompatible
  apply selectionSetLookupValid_mergedFieldSelectionSet
  intro candidate hcandidate
  have hcollected :
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  exact
    collectFields_childLookupValid_of_selectionSetImplementationValidInScope_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet candidate childRuntime hschema
      hparentRuntime himplementation hcollected
      (hcompatible candidate hcandidate)

mutual
  theorem collectSelection_childImplementation_of_selectionImplementationValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selection : Selection)
      (candidate : ExecutableField) (childRuntime : Name) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionImplementationValid schema variableDefinitions
        validParent selection ->
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent (.object runtimeType identity) selection) ->
      (∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent [selection] ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime candidate.selectionSet := by
    intro hparentRuntime himplementation hcandidate hcompatible
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · have hcandidateEq :
              candidate =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa [GraphQL.Execution.collectSelection, hallows,
              collectedExecutableFields] using hcandidate
          subst candidate
          cases hlookup : schema.lookupField validParent fieldName with
          | none =>
              simp [Validation.selectionImplementationValid, hlookup] at himplementation
          | some fieldDefinition =>
              let scopedField : FieldMerge.ScopedField :=
                { parentType := validParent
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  outputType := fieldDefinition.outputType
                  selectionSet := selectionSet }
              have hscopedMem :
                  scopedField ∈
                    FieldMerge.collectFields schema validParent
                      [Selection.field responseName fieldName arguments
                        directives selectionSet] := by
                simp [scopedField, FieldMerge.collectFields, hlookup]
              have hmatch :
                  ScopedFieldMatchesExecutableIdentity scopedField
                    {
                      parentType := collectParent,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet := selectionSet
                    } := by
                simp [scopedField, ScopedFieldMatchesExecutableIdentity]
              have hinclude :
                  schema.typeIncludesObjectBool
                      scopedField.outputType.namedType childRuntime =
                    true :=
                hcompatible scopedField hscopedMem hmatch
                  (by simpa [scopedField, ScopedFieldRuntimeApplies] using
                    hparentRuntime)
              exact
                NormalForm.GroundTypeNormalization.selectionImplementationValid_field_child
                  himplementation hlookup
                  (Or.inr (List.contains_iff_mem.mp hinclude))
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            collectedExecutableFields] at hcandidate
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hbody :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions validParent selectionSet := by
              simpa [Validation.selectionImplementationValid] using
                himplementation
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows] at hcandidate
              exact
                collectFields_childImplementation_of_selectionSetImplementationValidInScope_object
                  schema variableDefinitions variableValues collectParent
                  validParent runtimeType identity selectionSet candidate
                  childRuntime hparentRuntime hbody hcandidate
                  (by
                    intro scopedField hscoped hmatch hruntime
                    exact hcompatible scopedField
                      (by
                        simpa [FieldMerge.collectFields] using hscoped)
                      hmatch hruntime)
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have hcondition :
                    schema.typeIncludesObjectBool typeCondition runtimeType =
                      true := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using
                    happly
                have hoverlap :
                    schema.typesOverlapBool validParent typeCondition =
                      true := by
                  unfold Schema.typesOverlapBool
                  exact List.any_eq_true.mpr
                    ⟨runtimeType, List.contains_iff_mem.mp hparentRuntime,
                      hcondition⟩
                have hbody :
                    Validation.selectionSetImplementationValidInScope schema
                      variableDefinitions typeCondition selectionSet :=
                  (himplementation hoverlap).1
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hcandidate
                exact
                  collectFields_childImplementation_of_selectionSetImplementationValidInScope_object
                    schema variableDefinitions variableValues collectParent
                    typeCondition runtimeType identity selectionSet candidate
                    childRuntime
                    (ScopedParentRuntimeApplies.of_typeIncludesObjectBool
                      schema runtimeType typeCondition hcondition)
                    hbody hcandidate
                    (by
                      intro scopedField hscoped hmatch hruntime
                      exact hcompatible scopedField
                        (by
                          simpa [FieldMerge.collectFields] using hscoped)
                        hmatch hruntime)
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  collectedExecutableFields] at hcandidate
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate

  theorem collectFields_childImplementation_of_selectionSetImplementationValidInScope_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selectionSet : List Selection)
      (candidate : ExecutableField) (childRuntime : Name) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions validParent selectionSet ->
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) ->
      (∀ scopedField,
        scopedField ∈
          FieldMerge.collectFields schema validParent selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime candidate.selectionSet := by
    intro hparentRuntime himplementation hcandidate hcompatible
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hcandidate
    | cons selection rest =>
        have hhead :
            Validation.selectionImplementationValid schema variableDefinitions
              validParent selection := by
          simpa [Validation.selectionSetImplementationValidInScope] using
            himplementation.1
        have htail :
            Validation.selectionSetImplementationValidInScope schema
              variableDefinitions validParent rest := by
          simpa [Validation.selectionSetImplementationValidInScope] using
            himplementation.2
        simp [GraphQL.Execution.collectFields] at hcandidate
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) rest)
              candidate).mp hcandidate with hselection | hrest
        · exact
            collectSelection_childImplementation_of_selectionImplementationValid_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity selection candidate childRuntime
              hparentRuntime hhead hselection
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inl hscoped))
                  hmatch hruntime)
        · exact
            collectFields_childImplementation_of_selectionSetImplementationValidInScope_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity rest candidate childRuntime hparentRuntime
              htail hrest
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inr hscoped))
                  hmatch hruntime)
end

theorem collectFields_group_prefix_mergedFieldSelectionSet_implementationValid
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (childRuntime : Name) (field : ExecutableField)
    (prefixTail : List ExecutableField) :
    (∀ candidate, candidate ∈ field :: prefixTail ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions childRuntime candidate.selectionSet) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions childRuntime
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hfields
  exact
    selectionSetImplementationValidInScope_mergedFieldSelectionSet schema
      variableDefinitions childRuntime (field :: prefixTail) hfields

theorem collectFields_group_prefix_mergedFieldSelectionSet_implementationValid_of_selectionSetImplementationValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      validParent selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    (∀ candidate, candidate ∈ field :: prefixTail ->
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent
          selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions childRuntime
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hparentRuntime himplementation hgroup hprefix hcompatible
  apply collectFields_group_prefix_mergedFieldSelectionSet_implementationValid
  intro candidate hcandidate
  have hcollected :
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  exact
    collectFields_childImplementation_of_selectionSetImplementationValidInScope_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet candidate childRuntime hparentRuntime
      himplementation hcollected (hcompatible candidate hcandidate)

theorem collectFields_group_fieldParentRuntime
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) :
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType (some identity)) selectionSet ->
    schema.typeIncludesObjectBool collectParent runtimeType = true ->
      schema.typeIncludesObjectBool field.parentType runtimeType = true := by
  intro hgroup hparentRuntime
  have hparents :
      CollectedGroupsParent collectParent
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType (some identity)) selectionSet) :=
    collectFields_parent schema variableValues collectParent
      (.object runtimeType (some identity)) selectionSet
  have hfieldParent : field.parentType = collectParent :=
    hparents responseName (field :: fields) hgroup field (by simp)
  simpa [hfieldParent] using hparentRuntime

theorem fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (responseName : Name)
    (fields : List ExecutableField) :
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    (∀ field, field ∈ fields -> field.responseName = responseName) ->
    ExecutableFieldsRuntimeScopedBy schema runtimeType
      (FieldMerge.collectFields schema parentType selectionSet) fields ->
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hmerge hresponses hscoped objectType
  apply FieldMerge.fieldsInSetCanMerge_mergedFieldSelectionSet_of_pairwise
  intro first hfirst later hlater
  rcases hscoped first hfirst with
    ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
  rcases hscoped later hlater with
    ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨hfirstResponse, _hfirstField, _hfirstArguments, hfirstSelectionSet⟩
  rcases hlaterMatch with
    ⟨hlaterResponse, _hlaterField, _hlaterArguments, hlaterSelectionSet⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse, hresponses first hfirst,
      hresponses later hlater]
  have hparents :
      firstScoped.parentType = laterScoped.parentType
        ∨ ¬schema.objectType firstScoped.parentType
        ∨ ¬schema.objectType laterScoped.parentType :=
    ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
      firstScoped laterScoped hfirstRuntime hlaterRuntime
  simpa [hfirstSelectionSet, hlaterSelectionSet] using
    FieldMerge.fieldsInSetCanMerge_pair_subfields schema parentType
      selectionSet firstScoped laterScoped hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse hparents objectType

theorem collectFields_group_prefix_mergedFieldSelectionSet_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType (some identity)) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail)) := by
  intro hvalid hmerge hparentRuntime hgroup hprefix objectType
  apply
    fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
      schema validParent runtimeType selectionSet responseName
      (field :: prefixTail) hmerge
  · exact collectFields_group_prefix_responseName schema variableValues
      collectParent runtimeType identity selectionSet responseName field
      fields prefixTail hgroup hprefix
  · intro candidate hcandidate
    have hscopedPrefix :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) :=
      collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid schema
        variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet responseName field fields prefixTail
        hparentRuntime hvalid hgroup hprefix
    exact hscopedPrefix candidate hcandidate

theorem collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType (some identity)) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail)) := by
  intro hlookupValid hmerge hparentRuntime hgroup hprefix objectType
  apply
    fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
      schema validParent runtimeType selectionSet responseName
      (field :: prefixTail) hmerge
  · exact collectFields_group_prefix_responseName schema variableValues
      collectParent runtimeType identity selectionSet responseName field
      fields prefixTail hgroup hprefix
  · intro candidate hcandidate
    have hscopedPrefix :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) := by
      have hscopedAll :
          ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType (some identity)) selectionSet)) :=
        collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
          variableValues collectParent validParent runtimeType identity
          selectionSet hparentRuntime hlookupValid
      apply
        ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType (some identity)) selectionSet))
          (field :: prefixTail)
      · intro executable hexecutable
        apply collectedExecutableFields_mem_of_group_mem hgroup
        rcases List.mem_cons.mp hexecutable with hhead | htail
        · subst executable
          simp
        · exact List.mem_cons_of_mem field (hprefix executable htail)
      · exact hscopedAll
    exact hscopedPrefix candidate hcandidate

theorem collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (GraphQL.Execution.mergedFieldSelectionSet
            (field :: prefixTail)) := by
  intro hlookupValid hmerge hparentRuntime hgroup hprefix objectType
  apply
    fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
      schema validParent runtimeType selectionSet responseName
      (field :: prefixTail) hmerge
  · intro candidate hcandidate
    apply
      collectFields_responseName schema variableValues collectParent
        (.object runtimeType identity) selectionSet responseName
        (field :: fields) hgroup candidate
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  · intro candidate hcandidate
    have hscopedPrefix :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) := by
      have hscopedAll :
          ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) selectionSet)) :=
        collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
          variableValues collectParent validParent runtimeType identity
          selectionSet hparentRuntime hlookupValid
      apply
        ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet))
          (field :: prefixTail)
      · intro executable hexecutable
        apply collectedExecutableFields_mem_of_group_mem hgroup
        rcases List.mem_cons.mp hexecutable with hhead | htail
        · subst executable
          simp
        · exact List.mem_cons_of_mem field (hprefix executable htail)
      · exact hscopedAll
    exact hscopedPrefix candidate hcandidate

theorem collectFields_group_prefix_outputCompatible_of_concreteParent
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    collectParent = validParent ->
    schema.objectType validParent ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    ∀ childRuntime,
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        childRuntime = true ->
      ∀ candidate, candidate ∈ field :: prefixTail ->
        ∀ scopedField,
          scopedField ∈ FieldMerge.collectFields schema validParent
            selectionSet ->
          ScopedFieldMatchesExecutableIdentity scopedField candidate ->
          ScopedFieldRuntimeApplies schema runtimeType scopedField ->
            schema.typeIncludesObjectBool scopedField.outputType.namedType
              childRuntime = true := by
  intro hschema hparentEq hvalidObject hparentRuntime hlookup hmerge hgroup
    hprefix childRuntime hinclude candidate hcandidate scopedField hscoped
    hmatch hruntime
  subst collectParent
  have hruntimeEq : runtimeType = validParent :=
    object_typeIncludesObjectBool_eq_self schema hvalidObject hparentRuntime
  have hfieldParent : field.parentType = validParent := by
    have hparents :
        CollectedGroupsParent validParent
          (GraphQL.Execution.collectFields schema variableValues validParent
            (.object runtimeType identity) selectionSet) :=
      collectFields_parent schema variableValues validParent
        (.object runtimeType identity) selectionSet
    exact hparents responseName (field :: fields) hgroup field (by simp)
  have hscopedAll :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues validParent
            (.object runtimeType identity) selectionSet)) :=
    collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
      variableValues validParent validParent runtimeType identity selectionSet
      hparentRuntime hlookup
  have hscopedPrefix :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) := by
    apply
      ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues validParent
            (.object runtimeType identity) selectionSet))
        (field :: prefixTail)
    · intro executable hexecutable
      apply collectedExecutableFields_mem_of_group_mem hgroup
      rcases List.mem_cons.mp hexecutable with hhead | htail
      · subst executable
        simp
      · exact List.mem_cons_of_mem field (hprefix executable htail)
    · exact hscopedAll
  rcases hscopedPrefix field (by simp) with
    ⟨headScoped, hheadScopedMem, hheadMatch, hheadRuntime⟩
  rcases hheadMatch with
    ⟨_hheadResponse, hheadField, _hheadArguments, _hheadSelection⟩
  rcases
      GraphQL.NormalForm.fieldMerge_collectFields_mem_lookupField_outputType
        schema validParent selectionSet headScoped hheadScopedMem with
    ⟨headExpectedDefinition, hheadExpectedLookup, _hheadOutput⟩
  have hheadPossible :
      validParent ∈ schema.getPossibleTypes headScoped.parentType := by
    have hheadRuntime' :
        schema.typeIncludesObjectBool headScoped.parentType validParent =
          true := by
      simpa [hruntimeEq] using hheadRuntime
    exact List.contains_iff_mem.mp hheadRuntime'
  rcases
      SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
        hschema hheadPossible hheadExpectedLookup with
    ⟨headImplementationDefinition, hheadImplementationLookup⟩
  have hheadImplementationLookupField :
      schema.lookupField validParent field.fieldName =
        some headImplementationDefinition := by
    simpa [hheadField] using hheadImplementationLookup
  have hheadInclude :
      schema.typeIncludesObjectBool
        headImplementationDefinition.outputType.namedType childRuntime =
        true := by
    have hlookupAtFieldParent :
        schema.lookupField field.parentType field.fieldName =
          some headImplementationDefinition := by
      simpa [hfieldParent] using hheadImplementationLookupField
    simpa [Schema.fieldReturnType?, hlookupAtFieldParent] using hinclude
  have hresponseNames :
      ∀ candidate, candidate ∈ field :: prefixTail ->
        candidate.responseName = responseName := by
    intro executable hexecutable
    apply
      collectFields_responseName schema variableValues validParent
        (.object runtimeType identity) selectionSet responseName
        (field :: fields) hgroup executable
    rcases List.mem_cons.mp hexecutable with hhead | htail
    · subst executable
      simp
    · exact List.mem_cons_of_mem field (hprefix executable htail)
  have hexecutableCompatible :
      ExecutableFieldsFieldValidationMergeCompatible (field :: prefixTail) := by
    intro first later hfirst hlater hresponse
    rcases hscopedPrefix first hfirst with
      ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
    rcases hscopedPrefix later hlater with
      ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
    rcases hfirstMatch with
      ⟨hfirstResponse, hfirstField, hfirstArguments, _hfirstSelection⟩
    rcases hlaterMatch with
      ⟨hlaterResponse, hlaterField, hlaterArguments, _hlaterSelection⟩
    have hscopedResponse :
        firstScoped.responseName = laterScoped.responseName := by
      rw [hfirstResponse, hlaterResponse]
      exact hresponse
    have hfieldMerge :
        FieldMerge.fieldsForNameCanMerge schema firstScoped laterScoped :=
      FieldMerge.fieldsInSetCanMerge_pair hmerge hfirstScopedMem
        hlaterScopedMem hscopedResponse
    rcases
        FieldMerge.fieldsForNameCanMerge_identity hfieldMerge
          (ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
            firstScoped laterScoped hfirstRuntime hlaterRuntime) with
      ⟨hfield, hargumentsEquivalent⟩
    constructor
    · rw [← hfirstField, ← hlaterField]
      exact hfield
    · rw [← hfirstArguments, ← hlaterArguments]
      exact hargumentsEquivalent
  have hfieldEq : field.fieldName = candidate.fieldName := by
    exact
      (hexecutableCompatible field candidate (by simp) hcandidate
        (by
          rw [hresponseNames field (by simp),
            hresponseNames candidate hcandidate])).1
  rcases hmatch with
    ⟨_hscopedResponse, hscopedFieldName, _hscopedArguments,
      _hscopedSelection⟩
  have hscopedFieldEq : scopedField.fieldName = field.fieldName :=
    hscopedFieldName.trans hfieldEq.symm
  rcases
      GraphQL.NormalForm.fieldMerge_collectFields_mem_lookupField_outputType
        schema validParent selectionSet scopedField hscoped with
    ⟨scopedDefinition, hscopedLookup, hscopedOutput⟩
  have hscopedPossible :
      validParent ∈ schema.getPossibleTypes scopedField.parentType := by
    have hruntime' :
        schema.typeIncludesObjectBool scopedField.parentType validParent =
          true := by
      simpa [hruntimeEq] using hruntime
    exact List.contains_iff_mem.mp hruntime'
  have himplementationLookupForScoped :
      schema.lookupField validParent scopedField.fieldName =
        some headImplementationDefinition := by
    simpa [hscopedFieldEq] using hheadImplementationLookupField
  have hsubtype :
      schema.outputTypeSubtype headImplementationDefinition.outputType
        scopedDefinition.outputType :=
    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
      hschema hscopedPossible hscopedLookup himplementationLookupForScoped
  have hscopedDefinitionInclude :
      schema.typeIncludesObjectBool scopedDefinition.outputType.namedType
        childRuntime = true :=
    typeIncludesObjectBool_of_outputTypeSubtype_namedType schema hsubtype
      hheadInclude
  simpa [hscopedOutput] using hscopedDefinitionInclude

theorem collectFields_group_prefix_mergedFieldSelectionSet_childLocalFacts_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      validParent selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues collectParent
        (.object runtimeType identity) selectionSet ->
    (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
    (∀ candidate, candidate ∈ field :: prefixTail ->
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema validParent
          selectionSet ->
        ScopedFieldMatchesExecutableIdentity scopedField candidate ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField ->
          schema.typeIncludesObjectBool scopedField.outputType.namedType
            childRuntime = true) ->
      NormalForm.selectionSetLookupValid schema childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        ∧
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        ∧
        (∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) := by
  intro hschema hparentRuntime hvalid hlookupValid himplementation hmerge
    hgroup hprefix hcompatible
  constructor
  · exact
      collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetValid_object
        schema variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet responseName childRuntime field fields
        prefixTail hschema hparentRuntime hvalid hgroup hprefix hcompatible
  constructor
  · exact
      collectFields_group_prefix_mergedFieldSelectionSet_implementationValid_of_selectionSetImplementationValid_object
        schema variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet responseName childRuntime field fields
        prefixTail hparentRuntime himplementation hgroup hprefix hcompatible
  · exact
      collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid_object
        schema variableValues collectParent validParent runtimeType identity
        selectionSet responseName field fields prefixTail hlookupValid hmerge
        hparentRuntime hgroup hprefix

def CollectedGroupsArgumentsNodup
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsArgumentsNodup fields

theorem ExecutableFieldsArgumentsNodup_singleton
    (field : ExecutableField) :
    (field.arguments.map Argument.name).Nodup ->
      ExecutableFieldsArgumentsNodup [field] := by
  intro hnodup candidate hmem
  have hcandidate : candidate = field := by
    simpa using hmem
  subst candidate
  exact hnodup

theorem ExecutableFieldsArgumentsNodup_append
    (left right : List ExecutableField) :
    ExecutableFieldsArgumentsNodup left ->
      ExecutableFieldsArgumentsNodup right ->
        ExecutableFieldsArgumentsNodup (left ++ right) := by
  intro hleft hright field hmem
  rcases List.mem_append.mp hmem with hfield | hfield
  · exact hleft field hfield
  · exact hright field hfield

theorem CollectedGroupsArgumentsNodup_nil :
    CollectedGroupsArgumentsNodup [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsArgumentsNodup_singleton
    (responseName : Name) (fields : List ExecutableField) :
    ExecutableFieldsArgumentsNodup fields ->
      CollectedGroupsArgumentsNodup [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hpair :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hpair
  exact hfields

theorem CollectedGroupsArgumentsNodup_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)} :
    CollectedGroupsArgumentsNodup (group :: groups) ->
      CollectedGroupsArgumentsNodup groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsArgumentsNodup_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    ExecutableFieldsArgumentsNodup group.snd ->
      CollectedGroupsArgumentsNodup groups ->
        CollectedGroupsArgumentsNodup
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields hmem
      simp [GraphQL.Execution.addExecutableGroup] at hmem
      rcases hmem with ⟨_hresponseName, hfields⟩
      cases hfields
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact ExecutableFieldsArgumentsNodup_append currentFields
            groupFields
            (hgroups currentName currentFields (by simp))
            hgroup
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsArgumentsNodup_tail hgroups)
            responseName fields htail

theorem CollectedGroupsArgumentsNodup_mergeExecutableGroups
    (left right : List (Name × List ExecutableField)) :
    CollectedGroupsArgumentsNodup left ->
      CollectedGroupsArgumentsNodup right ->
        CollectedGroupsArgumentsNodup
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [GraphQL.Execution.mergeExecutableGroups]
      exact ih (GraphQL.Execution.addExecutableGroup (responseName, fields) left)
        (CollectedGroupsArgumentsNodup_addExecutableGroup
          (responseName, fields) left (hright responseName fields (by simp))
          hleft)
        (CollectedGroupsArgumentsNodup_tail hright)

theorem argumentsValid_argumentsNodup
    {schema : Schema} {definitions : List InputValueDefinition}
    {variableDefinitions : List VariableDefinition}
    {arguments : List Argument} :
    Validation.argumentsValid schema definitions variableDefinitions
      arguments ->
        (arguments.map Argument.name).Nodup := by
  intro hvalid
  exact hvalid.1

theorem ValidOperationPrefixSelectionState.field_argumentsNodup
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection} :
    ValidOperationPrefixSelectionState schema operation prefixSelections
      (.field responseName fieldName arguments directives selectionSet)
      suffix ->
      (arguments.map Argument.name).Nodup := by
  intro hstate
  rcases ValidOperationPrefixSelectionState.field_lookup hstate with
    ⟨_fieldDefinition, _hlookup, harguments, _hselectionSet⟩
  exact argumentsValid_argumentsNodup harguments

mutual
  theorem collectSelection_argumentsNodup_of_selectionValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : Value ObjectIdentity)
      (selection : Selection) :
      Validation.selectionValid schema variableDefinitions validParent
        selection ->
        CollectedGroupsArgumentsNodup
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent source selection) := by
    intro hvalid
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨_fieldDefinition, _hlookup, harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsArgumentsNodup_singleton responseName
            [{
              parentType := collectParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsArgumentsNodup_singleton
              {
                parentType := collectParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              (argumentsValid_argumentsNodup harguments))
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsArgumentsNodup_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_argumentsNodup_of_selectionSetValid schema
                variableDefinitions variableValues collectParent validParent
                source selectionSet hselectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_argumentsNodup_of_selectionSetValid schema
                  variableDefinitions variableValues collectParent typeCondition
                  source selectionSet hselectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsArgumentsNodup_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]

  theorem collectFields_argumentsNodup_of_selectionSetValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : Value ObjectIdentity)
      (selectionSet : List Selection) :
      Validation.selectionSetValid schema variableDefinitions validParent
        selectionSet ->
        CollectedGroupsArgumentsNodup
          (GraphQL.Execution.collectFields schema variableValues collectParent
            source selectionSet) := by
    intro hvalid
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsArgumentsNodup_nil]
    | cons selection rest =>
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsArgumentsNodup_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent source selection)
          (GraphQL.Execution.collectFields schema variableValues collectParent
            source rest)
          (collectSelection_argumentsNodup_of_selectionValid schema
            variableDefinitions variableValues collectParent validParent source
            selection hhead)
          (collectFields_argumentsNodup_of_selectionSetValid schema
            variableDefinitions variableValues collectParent validParent source
            rest htail)
end

mutual
  theorem collectSelection_argumentsNodup_of_selectionImplementationValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selection : Selection) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionImplementationValid schema variableDefinitions
        validParent selection ->
        CollectedGroupsArgumentsNodup
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent (.object runtimeType identity) selection) := by
    intro hparentRuntime hvalid
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hselectionValid :
            Validation.selectionValid schema variableDefinitions validParent
              (Selection.field responseName fieldName arguments directives
                selectionSet) := by
          simpa [Validation.selectionImplementationValid] using hvalid.1
        rcases Validation.selectionValid_field_lookup hselectionValid with
          ⟨_fieldDefinition, _hlookup, harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsArgumentsNodup_singleton responseName
            [{
              parentType := collectParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsArgumentsNodup_singleton
              {
                parentType := collectParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              (argumentsValid_argumentsNodup harguments))
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsArgumentsNodup_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hbody :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions validParent selectionSet := by
              simpa [Validation.selectionImplementationValid] using hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact
                collectFields_argumentsNodup_of_selectionSetImplementationValidInScope_object
                  schema variableDefinitions variableValues collectParent
                  validParent runtimeType identity selectionSet hparentRuntime
                  hbody
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have hcondition :
                    schema.typeIncludesObjectBool typeCondition runtimeType =
                      true := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using
                    happly
                have hoverlap :
                    schema.typesOverlapBool validParent typeCondition =
                      true := by
                  unfold Schema.typesOverlapBool
                  exact List.any_eq_true.mpr
                    ⟨runtimeType, List.contains_iff_mem.mp hparentRuntime,
                      hcondition⟩
                have hbody :
                    Validation.selectionSetImplementationValidInScope schema
                      variableDefinitions typeCondition selectionSet := by
                  exact (hvalid hoverlap).1
                simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact
                  collectFields_argumentsNodup_of_selectionSetImplementationValidInScope_object
                    schema variableDefinitions variableValues collectParent
                    typeCondition runtimeType identity selectionSet
                    (ScopedParentRuntimeApplies.of_typeIncludesObjectBool
                      schema runtimeType typeCondition hcondition)
                    hbody
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsArgumentsNodup_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]

  theorem collectFields_argumentsNodup_of_selectionSetImplementationValidInScope_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : Option ObjectIdentity)
      (selectionSet : List Selection) :
      ScopedParentRuntimeApplies schema runtimeType validParent ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions validParent selectionSet ->
        CollectedGroupsArgumentsNodup
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
    intro hparentRuntime himplementation
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsArgumentsNodup_nil]
    | cons selection rest =>
        have hhead :
            Validation.selectionImplementationValid schema variableDefinitions
              validParent selection := by
          simpa [Validation.selectionSetImplementationValidInScope] using
            himplementation.1
        have htail :
            Validation.selectionSetImplementationValidInScope schema
              variableDefinitions validParent rest := by
          simpa [Validation.selectionSetImplementationValidInScope] using
            himplementation.2
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsArgumentsNodup_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent (.object runtimeType identity) selection)
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) rest)
          (collectSelection_argumentsNodup_of_selectionImplementationValid_object
            schema variableDefinitions variableValues collectParent validParent
            runtimeType identity selection hparentRuntime hhead)
          (collectFields_argumentsNodup_of_selectionSetImplementationValidInScope_object
            schema variableDefinitions variableValues collectParent validParent
            runtimeType identity rest hparentRuntime htail)
end

def CollectedGroupsResolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups ->
      ExecutableFieldsResolveStable resolvers source fields

theorem CollectedGroupsResolveStable.group
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField) :
    CollectedGroupsResolveStable resolvers source groups ->
    (responseName, fields) ∈ groups ->
      ExecutableFieldsResolveStable resolvers source fields := by
  intro hstable hmem
  exact hstable responseName fields hmem

theorem CollectedGroupsResolveStable.tail
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity)
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) :
    CollectedGroupsResolveStable resolvers source (group :: groups) ->
      CollectedGroupsResolveStable resolvers source groups := by
  intro hstable responseName fields hmem
  exact hstable responseName fields (by simp [hmem])

structure ExecutionStateInvariant
    (state : ExecutionEquivalenceState ObjectIdentity) : Prop where
  groupedResponseKeysUnique :
    PairKeysNodup
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  groupedFieldsCompatible :
    ∀ responseName fields,
      (responseName, fields) ∈
        GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet ->
        ExecutableFieldsMergeCompatible fields
  groupedFieldsResolveStable :
    ∀ responseName fields,
      (responseName, fields) ∈
        GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet ->
        ExecutableFieldsResolveStable state.window.resolvers state.window.source
          fields

structure ExecutionSemanticStateInvariant
    (state : ExecutionEquivalenceState ObjectIdentity) : Prop where
  groupedResponseKeysUnique :
    PairKeysNodup
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  groupedFieldsSameParent :
    CollectedGroupsSameResponseParent
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  groupedFieldsValidationCompatible :
    CollectedGroupsValidationMergeCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  resolversRespectArgumentEquivalence :
    ResolversRespectArgumentEquivalence state.window.resolvers
      state.window.source

structure ExecutionFieldSemanticStateInvariant
    (state : ExecutionEquivalenceState ObjectIdentity) : Prop where
  groupedResponseKeysUnique :
    PairKeysNodup
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  groupedFieldsFieldCompatible :
    CollectedGroupsFieldValidationMergeCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  resolversRespectFieldAndArgumentEquivalence :
    ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
      state.window.source

structure ExecutionValidFieldSemanticStateInvariant
    (state : ExecutionEquivalenceState ObjectIdentity) : Prop where
  groupedResponseKeysUnique :
    PairKeysNodup
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  groupedFieldsFieldCompatible :
    CollectedGroupsFieldValidationMergeCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  groupedFieldsArgumentsNodup :
    CollectedGroupsArgumentsNodup
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  resolversRespectValidFieldAndArgumentEquivalence :
    ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
      state.window.source

structure ExecutionCollectedFieldInvariant
    (state : ExecutionEquivalenceState ObjectIdentity) : Prop where
  groupedResponseKeysUnique :
    PairKeysNodup
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)
  groupedFieldsResolveStable :
    CollectedGroupsResolveStable state.window.resolvers state.window.source
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet)

mutual
  theorem inputValue_structuralEquivalent_refl :
      ∀ value : InputValue,
        InputValue.structuralEquivalent value value
    | .null => by simp [InputValue.structuralEquivalent]
    | .int value => by simp [InputValue.structuralEquivalent]
    | .float value => by simp [InputValue.structuralEquivalent]
    | .string value => by simp [InputValue.structuralEquivalent]
    | .boolean value => by simp [InputValue.structuralEquivalent]
    | .enum value => by simp [InputValue.structuralEquivalent]
    | .variable name => by simp [InputValue.structuralEquivalent]
    | .list values => by
        simp [InputValue.structuralEquivalent,
          inputValue_structuralValuesEquivalent_refl values]
    | .object fields => by
        simp [InputValue.structuralEquivalent,
          inputValue_structuralObjectFieldsEquivalent_refl fields]

  theorem inputValue_structuralValuesEquivalent_refl :
      ∀ values : List InputValue,
        InputValue.structuralValuesEquivalent values values
    | [] => by simp [InputValue.structuralValuesEquivalent]
    | value :: rest => by
        simp [InputValue.structuralValuesEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputValue_structuralValuesEquivalent_refl rest]

  theorem inputValue_structuralObjectFieldsEquivalent_refl :
      ∀ fields : List (Name × InputValue),
        InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => by simp [InputValue.structuralObjectFieldsEquivalent]
    | (name, value) :: rest => by
        simp [InputValue.structuralObjectFieldsEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputValue_structuralObjectFieldsEquivalent_refl rest]
end

theorem inputValue_equivalent_refl (value : InputValue) :
    value.equivalent value := by
  exact inputValue_structuralEquivalent_refl value.canonical

theorem fieldsForNameCanMerge_executable_identity
    (schema : Schema) (first later : ExecutableField)
    (firstOutputType laterOutputType : TypeRef) :
    FieldMerge.fieldsForNameCanMerge schema
      { parentType := first.parentType
        responseName := first.responseName
        fieldName := first.fieldName
        arguments := first.arguments
        outputType := firstOutputType
        selectionSet := first.selectionSet }
      { parentType := later.parentType
        responseName := later.responseName
        fieldName := later.fieldName
        arguments := later.arguments
        outputType := laterOutputType
        selectionSet := later.selectionSet } ->
    first.parentType = later.parentType ->
      first.fieldName = later.fieldName ∧
      Argument.argumentsEquivalent first.arguments later.arguments := by
  intro hmerge hparent
  exact FieldMerge.fieldsForNameCanMerge_same_parent_identity hmerge hparent

theorem fieldsInSetCanMerge_scoped_collectFields_compatible
    (schema : Schema) (parentType : Name) (selectionSet : List Selection) :
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      ScopedFieldsValidationMergeCompatible
        (FieldMerge.collectFields schema parentType selectionSet) := by
  intro hmerge first later hfirst hlater hresponse hparent
  exact FieldMerge.fieldsForNameCanMerge_same_parent_identity
    (FieldMerge.fieldsInSetCanMerge_pair hmerge hfirst hlater hresponse)
    hparent

theorem ScopedFieldsValidationMergeCompatible.fieldCompatible
    (fields : List FieldMerge.ScopedField) :
    ScopedFieldsSameResponseParent fields ->
    ScopedFieldsValidationMergeCompatible fields ->
      ScopedFieldsFieldValidationMergeCompatible fields := by
  intro hsameParent hcompatible first later hfirst hlater hresponse
  exact hcompatible first later hfirst hlater hresponse
    (hsameParent first later hfirst hlater hresponse)

theorem fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
    (schema : Schema) (parentType : Name) (selectionSet : List Selection) :
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    ScopedFieldsSameResponseParent
      (FieldMerge.collectFields schema parentType selectionSet) ->
      ScopedFieldsFieldValidationMergeCompatible
        (FieldMerge.collectFields schema parentType selectionSet) := by
  intro hmerge hsameParent
  exact ScopedFieldsValidationMergeCompatible.fieldCompatible
    (FieldMerge.collectFields schema parentType selectionSet)
    hsameParent
      (fieldsInSetCanMerge_scoped_collectFields_compatible schema parentType
        selectionSet hmerge)

theorem fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_runtimeApplies
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) :
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    (∀ scopedField,
      scopedField ∈ FieldMerge.collectFields schema parentType selectionSet ->
        ScopedFieldRuntimeApplies schema runtimeType scopedField) ->
      ScopedFieldsFieldValidationMergeCompatible
        (FieldMerge.collectFields schema parentType selectionSet) := by
  intro hmerge happlies first later hfirst hlater hresponse
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema first later :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hfirst hlater hresponse
  exact FieldMerge.fieldsForNameCanMerge_identity hfieldMerge
    (ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
      first later (happlies first hfirst) (happlies later hlater))

theorem ScopedFieldsValidationMergeCompatible.executable_sameParent
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) :
    ScopedFieldsValidationMergeCompatible scopedFields ->
    ExecutableFieldsScopedBy scopedFields fields ->
      ExecutableFieldsSameParentValidationMergeCompatible fields := by
  intro hcompatible hscoped first later hfirst hlater hresponse hparent
  rcases hscoped first hfirst with ⟨firstScoped, hfirstScopedMem,
    hfirstScopedMatch⟩
  rcases hscoped later hlater with ⟨laterScoped, hlaterScopedMem,
    hlaterScopedMatch⟩
  rcases hfirstScopedMatch with
    ⟨hfirstParent, hfirstResponse, hfirstField, hfirstArguments,
      _hfirstSelection⟩
  rcases hlaterScopedMatch with
    ⟨hlaterParent, hlaterResponse, hlaterField, hlaterArguments,
      _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  have hscopedParent :
      firstScoped.parentType = laterScoped.parentType := by
    rw [hfirstParent, hlaterParent]
    exact hparent
  rcases hcompatible firstScoped laterScoped hfirstScopedMem hlaterScopedMem
      hscopedResponse hscopedParent with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem ScopedFieldsFieldValidationMergeCompatible.executable
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) :
    ScopedFieldsFieldValidationMergeCompatible scopedFields ->
    ExecutableFieldsScopedBy scopedFields fields ->
      ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hcompatible hscoped first later hfirst hlater hresponse
  rcases hscoped first hfirst with ⟨firstScoped, hfirstScopedMem,
    hfirstScopedMatch⟩
  rcases hscoped later hlater with ⟨laterScoped, hlaterScopedMem,
    hlaterScopedMatch⟩
  rcases hfirstScopedMatch with
    ⟨_hfirstParent, hfirstResponse, hfirstField, hfirstArguments,
      _hfirstSelection⟩
  rcases hlaterScopedMatch with
    ⟨_hlaterParent, hlaterResponse, hlaterField, hlaterArguments,
      _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  rcases hcompatible firstScoped laterScoped hfirstScopedMem hlaterScopedMem
      hscopedResponse with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem ScopedFieldsFieldValidationMergeCompatible.executable_identity
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField) :
    ScopedFieldsFieldValidationMergeCompatible scopedFields ->
    ExecutableFieldsIdentityScopedBy scopedFields fields ->
      ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hcompatible hscoped first later hfirst hlater hresponse
  rcases hscoped first hfirst with ⟨firstScoped, hfirstScopedMem,
    hfirstScopedMatch⟩
  rcases hscoped later hlater with ⟨laterScoped, hlaterScopedMem,
    hlaterScopedMatch⟩
  rcases hfirstScopedMatch with
    ⟨hfirstResponse, hfirstField, hfirstArguments, _hfirstSelection⟩
  rcases hlaterScopedMatch with
    ⟨hlaterResponse, hlaterField, hlaterArguments, _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  rcases hcompatible firstScoped laterScoped hfirstScopedMem hlaterScopedMem
      hscopedResponse with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem fieldsInSetCanMerge_executable_runtimeScoped
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField) :
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    ExecutableFieldsRuntimeScopedBy schema runtimeType
      (FieldMerge.collectFields schema parentType selectionSet) fields ->
      ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hmerge hscoped first later hfirst hlater hresponse
  rcases hscoped first hfirst with
    ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
  rcases hscoped later hlater with
    ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨hfirstResponse, hfirstField, hfirstArguments, _hfirstSelection⟩
  rcases hlaterMatch with
    ⟨hlaterResponse, hlaterField, hlaterArguments, _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema firstScoped laterScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse
  rcases
      FieldMerge.fieldsForNameCanMerge_identity hfieldMerge
        (ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
          firstScoped laterScoped hfirstRuntime hlaterRuntime) with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (responseName : Name)
    (fields : List ExecutableField) :
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    (∀ field, field ∈ fields -> field.responseName = responseName) ->
    ExecutableFieldsRuntimeScopedBy schema runtimeType
      (FieldMerge.collectFields schema parentType selectionSet) fields ->
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hmerge hresponses hscoped objectType
  apply FieldMerge.fieldsInSetCanMerge_mergedFieldSelectionSet_of_pairwise
  intro first hfirst later hlater
  rcases hscoped first hfirst with
    ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
  rcases hscoped later hlater with
    ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨hfirstResponse, _hfirstField, _hfirstArguments, hfirstSelectionSet⟩
  rcases hlaterMatch with
    ⟨hlaterResponse, _hlaterField, _hlaterArguments, hlaterSelectionSet⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse, hresponses first hfirst,
      hresponses later hlater]
  have hparents :
      firstScoped.parentType = laterScoped.parentType
        ∨ ¬schema.objectType firstScoped.parentType
        ∨ ¬schema.objectType laterScoped.parentType :=
    ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
      firstScoped laterScoped hfirstRuntime hlaterRuntime
  simpa [hfirstSelectionSet, hlaterSelectionSet] using
    FieldMerge.fieldsInSetCanMerge_pair_subfields schema parentType
      selectionSet firstScoped laterScoped hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse hparents objectType

theorem collectFields_group_mergedFieldSelectionSet_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField) :
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    GraphQL.Execution.collectFields schema variableValues collectParent
      (.object runtimeType (some identity)) selectionSet = groups ->
    (responseName, fields) ∈ groups ->
    CollectedGroupsResponseName groups ->
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hvalid hmerge hparentRuntime hcollect hgroup hresponses
  apply fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped
    schema validParent runtimeType selectionSet responseName fields hmerge
  · intro field hfield
    exact hresponses responseName fields hgroup field hfield
  · have hscopedAll :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields groups) := by
      rw [← hcollect]
      exact collectFields_runtimeScopedBy_of_selectionSetValid schema
        variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet hparentRuntime hvalid
    intro field hfield
    exact hscopedAll field
      (collectedExecutableFields_mem_of_group_mem hgroup hfield)

theorem collectFields_group_mergedFieldSelectionSet_canMerge_of_valid_root_operation
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (operation : Operation)
    (runtimeType : Name) (identity : ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField) :
    rootSourceAppliesBool schema operation (.object runtimeType (some identity)) =
      true ->
    Validation.operationDefinitionValid schema operation ->
    GraphQL.Execution.collectFields schema variableValues operation.rootType
      (.object runtimeType (some identity)) operation.selectionSet = groups ->
    (responseName, fields) ∈ groups ->
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hroot hvalid hcollect hgroup
  apply collectFields_group_mergedFieldSelectionSet_canMerge_runtimeScoped
    schema operation.variableDefinitions variableValues operation.rootType
    operation.rootType runtimeType identity operation.selectionSet groups
    responseName fields
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  · exact ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      runtimeType identity hroot
  · exact hcollect
  · exact hgroup
  · rw [← hcollect]
    exact collectFields_responseName schema variableValues operation.rootType
      (.object runtimeType (some identity)) operation.selectionSet

theorem collectFields_fieldCompatible_of_selectionSetValid_scopedCompatible
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent : Name)
    (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    Validation.selectionSetValid schema variableDefinitions validParent
      selectionSet ->
    ScopedFieldsFieldValidationMergeCompatible
      (FieldMerge.collectFields schema validParent selectionSet) ->
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues collectParent
          source selectionSet) := by
  intro hvalid hscopedCompatible
  apply CollectedGroupsFieldValidationMergeCompatible.of_collectedExecutableFields
  exact ScopedFieldsFieldValidationMergeCompatible.executable_identity
    (FieldMerge.collectFields schema validParent selectionSet)
    (collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues collectParent source
        selectionSet))
    hscopedCompatible
    (collectFields_identityScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent source
      selectionSet hvalid)

theorem collectFields_fieldCompatible_of_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    ExecutableFieldsRuntimeScopedBy schema runtimeType
      (FieldMerge.collectFields schema validParent selectionSet)
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues collectParent
          source selectionSet)) ->
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues collectParent
          source selectionSet) := by
  intro hmerge hscoped
  apply CollectedGroupsFieldValidationMergeCompatible.of_collectedExecutableFields
  exact fieldsInSetCanMerge_executable_runtimeScoped schema validParent
    runtimeType selectionSet
    (collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues collectParent
        source selectionSet))
    hmerge hscoped

theorem collectFields_fieldCompatible_of_canMerge_lookupValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection) :
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType (some identity)) selectionSet) := by
  intro hmerge hparentRuntime hlookupValid
  apply collectFields_fieldCompatible_of_canMerge_runtimeScoped
    schema variableValues collectParent validParent runtimeType
    (.object runtimeType (some identity)) selectionSet hmerge
  exact collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
    variableValues collectParent validParent runtimeType identity selectionSet
    hparentRuntime hlookupValid

theorem collectFields_fieldCompatible_of_canMerge_lookupValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : Option ObjectIdentity)
    (selectionSet : List Selection) :
    FieldMerge.fieldsInSetCanMerge schema validParent selectionSet ->
    ScopedParentRuntimeApplies schema runtimeType validParent ->
    NormalForm.selectionSetLookupValid schema validParent selectionSet ->
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet) := by
  intro hmerge hparentRuntime hlookupValid
  apply collectFields_fieldCompatible_of_canMerge_runtimeScoped
    schema variableValues collectParent validParent runtimeType
    (.object runtimeType identity) selectionSet hmerge
  exact collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
    variableValues collectParent validParent runtimeType identity selectionSet
    hparentRuntime hlookupValid

theorem ExecutableFieldsMergeCompatible.to_validation
    (fields : List ExecutableField) :
    ExecutableFieldsMergeCompatible fields ->
      ExecutableFieldsValidationMergeCompatible fields := by
  intro hcompatible first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hparent, hfield, harguments⟩
  constructor
  · exact hparent
  constructor
  · exact hfield
  · rw [harguments]
    constructor
    · intro argument hmem
      exact ⟨argument, hmem, by exact ⟨rfl, inputValue_equivalent_refl argument.value⟩⟩
    · intro argument hmem
      exact ⟨argument, hmem, by exact ⟨rfl, inputValue_equivalent_refl argument.value⟩⟩

theorem ExecutableFieldsSameParentValidationMergeCompatible.fieldCompatible
    (fields : List ExecutableField) :
    ExecutableFieldsSameResponseParent fields ->
    ExecutableFieldsSameParentValidationMergeCompatible fields ->
      ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hsameParent hcompatible first later hfirst hlater hresponse
  exact hcompatible first later hfirst hlater hresponse
    (hsameParent first later hfirst hlater hresponse)

theorem CollectedGroupsValidationMergeCompatible.fieldCompatible
    (groups : List (Name × List ExecutableField)) :
    CollectedGroupsSameResponseParent groups ->
    CollectedGroupsValidationMergeCompatible groups ->
      CollectedGroupsFieldValidationMergeCompatible groups := by
  intro hsameParent hcompatible responseName fields hmem
  exact ExecutableFieldsSameParentValidationMergeCompatible.fieldCompatible
    fields
    (hsameParent responseName fields hmem)
    (hcompatible responseName fields hmem)

theorem ExecutableFieldsMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) (fields : List ExecutableField) :
    ExecutableFieldsMergeCompatible fields ->
      ExecutableFieldsResolveStable resolvers source fields := by
  intro hcompatible first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hparent, hfield, harguments⟩
  simp [hparent, hfield, harguments]

theorem ExecutableFieldsSameParentValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) (fields : List ExecutableField) :
    ResolversRespectArgumentEquivalence resolvers source ->
    ExecutableFieldsSameResponseParent fields ->
    ExecutableFieldsSameParentValidationMergeCompatible fields ->
      ExecutableFieldsResolveStable resolvers source fields := by
  intro hresolvers hsameParent hcompatible first later hfirst hlater hresponse
  have hparent := hsameParent first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse hparent with
    ⟨hfield, harguments⟩
  rw [hparent, hfield]
  exact hresolvers later.parentType later.fieldName first.arguments
    later.arguments harguments

theorem ExecutableFieldsFieldValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) (fields : List ExecutableField) :
    ResolversRespectFieldAndArgumentEquivalence resolvers source ->
    ExecutableFieldsFieldValidationMergeCompatible fields ->
      ExecutableFieldsResolveStable resolvers source fields := by
  intro hresolvers hcompatible first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hfield, harguments⟩
  rw [hfield]
  exact hresolvers first.parentType later.parentType later.fieldName
    first.arguments later.arguments harguments

theorem ExecutableFieldsFieldValidationMergeCompatible.resolveStableValid
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity) (fields : List ExecutableField) :
    ResolversRespectValidFieldAndArgumentEquivalence resolvers source ->
    ExecutableFieldsFieldValidationMergeCompatible fields ->
    ExecutableFieldsArgumentsNodup fields ->
      ExecutableFieldsResolveStable resolvers source fields := by
  intro hresolvers hcompatible hnodup first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hfield, harguments⟩
  rw [hfield]
  exact hresolvers first.parentType later.parentType later.fieldName
    first.arguments later.arguments (hnodup first hfirst)
    (hnodup later hlater) harguments

theorem CollectedGroupsValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) :
    ResolversRespectArgumentEquivalence resolvers source ->
    CollectedGroupsSameResponseParent groups ->
    CollectedGroupsValidationMergeCompatible groups ->
      CollectedGroupsResolveStable resolvers source groups := by
  intro hresolvers hsameParent hcompatible responseName fields hmem
  exact
    ExecutableFieldsSameParentValidationMergeCompatible.resolveStable
      resolvers source fields hresolvers
      (hsameParent responseName fields hmem)
      (hcompatible responseName fields hmem)

theorem CollectedGroupsFieldValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) :
    ResolversRespectFieldAndArgumentEquivalence resolvers source ->
    CollectedGroupsFieldValidationMergeCompatible groups ->
      CollectedGroupsResolveStable resolvers source groups := by
  intro hresolvers hcompatible responseName fields hmem
  exact
    ExecutableFieldsFieldValidationMergeCompatible.resolveStable resolvers
      source fields hresolvers (hcompatible responseName fields hmem)

theorem CollectedGroupsFieldValidationMergeCompatible.resolveStableValid
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) :
    ResolversRespectValidFieldAndArgumentEquivalence resolvers source ->
    CollectedGroupsFieldValidationMergeCompatible groups ->
    CollectedGroupsArgumentsNodup groups ->
      CollectedGroupsResolveStable resolvers source groups := by
  intro hresolvers hcompatible hnodup responseName fields hmem
  exact
    ExecutableFieldsFieldValidationMergeCompatible.resolveStableValid resolvers
      source fields hresolvers (hcompatible responseName fields hmem)
      (hnodup responseName fields hmem)

theorem ExecutionSemanticStateInvariant.groupedFieldsResolveStable
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionSemanticStateInvariant state ->
      ∀ responseName fields,
        (responseName, fields) ∈
          GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet ->
        ExecutableFieldsResolveStable state.window.resolvers
          state.window.source fields := by
  intro hinvariant responseName fields hmem
  exact
    CollectedGroupsValidationMergeCompatible.resolveStable
      state.window.resolvers state.window.source
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.resolversRespectArgumentEquivalence
      hinvariant.groupedFieldsSameParent
      hinvariant.groupedFieldsValidationCompatible
      responseName fields hmem

theorem ExecutionFieldSemanticStateInvariant.groupedFieldsResolveStable
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionFieldSemanticStateInvariant state ->
      ∀ responseName fields,
        (responseName, fields) ∈
          GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet ->
        ExecutableFieldsResolveStable state.window.resolvers
          state.window.source fields := by
  intro hinvariant responseName fields hmem
  exact
    CollectedGroupsFieldValidationMergeCompatible.resolveStable
      state.window.resolvers state.window.source
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.resolversRespectFieldAndArgumentEquivalence
      hinvariant.groupedFieldsFieldCompatible
      responseName fields hmem

theorem ExecutionValidFieldSemanticStateInvariant.groupedFieldsResolveStable
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionValidFieldSemanticStateInvariant state ->
      ∀ responseName fields,
        (responseName, fields) ∈
          GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet ->
        ExecutableFieldsResolveStable state.window.resolvers
          state.window.source fields := by
  intro hinvariant responseName fields hmem
  exact
    CollectedGroupsFieldValidationMergeCompatible.resolveStableValid
      state.window.resolvers state.window.source
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.resolversRespectValidFieldAndArgumentEquivalence
      hinvariant.groupedFieldsFieldCompatible
      hinvariant.groupedFieldsArgumentsNodup
      responseName fields hmem

theorem ExecutionCollectedFieldInvariant.of_stateInvariant
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionStateInvariant state ->
      ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact hinvariant.groupedFieldsResolveStable

theorem ExecutionCollectedFieldInvariant.of_semantic
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionSemanticStateInvariant state ->
      ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact ExecutionSemanticStateInvariant.groupedFieldsResolveStable state
      hinvariant

theorem ExecutionCollectedFieldInvariant.of_fieldSemantic
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionFieldSemanticStateInvariant state ->
      ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact ExecutionFieldSemanticStateInvariant.groupedFieldsResolveStable state
      hinvariant

theorem ExecutionCollectedFieldInvariant.of_validFieldSemantic
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionValidFieldSemanticStateInvariant state ->
      ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact ExecutionValidFieldSemanticStateInvariant.groupedFieldsResolveStable
      state hinvariant

theorem ExecutionCollectedFieldInvariant.responseName_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hcollect :
      GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet = groups) :
    CollectedGroupsResponseName groups := by
  rw [← hcollect]
  exact collectFields_responseName state.window.schema
    state.window.variableValues state.window.parentType state.window.source
    state.window.selectionSet

theorem ExecutionCollectedFieldInvariant.parent_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hcollect :
      GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet = groups) :
    CollectedGroupsParent state.window.parentType groups := by
  rw [← hcollect]
  exact collectFields_parent state.window.schema state.window.variableValues
    state.window.parentType state.window.source state.window.selectionSet

theorem ExecutionCollectedFieldInvariant.pairKeysNodup_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hinvariant : ExecutionCollectedFieldInvariant state)
    (hcollect :
      GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet = groups) :
    PairKeysNodup groups := by
  rw [← hcollect]
  exact hinvariant.groupedResponseKeysUnique

theorem ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hinvariant : ExecutionCollectedFieldInvariant state)
    (hcollect :
      GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet = groups) :
    CollectedGroupsResolveStable state.window.resolvers state.window.source
      groups := by
  rw [← hcollect]
  exact hinvariant.groupedFieldsResolveStable

theorem ExecutionCollectedFieldInvariant.groupResolveStable_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField)
    (hinvariant : ExecutionCollectedFieldInvariant state)
    (hcollect :
      GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType state.window.source
        state.window.selectionSet = groups)
    (hgroup : (responseName, fields) ∈ groups) :
    ExecutableFieldsResolveStable state.window.resolvers state.window.source
      fields :=
  (hinvariant.resolveStable_of_collect_eq state groups hcollect)
    responseName fields hgroup

theorem ExecutionSemanticStateInvariant.of_grouped_validation
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique :
      PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hsameParent :
      CollectedGroupsSameResponseParent
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hcompatible :
      CollectedGroupsValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hresolvers :
      ResolversRespectArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionSemanticStateInvariant state := by
  constructor
  · exact hunique
  · exact hsameParent
  · exact hcompatible
  · exact hresolvers

theorem ExecutionFieldSemanticStateInvariant.of_grouped_validation
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique :
      PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hcompatible :
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hresolvers :
      ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionFieldSemanticStateInvariant state := by
  constructor
  · exact hunique
  · exact hcompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_grouped_validation
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique :
      PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hcompatible :
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hargumentsNodup :
      CollectedGroupsArgumentsNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  constructor
  · exact hunique
  · exact hcompatible
  · exact hargumentsNodup
  · exact hresolvers

theorem ExecutionFieldSemanticStateInvariant.of_semantic_same_parent
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity) :
    ExecutionSemanticStateInvariant state ->
    ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
      state.window.source ->
      ExecutionFieldSemanticStateInvariant state := by
  intro hinvariant hresolvers
  apply ExecutionFieldSemanticStateInvariant.of_grouped_validation state
  · exact hinvariant.groupedResponseKeysUnique
  · exact CollectedGroupsValidationMergeCompatible.fieldCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.groupedFieldsSameParent
      hinvariant.groupedFieldsValidationCompatible
  · exact hresolvers

theorem ExecutionSemanticStateInvariant.of_collected_groups
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups :
      List (Name × List ExecutableField))
    (hgroups :
      groups =
        GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet)
    (hunique : PairKeysNodup groups)
    (hsameParent : CollectedGroupsSameResponseParent groups)
    (hcompatible : CollectedGroupsValidationMergeCompatible groups)
    (hresolvers :
      ResolversRespectArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionSemanticStateInvariant state := by
  apply ExecutionSemanticStateInvariant.of_grouped_validation state
  · simpa [← hgroups] using hunique
  · simpa [← hgroups] using hsameParent
  · simpa [← hgroups] using hcompatible
  · exact hresolvers

theorem ExecutionFieldSemanticStateInvariant.of_collected_groups
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups :
      List (Name × List ExecutableField))
    (hgroups :
      groups =
        GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet)
    (hunique : PairKeysNodup groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hresolvers :
      ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionFieldSemanticStateInvariant state := by
  apply ExecutionFieldSemanticStateInvariant.of_grouped_validation state
  · simpa [← hgroups] using hunique
  · simpa [← hgroups] using hcompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_collected_groups
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups :
      List (Name × List ExecutableField))
    (hgroups :
      groups =
        GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet)
    (hunique : PairKeysNodup groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hargumentsNodup : CollectedGroupsArgumentsNodup groups)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · simpa [← hgroups] using hunique
  · simpa [← hgroups] using hcompatible
  · simpa [← hgroups] using hargumentsNodup
  · exact hresolvers

theorem ExecutionStateInvariant.of_grouped_compatible
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique :
      PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hcompatible :
      ∀ responseName fields,
        (responseName, fields) ∈
          GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet ->
          ExecutableFieldsMergeCompatible fields) :
    ExecutionStateInvariant state := by
  constructor
  · exact hunique
  · exact hcompatible
  · intro responseName fields hmem
    exact ExecutableFieldsMergeCompatible.resolveStable state.window.resolvers
      state.window.source fields (hcompatible responseName fields hmem)


end ExecutionUngrouped
end Algorithms

end GraphQL
