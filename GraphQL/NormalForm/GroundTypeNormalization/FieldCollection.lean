import GraphQL.NormalForm.GroundTypeNormalization

/-!
Field-collection helper lemmas for directive-free ground-type normalization.

This module separates execution-facing collection facts from the structural normal-form
proofs in `GraphQL.NormalForm.GroundTypeNormalization`.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def executableGroupNamesNodup :
    List (Name × List Execution.ExecutableField) -> Prop
  | [] => True
  | (responseName, _fields) :: rest =>
      responseName ∉ rest.map Prod.fst ∧ executableGroupNamesNodup rest

def executableGroupNamesDisjoint
    (left right : List (Name × List Execution.ExecutableField)) : Prop :=
  ∀ responseName,
    responseName ∈ left.map Prod.fst ->
      responseName ∈ right.map Prod.fst -> False

def executableFieldsMatchResponseName
    (responseName : Name) (fields : List Execution.ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> field.responseName = responseName

def executableGroupWellFormed
    (group : Name × List Execution.ExecutableField) : Prop :=
  group.snd ≠ [] ∧ executableFieldsMatchResponseName group.fst group.snd

def executableGroupsWellFormed
    (groups : List (Name × List Execution.ExecutableField)) : Prop :=
  ∀ group, group ∈ groups -> executableGroupWellFormed group

def collectedResponseSelectionSet
    (responseName : Name) :
    List (Name × List Execution.ExecutableField) -> List Selection
  | [] => []
  | (groupResponseName, fields) :: rest =>
      if groupResponseName == responseName then
        Execution.mergedFieldSelectionSet fields
      else
        collectedResponseSelectionSet responseName rest

def executableFieldScoped? (schema : Schema)
    (field : Execution.ExecutableField) : Option FieldMerge.ScopedField := do
  let fieldDefinition <- schema.lookupField field.parentType field.fieldName
  some {
    parentType := field.parentType,
    responseName := field.responseName,
    fieldName := field.fieldName,
    arguments := field.arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := field.selectionSet
  }

theorem executableFieldScoped?_some
    {schema : Schema} {field : Execution.ExecutableField}
    {scopedField : FieldMerge.ScopedField} :
    executableFieldScoped? schema field = some scopedField ->
      ∃ fieldDefinition,
        schema.lookupField field.parentType field.fieldName =
          some fieldDefinition
          ∧ scopedField = {
            parentType := field.parentType,
            responseName := field.responseName,
            fieldName := field.fieldName,
            arguments := field.arguments,
            outputType := fieldDefinition.outputType,
            selectionSet := field.selectionSet
          } := by
  intro hscoped
  unfold executableFieldScoped? at hscoped
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp [hlookup] at hscoped
  | some fieldDefinition =>
      simp [hlookup] at hscoped
      subst scopedField
      exact ⟨fieldDefinition, rfl, rfl⟩

theorem executableFieldScoped?_sameSelection
    {schema : Schema} {field : Execution.ExecutableField}
    {scopedField : FieldMerge.ScopedField} :
    executableFieldScoped? schema field = some scopedField ->
      scopedField.parentType = field.parentType
        ∧ scopedField.responseName = field.responseName
        ∧ scopedField.fieldName = field.fieldName
        ∧ scopedField.arguments = field.arguments
        ∧ scopedField.selectionSet = field.selectionSet := by
  intro hscoped
  rcases executableFieldScoped?_some hscoped with
    ⟨_fieldDefinition, _hlookup, hshape⟩
  subst scopedField
  simp

theorem executableGroupWellFormed_field_responseName
    {group : Name × List Execution.ExecutableField}
    {field : Execution.ExecutableField} :
    executableGroupWellFormed group ->
      field ∈ group.snd ->
        field.responseName = group.fst := by
  intro hgroup hfield
  exact hgroup.2 field hfield

theorem executableFields_same_parent_identity_of_scoped_merge
    {schema : Schema}
    {left right : Execution.ExecutableField}
    {leftScoped rightScoped : FieldMerge.ScopedField} :
    executableFieldScoped? schema left = some leftScoped ->
      executableFieldScoped? schema right = some rightScoped ->
        FieldMerge.fieldsForNameCanMerge schema leftScoped rightScoped ->
          left.parentType = right.parentType ->
            left.fieldName = right.fieldName
              ∧ Argument.argumentsEquivalent left.arguments right.arguments := by
  intro hleftScoped hrightScoped hmerge hparent
  have hleftShape :=
    executableFieldScoped?_sameSelection hleftScoped
  have hrightShape :=
    executableFieldScoped?_sameSelection hrightScoped
  have hscopedParent :
      leftScoped.parentType = rightScoped.parentType := by
    exact hleftShape.1.trans (hparent.trans hrightShape.1.symm)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_same_parent_identity hmerge
      hscopedParent
  exact ⟨
    hleftShape.2.2.1.symm.trans
      (hidentity.1.trans hrightShape.2.2.1),
    by
      simpa [hleftShape.2.2.2.1, hrightShape.2.2.2.1]
        using hidentity.2⟩

theorem collectedResponseSelectionSet_eq_nil_of_key_absent
    (responseName : Name) :
    ∀ groups,
      responseName ∉ groups.map Prod.fst ->
        collectedResponseSelectionSet responseName groups = []
  | [], _habsent => by
      simp [collectedResponseSelectionSet]
  | group :: rest, habsent => by
      rcases group with ⟨groupResponseName, fields⟩
      have hheadNe : groupResponseName ≠ responseName := by
        intro heq
        exact habsent (by simp [heq])
      have hheadFalse : (groupResponseName == responseName) = false := by
        cases hmatch : groupResponseName == responseName
        · rfl
        · exact False.elim (hheadNe (beq_iff_eq.mp hmatch))
      have hrestAbsent : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact habsent (by simp [hmem])
      simp [collectedResponseSelectionSet, hheadFalse,
        collectedResponseSelectionSet_eq_nil_of_key_absent responseName rest
          hrestAbsent]

theorem collectedResponseSelectionSet_addExecutableGroup
    (responseName : Name) (group : Name × List Execution.ExecutableField) :
    ∀ groups,
      collectedResponseSelectionSet responseName
        (Execution.addExecutableGroup group groups)
        =
      collectedResponseSelectionSet responseName groups
        ++ if group.fst == responseName then
          Execution.mergedFieldSelectionSet group.snd
        else
          []
  | [] => by
      rcases group with ⟨groupResponseName, fields⟩
      by_cases hresponse : (groupResponseName == responseName) = true
      · simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
          hresponse]
      · have hfalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · contradiction
        simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
          hfalse]
  | current :: rest => by
      rcases group with ⟨groupResponseName, groupFields⟩
      rcases current with ⟨currentName, currentFields⟩
      by_cases hcurrentGroup : (currentName == groupResponseName) = true
      · have hcurrentEq : currentName = groupResponseName :=
          beq_iff_eq.mp hcurrentGroup
        subst currentName
        by_cases hresponse : (groupResponseName == responseName) = true
        · simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hresponse, Execution.mergedFieldSelectionSet_append]
        · have hresponseFalse : (groupResponseName == responseName) = false := by
            cases hmatch : groupResponseName == responseName
            · rfl
            · contradiction
          simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hresponseFalse]
      · have hcurrentGroupFalse :
            (currentName == groupResponseName) = false := by
          cases hmatch : currentName == groupResponseName
          · rfl
          · contradiction
        by_cases hcurrentResponse : (currentName == responseName) = true
        · have hgroupResponseFalse :
              (groupResponseName == responseName) = false := by
            cases hmatch : groupResponseName == responseName
            · rfl
            · have hcr : currentName = responseName :=
                beq_iff_eq.mp hcurrentResponse
              have hgr : groupResponseName = responseName :=
                beq_iff_eq.mp hmatch
              subst currentName
              subst groupResponseName
              simp at hcurrentGroupFalse
          simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hcurrentGroupFalse, hcurrentResponse, hgroupResponseFalse]
        · have hcurrentResponseFalse :
              (currentName == responseName) = false := by
            cases hmatch : currentName == responseName
            · rfl
            · contradiction
          simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hcurrentGroupFalse, hcurrentResponseFalse,
            collectedResponseSelectionSet_addExecutableGroup responseName
              (groupResponseName, groupFields) rest]

theorem collectedResponseSelectionSet_mergeExecutableGroups
    (responseName : Name) :
    ∀ left right,
      executableGroupNamesNodup right ->
        collectedResponseSelectionSet responseName
          (Execution.mergeExecutableGroups left right)
          =
        collectedResponseSelectionSet responseName left
          ++ collectedResponseSelectionSet responseName right
  | left, [], _hnodup => by
      simp [Execution.mergeExecutableGroups, collectedResponseSelectionSet]
  | left, group :: rest, hnodup => by
      rcases group with ⟨groupResponseName, fields⟩
      have hrestNodup : executableGroupNamesNodup rest := hnodup.2
      have hrestMerge :=
        collectedResponseSelectionSet_mergeExecutableGroups responseName
          (Execution.addExecutableGroup (groupResponseName, fields) left)
          rest hrestNodup
      by_cases hresponse : (groupResponseName == responseName) = true
      · have hresponseEq : groupResponseName = responseName :=
          beq_iff_eq.mp hresponse
        subst groupResponseName
        have hrestSelection :
            collectedResponseSelectionSet responseName rest = [] :=
          collectedResponseSelectionSet_eq_nil_of_key_absent responseName rest
            hnodup.1
        simp [Execution.mergeExecutableGroups] at hrestMerge ⊢
        rw [hrestMerge,
          collectedResponseSelectionSet_addExecutableGroup responseName
            (responseName, fields) left]
        simp [collectedResponseSelectionSet, hrestSelection]
      · have hresponseFalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · contradiction
        simp [Execution.mergeExecutableGroups] at hrestMerge ⊢
        rw [hrestMerge,
          collectedResponseSelectionSet_addExecutableGroup responseName
            (groupResponseName, fields) left]
        simp [collectedResponseSelectionSet, hresponseFalse]

theorem executableGroupWellFormed_singleton_field
    (field : Execution.ExecutableField) :
    executableGroupWellFormed (field.responseName, [field]) := by
  constructor
  · simp
  · intro candidate hcandidate
    simp at hcandidate
    subst candidate
    rfl

theorem executableGroupsWellFormed_nil :
    executableGroupsWellFormed [] := by
  intro group hgroup
  simp at hgroup

theorem executableGroupsWellFormed_tail
    {group : Name × List Execution.ExecutableField}
    {groups : List (Name × List Execution.ExecutableField)} :
    executableGroupsWellFormed (group :: groups) ->
      executableGroupsWellFormed groups := by
  intro hgroups candidate hcandidate
  exact hgroups candidate (by simp [hcandidate])

theorem addExecutableGroup_wellFormed
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField)) :
    executableGroupWellFormed group ->
      executableGroupsWellFormed groups ->
        executableGroupsWellFormed
          (Execution.addExecutableGroup group groups) := by
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro candidate hcandidate
      simp [Execution.addExecutableGroup] at hcandidate
      subst candidate
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == group.fst) = true
      · have hcurrentName : currentName = group.fst := beq_iff_eq.mp hname
        intro candidate hcandidate
        simp [Execution.addExecutableGroup, hname] at hcandidate
        rcases hcandidate with hhead | htail
        · subst candidate
          have hcurrent :
              executableGroupWellFormed (currentName, currentFields) :=
            hgroups (currentName, currentFields) (by simp)
          constructor
          · intro hnil
            simp at hnil
            exact hcurrent.1 hnil.1
          · intro field hfield
            rcases List.mem_append.mp hfield with hfieldCurrent | hfieldGroup
            · exact hcurrent.2 field hfieldCurrent
            · exact (hgroup.2 field hfieldGroup).trans hcurrentName.symm
        · exact hgroups candidate (by simp [htail])
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        intro candidate hcandidate
        simp [Execution.addExecutableGroup, hfalse] at hcandidate
        rcases hcandidate with hhead | htail
        · subst candidate
          exact hgroups (currentName, currentFields) (by simp)
        · exact ih (executableGroupsWellFormed_tail hgroups) candidate
            htail

theorem mergeExecutableGroups_wellFormed
    (left right : List (Name × List Execution.ExecutableField)) :
    executableGroupsWellFormed left ->
      executableGroupsWellFormed right ->
        executableGroupsWellFormed
          (Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      simp [Execution.mergeExecutableGroups]
      exact ih (Execution.addExecutableGroup group left)
        (addExecutableGroup_wellFormed group left
          (hright group (by simp)) hleft)
        (executableGroupsWellFormed_tail hright)

theorem addExecutableGroup_mem_responseName
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    (responseName : Name) :
    responseName ∈ (Execution.addExecutableGroup group groups).map Prod.fst
      ↔ responseName = group.fst ∨ responseName ∈ groups.map Prod.fst := by
  induction groups with
  | nil =>
      simp [Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      by_cases hname : (currentName == group.fst) = true
      · have hcurrent : currentName = group.fst := beq_iff_eq.mp hname
        subst currentName
        simp [Execution.addExecutableGroup]
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        have hne : currentName ≠ group.fst := by
          intro heq
          subst currentName
          simp at hfalse
        simp [Execution.addExecutableGroup, hfalse, ih, or_left_comm]

theorem addExecutableGroup_namesNodup
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField)) :
    executableGroupNamesNodup groups ->
      executableGroupNamesNodup
        (Execution.addExecutableGroup group groups) := by
  induction groups with
  | nil =>
      intro _hnodup
      simp [executableGroupNamesNodup, Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      intro hnodup
      by_cases hname : (currentName == group.fst) = true
      · simpa [Execution.addExecutableGroup, hname] using hnodup
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        have hne : currentName ≠ group.fst := by
          intro heq
          subst currentName
          simp at hfalse
        have hrest :
            executableGroupNamesNodup rest := by
          exact hnodup.2
        have hadded := ih hrest
        simp [Execution.addExecutableGroup, hfalse]
        constructor
        · intro hmem
          exact hnodup.1
            ((addExecutableGroup_mem_responseName group rest currentName).mp
              hmem
              |>.elim (fun heq => False.elim (hne heq))
                (fun hin => hin))
        · exact hadded

theorem addExecutableGroup_of_responseName_not_mem
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField)) :
    group.fst ∉ groups.map Prod.fst ->
      Execution.addExecutableGroup group groups = groups ++ [group] := by
  induction groups with
  | nil =>
      intro _hnotin
      simp [Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      intro hnotin
      have hcurrentNe : currentName ≠ group.fst := by
        intro heq
        exact hnotin (by simp [heq])
      have hfalse : (currentName == group.fst) = false := by
        cases hmatch : currentName == group.fst
        · rfl
        · exact False.elim (hcurrentNe (beq_iff_eq.mp hmatch))
      have hrestNotin : group.fst ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotin (by simp [hmem])
      simp [Execution.addExecutableGroup, hfalse, ih hrestNotin]

theorem addExecutableGroup_same_response_append
    (responseName : Name) (currentFields : List Execution.ExecutableField)
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField)) :
    group.fst = responseName ->
      Execution.addExecutableGroup group
          (Execution.addExecutableGroup (responseName, currentFields) groups)
        =
      Execution.addExecutableGroup
        (responseName, currentFields ++ group.snd) groups := by
  intro hname
  induction groups with
  | nil =>
      subst responseName
      simp [Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      subst responseName
      by_cases hcurrent : (currentName == group.fst) = true
      · simp [Execution.addExecutableGroup, hcurrent, List.append_assoc]
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        simpa [Execution.addExecutableGroup, hfalse] using ih

theorem addExecutableGroup_comm_of_responseName_ne_of_mem
    (leftGroup rightGroup : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField)) :
    leftGroup.fst ≠ rightGroup.fst ->
      leftGroup.fst ∈ groups.map Prod.fst ->
        Execution.addExecutableGroup leftGroup
            (Execution.addExecutableGroup rightGroup groups)
          =
        Execution.addExecutableGroup rightGroup
          (Execution.addExecutableGroup leftGroup groups) := by
  intro hne hmem
  induction groups with
  | nil =>
      cases hmem
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      rcases leftGroup with ⟨leftName, leftFields⟩
      rcases rightGroup with ⟨rightName, rightFields⟩
      by_cases hcurrentLeft : (currentName == leftName) = true
      · have hcurrentRight : (currentName == rightName) = false := by
          cases hmatch : currentName == rightName
          · rfl
          · have hcl : currentName = leftName := beq_iff_eq.mp hcurrentLeft
            have hcr : currentName = rightName := beq_iff_eq.mp hmatch
            exact False.elim (hne (by rw [← hcl, hcr]))
        simp [Execution.addExecutableGroup, hcurrentLeft, hcurrentRight]
      · have hcurrentLeftFalse : (currentName == leftName) = false := by
          cases hmatch : currentName == leftName
          · rfl
          · contradiction
        by_cases hcurrentRight : (currentName == rightName) = true
        · have hcurrentLeft' : (currentName == leftName) = false :=
            hcurrentLeftFalse
          simp [Execution.addExecutableGroup, hcurrentRight, hcurrentLeft']
        · have hcurrentRightFalse : (currentName == rightName) = false := by
            cases hmatch : currentName == rightName
            · rfl
            · contradiction
          have hrestMem : leftName ∈ rest.map Prod.fst := by
            have hcases :
                leftName = currentName ∨ leftName ∈ rest.map Prod.fst := by
              simpa using hmem
            cases hcases with
            | inl heq =>
                have hneCurrentLeft : currentName ≠ leftName := by
                  intro h
                  subst currentName
                  simp at hcurrentLeftFalse
                exact False.elim (hneCurrentLeft heq.symm)
            | inr hrest => exact hrest
          simp [Execution.addExecutableGroup, hcurrentLeftFalse,
            hcurrentRightFalse, ih hrestMem]

theorem addExecutableGroup_mergeExecutableGroups_of_responseName_not_mem
    (group : Name × List Execution.ExecutableField)
    (left middle : List (Name × List Execution.ExecutableField)) :
    group.fst ∉ middle.map Prod.fst ->
      group.fst ∈ left.map Prod.fst ->
        Execution.addExecutableGroup group
            (Execution.mergeExecutableGroups left middle)
          =
        Execution.mergeExecutableGroups
          (Execution.addExecutableGroup group left) middle := by
  intro hnotin hleftMem
  induction middle generalizing left with
  | nil =>
      simp [Execution.mergeExecutableGroups]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      have hcurrentNe : currentName ≠ group.fst := by
        intro heq
        exact hnotin (by simp [heq])
      have hrestNotin : group.fst ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotin (by simp [hmem])
      simp [Execution.mergeExecutableGroups]
      change Execution.addExecutableGroup group
          (Execution.mergeExecutableGroups
            (Execution.addExecutableGroup (currentName, currentFields) left)
            rest)
        =
        Execution.mergeExecutableGroups
          (Execution.addExecutableGroup (currentName, currentFields)
            (Execution.addExecutableGroup group left)) rest
      have hleftMem' :
          group.fst ∈
            (Execution.addExecutableGroup (currentName, currentFields)
              left).map Prod.fst := by
        exact (addExecutableGroup_mem_responseName
          (currentName, currentFields) left group.fst).mpr
          (Or.inr hleftMem)
      rw [ih (Execution.addExecutableGroup (currentName, currentFields) left)
        hrestNotin hleftMem']
      rw [addExecutableGroup_comm_of_responseName_ne_of_mem
        group (currentName, currentFields) left (by
          intro heq
          exact hcurrentNe heq.symm) hleftMem]

theorem addExecutableGroup_mergeExecutableGroups_of_namesNodup
    (group : Name × List Execution.ExecutableField)
    (left middle : List (Name × List Execution.ExecutableField)) :
    executableGroupNamesNodup middle ->
      Execution.addExecutableGroup group
          (Execution.mergeExecutableGroups left middle)
        =
      Execution.mergeExecutableGroups left
        (Execution.addExecutableGroup group middle) := by
  intro hmiddle
  induction middle generalizing left with
  | nil =>
      simp [Execution.mergeExecutableGroups, Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == group.fst) = true
      · simp [Execution.mergeExecutableGroups, Execution.addExecutableGroup,
          hname]
        have hkey : group.fst = currentName := (beq_iff_eq.mp hname).symm
        have hnotin : group.fst ∉ rest.map Prod.fst := by
          intro hmem
          exact hmiddle.1 (by simpa [hkey] using hmem)
        change Execution.addExecutableGroup group
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup (currentName, currentFields)
                left) rest)
          =
          Execution.mergeExecutableGroups
            (Execution.addExecutableGroup
              (currentName, currentFields ++ group.snd) left) rest
        rw [addExecutableGroup_mergeExecutableGroups_of_responseName_not_mem
          group
          (Execution.addExecutableGroup (currentName, currentFields) left)
          rest hnotin
          ((addExecutableGroup_mem_responseName
            (currentName, currentFields) left group.fst).mpr
            (Or.inl hkey))]
        rw [addExecutableGroup_same_response_append currentName currentFields
          group left hkey]
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        simp [Execution.mergeExecutableGroups, Execution.addExecutableGroup,
          hfalse]
        exact ih (Execution.addExecutableGroup (currentName, currentFields)
          left) hmiddle.2

theorem mergeExecutableGroups_assoc_of_namesNodup
    (left middle right :
      List (Name × List Execution.ExecutableField)) :
    executableGroupNamesNodup middle ->
      executableGroupNamesNodup right ->
        Execution.mergeExecutableGroups
            (Execution.mergeExecutableGroups left middle) right
          =
        Execution.mergeExecutableGroups left
          (Execution.mergeExecutableGroups middle right) := by
  intro hmiddle hright
  induction right generalizing left middle with
  | nil =>
      simp [Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change Execution.mergeExecutableGroups
          (Execution.addExecutableGroup group
            (Execution.mergeExecutableGroups left middle)) rest
        =
        Execution.mergeExecutableGroups left
          (Execution.mergeExecutableGroups
            (Execution.addExecutableGroup group middle) rest)
      rw [addExecutableGroup_mergeExecutableGroups_of_namesNodup group left
        middle hmiddle]
      exact ih left (Execution.addExecutableGroup group middle)
        (addExecutableGroup_namesNodup group middle hmiddle)
        hright.2

theorem mergeExecutableGroups_eq_append_of_namesDisjoint
    (left right : List (Name × List Execution.ExecutableField)) :
    executableGroupNamesDisjoint left right ->
      executableGroupNamesNodup right ->
        Execution.mergeExecutableGroups left right = left ++ right := by
  induction right generalizing left with
  | nil =>
      intro _hdisjoint _hnodup
      simp [Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      intro hdisjoint hnodup
      have hnotinLeft : responseName ∉ left.map Prod.fst := by
        intro hmem
        exact hdisjoint responseName hmem (by simp)
      have hrestNodup : executableGroupNamesNodup rest := hnodup.2
      have hrestDisjoint :
          executableGroupNamesDisjoint (left ++ [(responseName, fields)])
            rest := by
        intro name hleft hright
        have hleftCases :
            name ∈ left.map Prod.fst ∨ name = responseName := by
          simpa using hleft
        cases hleftCases with
        | inl hleftMem =>
            exact hdisjoint name hleftMem (by simp [hright])
        | inr hname =>
            subst name
            exact hnodup.1 hright
      simp [Execution.mergeExecutableGroups,
        addExecutableGroup_of_responseName_not_mem (responseName, fields)
          left hnotinLeft]
      change Execution.mergeExecutableGroups
          (left ++ [(responseName, fields)]) rest
        = left ++ (responseName, fields) :: rest
      rw [ih (left ++ [(responseName, fields)]) hrestDisjoint hrestNodup]
      simp [List.append_assoc]

theorem mergeExecutableGroups_nil_left_of_namesNodup
    (groups : List (Name × List Execution.ExecutableField)) :
    executableGroupNamesNodup groups ->
      Execution.mergeExecutableGroups [] groups = groups := by
  intro hnodup
  simpa using
    mergeExecutableGroups_eq_append_of_namesDisjoint [] groups
      (by
        intro responseName hleft _hright
        cases hleft)
      hnodup

theorem mergeExecutableGroups_namesNodup
    (left right : List (Name × List Execution.ExecutableField)) :
    executableGroupNamesNodup left ->
      executableGroupNamesNodup
        (Execution.mergeExecutableGroups left right) := by
  induction right generalizing left with
  | nil =>
      intro hleft
      exact hleft
  | cons group rest ih =>
      intro hleft
      simp [Execution.mergeExecutableGroups]
      exact ih (Execution.addExecutableGroup group left)
        (addExecutableGroup_namesNodup group left hleft)

theorem collectFields_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value) :
    Execution.collectFields schema variableValues parentType source [] = [] := by
  rfl

theorem collectFields_cons
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selection : Selection) (rest : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (selection :: rest)
      =
    Execution.mergeExecutableGroups
      (Execution.collectSelection schema variableValues parentType source selection)
      (Execution.collectFields schema variableValues parentType source rest) := by
  rfl

theorem collectFields_field_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet rest : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] selectionSet :: rest)
      =
    Execution.mergeExecutableGroups
      [(responseName, [{
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      }])]
      (Execution.collectFields schema variableValues parentType source rest) := by
  simp [collectFields_cons, collectSelection_field_noDirectives]

theorem collectFields_inlineFragment_none_directiveFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (Selection.inlineFragment none [] selectionSet :: rest)
      =
    Execution.mergeExecutableGroups
      (Execution.collectFields schema variableValues parentType source selectionSet)
      (Execution.collectFields schema variableValues parentType source rest) := by
  simp [collectFields_cons, collectSelection_inlineFragment_none_noDirectives]

theorem collectFields_inlineFragment_some_directiveFree_apply
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
      Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues parentType source selectionSet)
        (Execution.collectFields schema variableValues parentType source rest) := by
  intro happly
  simp [collectFields_cons, collectSelection_inlineFragment_some_noDirectives,
    happly]

theorem collectFields_inlineFragment_some_directiveFree_skip
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
      Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.mergeExecutableGroups []
        (Execution.collectFields schema variableValues parentType source rest) := by
  intro hskip
  simp [collectFields_cons, collectSelection_inlineFragment_some_noDirectives,
    hskip]

mutual
  theorem collectSelection_namesNodup
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.Value)
      (selection : Selection) :
      executableGroupNamesNodup
        (Execution.collectSelection schema variableValues parentType source
          selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            Execution.selectionDirectivesAllowBool variableValues directives = true
        · simp [Execution.collectSelection, hallows,
            executableGroupNamesNodup]
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues directives =
                false := by
            cases hmatch :
                Execution.selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hfalse,
            executableGroupNamesNodup]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · simp [Execution.collectSelection, hallows]
              exact collectFields_namesNodup schema variableValues parentType
                source selectionSet
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupNamesNodup]
        | some typeCondition =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · by_cases happly :
                Execution.doesFragmentTypeApplyBool schema parentType source
                  typeCondition = true
              · simp [Execution.collectSelection, hallows, happly]
                exact collectFields_namesNodup schema variableValues parentType
                  source selectionSet
              · have hfalse :
                    Execution.doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      Execution.doesFragmentTypeApplyBool schema parentType
                        source typeCondition
                  · rfl
                  · contradiction
                simp [Execution.collectSelection, hallows, hfalse,
                  executableGroupNamesNodup]
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupNamesNodup]

  theorem collectFields_namesNodup
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.Value)
      (selectionSet : List Selection) :
      executableGroupNamesNodup
        (Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [Execution.collectFields, executableGroupNamesNodup]
    | cons selection rest =>
        simp [Execution.collectFields]
        exact mergeExecutableGroups_namesNodup
          (Execution.collectSelection schema variableValues parentType source
            selection)
          (Execution.collectFields schema variableValues parentType source rest)
          (collectSelection_namesNodup schema variableValues parentType source
            selection)
end

mutual
  theorem collectSelection_wellFormed
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.Value)
      (selection : Selection) :
      executableGroupsWellFormed
        (Execution.collectSelection schema variableValues parentType source
          selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            Execution.selectionDirectivesAllowBool variableValues directives = true
        · simp [Execution.collectSelection, hallows]
          intro group hgroup
          simp at hgroup
          subst group
          exact executableGroupWellFormed_singleton_field {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues directives =
                false := by
            cases hmatch :
                Execution.selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hfalse,
            executableGroupsWellFormed_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · simp [Execution.collectSelection, hallows]
              exact collectFields_wellFormed schema variableValues parentType
                source selectionSet
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupsWellFormed_nil]
        | some typeCondition =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · by_cases happly :
                Execution.doesFragmentTypeApplyBool schema parentType source
                  typeCondition = true
              · simp [Execution.collectSelection, hallows, happly]
                exact collectFields_wellFormed schema variableValues parentType
                  source selectionSet
              · have hfalse :
                    Execution.doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      Execution.doesFragmentTypeApplyBool schema parentType
                        source typeCondition
                  · rfl
                  · contradiction
                simp [Execution.collectSelection, hallows, hfalse,
                  executableGroupsWellFormed_nil]
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupsWellFormed_nil]

  theorem collectFields_wellFormed
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.Value)
      (selectionSet : List Selection) :
      executableGroupsWellFormed
        (Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [Execution.collectFields, executableGroupsWellFormed_nil]
    | cons selection rest =>
        simp [Execution.collectFields]
        exact mergeExecutableGroups_wellFormed
          (Execution.collectSelection schema variableValues parentType source
            selection)
          (Execution.collectFields schema variableValues parentType source rest)
          (collectSelection_wellFormed schema variableValues parentType source
            selection)
          (collectFields_wellFormed schema variableValues parentType source
            rest)
end

theorem collectFields_append
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (left right : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (left ++ right)
      =
    Execution.mergeExecutableGroups
      (Execution.collectFields schema variableValues parentType source left)
      (Execution.collectFields schema variableValues parentType source right) := by
  induction left with
  | nil =>
      simp [Execution.collectFields]
      rw [mergeExecutableGroups_nil_left_of_namesNodup
        (Execution.collectFields schema variableValues parentType source right)
        (collectFields_namesNodup schema variableValues parentType source
          right)]
  | cons selection rest ih =>
      simp [Execution.collectFields, ih]
      rw [mergeExecutableGroups_assoc_of_namesNodup]
      · exact collectFields_namesNodup schema variableValues parentType source
          rest
      · exact collectFields_namesNodup schema variableValues parentType source
          right

theorem collectFields_inlineFragment_none_directiveFree_flatten
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.collectFields schema variableValues parentType source
      (Selection.inlineFragment none [] selectionSet :: rest)
      =
    Execution.collectFields schema variableValues parentType source
      (selectionSet ++ rest) := by
  rw [collectFields_inlineFragment_none_directiveFree]
  rw [collectFields_append]

theorem collectFields_inlineFragment_some_directiveFree_apply_flatten
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition =
      true ->
      Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.collectFields schema variableValues parentType source
        (selectionSet ++ rest) := by
  intro happly
  rw [collectFields_inlineFragment_some_directiveFree_apply]
  · rw [collectFields_append]
  · exact happly

theorem mergeExecutableGroups_nil_left_collectFields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selectionSet : List Selection) :
    executableGroupNamesNodup
      (Execution.mergeExecutableGroups []
        (Execution.collectFields schema variableValues parentType source
          selectionSet)) := by
  exact mergeExecutableGroups_namesNodup []
    (Execution.collectFields schema variableValues parentType source selectionSet)
    (by simp [executableGroupNamesNodup])

theorem mergeExecutableGroups_nil_left_collectFields_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selectionSet : List Selection) :
    Execution.mergeExecutableGroups []
      (Execution.collectFields schema variableValues parentType source
        selectionSet)
      =
    Execution.collectFields schema variableValues parentType source
      selectionSet := by
  exact mergeExecutableGroups_nil_left_of_namesNodup
    (Execution.collectFields schema variableValues parentType source selectionSet)
    (collectFields_namesNodup schema variableValues parentType source
      selectionSet)

theorem collectFields_inlineFragment_some_directiveFree_skip_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
      Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.collectFields schema variableValues parentType source rest := by
  intro hskip
  rw [collectFields_inlineFragment_some_directiveFree_skip schema
    variableValues parentType typeCondition source selectionSet rest hskip]
  exact mergeExecutableGroups_nil_left_collectFields_eq schema variableValues
    parentType source rest

end GroundTypeNormalization

end NormalForm

end GraphQL
