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

end GroundTypeNormalization

end NormalForm

end GraphQL
