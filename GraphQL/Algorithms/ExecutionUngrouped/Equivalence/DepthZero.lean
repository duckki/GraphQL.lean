import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Absorption

/-!
Depth-zero facts for ungrouped execution.

At zero completion depth, field visits do not write sentinel `null` values into the
response object. They preserve the current output and only contribute an execution
error count. The proofs in this file therefore reduce depth-zero behavior to counting
the executable field occurrences that `CollectFields` exposes.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def depthZeroVisitStatus : Nat -> VisitStatus
  | 0 => visitOk
  | n + 1 => .error (n + 1)

theorem combineVisitStatus_depthZeroVisitStatus
    (left right : Nat) :
    combineVisitStatus (depthZeroVisitStatus left)
      (depthZeroVisitStatus right) =
    depthZeroVisitStatus (left + right) := by
  cases left <;> cases right <;>
    simp [depthZeroVisitStatus, visitOk, combineVisitStatus,
      GraphQL.Execution.Result.combine,
      Nat.add_comm, Nat.add_left_comm]

theorem collectedExecutableFields_length_eq_groups_length_of_singletons :
    ∀ groups : List (Name × List ExecutableField),
      (∀ responseName fields,
        (responseName, fields) ∈ groups -> fields.length = 1) ->
      (collectedExecutableFields groups).length = groups.length
  | [], _hsingletons => by
      simp [collectedExecutableFields]
  | (responseName, fields) :: rest, hsingletons => by
      have hfields : fields.length = 1 :=
        hsingletons responseName fields (by simp)
      have hrest :
          (collectedExecutableFields rest).length = rest.length :=
        collectedExecutableFields_length_eq_groups_length_of_singletons rest
          (by
            intro restResponseName restFields hmem
            exact hsingletons restResponseName restFields (by simp [hmem]))
      simp [collectedExecutableFields, List.length_append, hfields, hrest]
      omega

theorem executeCollectedFields_depth_zero_equivalence
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (source : ResolverValue ObjectIdentity) :
    ∀ groups,
      GraphQL.Execution.executeCollectedFieldsData schema resolvers variableValues
        0 source groups = []
  | [] => by
      simp [GraphQL.Execution.executeCollectedFieldsData,
        GraphQL.Execution.executeCollectedFields,
        GraphQL.Execution.Result.getD]
  | (_responseName, fields) :: rest => by
      cases fields with
      | nil =>
          have hrest :=
            executeCollectedFields_depth_zero_equivalence schema resolvers
              variableValues source rest
          cases hresult :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 source rest with
          | error errors =>
                simp [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, hresult]
          | ok result =>
              rcases result with ⟨fields, errors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hresult] at hrest ⊢
      | cons _head _tail =>
          cases hresult :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 source rest with
          | error errors =>
                simp [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, GraphQL.Execution.outOfFuel,
                  hresult]
          | ok result =>
              rcases result with ⟨fields, errors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, GraphQL.Execution.outOfFuel,
                hresult]

theorem executeCollectedFields_depth_zero_nonempty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (source : ResolverValue ObjectIdentity) :
    ∀ groups,
      CollectedGroupsFieldsNonempty groups ->
        GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          0 source groups =
        match groups with
        | [] => .ok ([], 0)
        | _group :: _rest => .error groups.length
  | [], _hnonempty => by
      simp [GraphQL.Execution.executeCollectedFields]
  | (_responseName, fields) :: rest, hnonempty => by
      have hfields : fields ≠ [] :=
        hnonempty _responseName fields (by simp)
      have hrest :=
        executeCollectedFields_depth_zero_nonempty schema resolvers
          variableValues source rest
          (CollectedGroupsFieldsNonempty_tail hnonempty)
      cases fields with
      | nil =>
          exact False.elim (hfields rfl)
      | cons _field _tail =>
          cases rest with
          | nil =>
                simp [GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine, GraphQL.Execution.outOfFuel]
          | cons _next _more =>
              simp [GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine, GraphQL.Execution.outOfFuel]
                at hrest ⊢
              rw [hrest]
              simp [Nat.add_comm, Nat.add_left_comm]

mutual
  theorem visitSelection_depth_zero_count
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity) :
      ∀ (selection : Selection) (output : ResponseValue),
        visitSelection schema resolvers variableValues 0 parentType source
          selection output =
        (output,
          depthZeroVisitStatus
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection)).length)
    := by
      intro selection output
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hdirectives :
              selectionDirectivesAllowBool variableValues directives <;>
              simp [visitSelection, GraphQL.Execution.collectSelection,
                hdirectives, depthZeroVisitStatus, collectedExecutableFields,
                visitOk, outOfFuel]
      | inlineFragment typeCondition directives selectionSet =>
          cases hdirectives :
              selectionDirectivesAllowBool variableValues directives
          · cases typeCondition <;>
              simp [visitSelection, GraphQL.Execution.collectSelection,
                hdirectives, collectedExecutableFields, depthZeroVisitStatus,
                visitOk]
          · cases typeCondition with
            | none =>
                simpa [visitSelection, GraphQL.Execution.collectSelection,
                  hdirectives] using
                  visitSubfields_depth_zero_count schema resolvers variableValues
                    parentType source selectionSet output
            | some typeCondition =>
                cases happly :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition
                · simp [visitSelection, GraphQL.Execution.collectSelection,
                    hdirectives, happly, collectedExecutableFields,
                    depthZeroVisitStatus, visitOk]
                · simpa [visitSelection, GraphQL.Execution.collectSelection,
                    hdirectives, happly] using
                    visitSubfields_depth_zero_count schema resolvers
                      variableValues parentType source selectionSet output

  theorem visitSubfields_depth_zero_count
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity) :
      ∀ (selectionSet : List Selection) (output : ResponseValue),
        visitSubfields schema resolvers variableValues 0 parentType source
          selectionSet output =
        (output,
          depthZeroVisitStatus
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                parentType source selectionSet)).length)
    := by
      intro selectionSet output
      cases selectionSet with
      | nil =>
          simp [visitSubfields, GraphQL.Execution.collectFields,
            collectedExecutableFields, depthZeroVisitStatus, visitOk]
      | cons selection rest =>
          have hhead :=
            visitSelection_depth_zero_count schema resolvers variableValues
              parentType source selection output
          have htail :=
            visitSubfields_depth_zero_count schema resolvers variableValues
              parentType source rest output
          simp [visitSubfields, GraphQL.Execution.collectFields, hhead, htail,
            collectedExecutableFields_mergeExecutableGroups_length,
            combineVisitStatus_depthZeroVisitStatus, Nat.add_comm]
end

theorem visitSubfields_executableFieldSelections_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)) :
    visitSubfields schema resolvers variableValues 0 parentType source
      (executableFieldSelections fields) (.object outputFields) =
    (.object outputFields, depthZeroVisitStatus fields.length) := by
  have hcount :=
    visitSubfields_depth_zero_count schema resolvers variableValues parentType
      source (executableFieldSelections fields) (.object outputFields)
  simpa [collectedExecutableFields_collectFields_executableFieldSelections_length]
    using hcount

theorem VisitSubfieldsFlatCollects_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (outputFields : List (Name × ResponseValue)) :
      VisitSubfieldsFlatCollects schema resolvers variableValues 0 parentType
        source selectionSet (.object outputFields) := by
  unfold VisitSubfieldsFlatCollects
  let fields :=
    collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
  have hleft :=
    visitSubfields_depth_zero_count schema resolvers variableValues parentType
      source selectionSet (.object outputFields)
  have hright :=
    visitSubfields_executableFieldSelections_depth_zero schema resolvers
      variableValues parentType source fields outputFields
  rw [hleft, hright]

theorem ExecutableGroupsFlatSpecEquivalent_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnodup : PairKeysNodup groups)
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hsingletons :
      ∀ responseName fields,
        (responseName, fields) ∈ groups -> fields.length = 1) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues 0
      parentType source groups := by
  unfold ExecutableGroupsFlatSpecEquivalent
  unfold ExecutableFieldsFlatSpecEquivalent
  have hvisit :=
    visitSubfields_executableFieldSelections_depth_zero schema resolvers
      variableValues parentType source (collectedExecutableFields groups) []
  have hspec :=
    specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
      schema resolvers variableValues 0 parentType source groups hnodup
      hnonempty hresponses hparents
  have hcollected :=
    executeCollectedFields_depth_zero_nonempty schema resolvers variableValues
      source groups hnonempty
  have hlength :
      (collectedExecutableFields groups).length = groups.length :=
    collectedExecutableFields_length_eq_groups_length_of_singletons groups
      hsingletons
  unfold executeRootSelectionSet
  rw [hvisit]
  rw [hspec]
  rw [hcollected]
  rw [hlength]
  cases groups <;> simp [depthZeroVisitStatus, visitOk]

theorem executeQueryAtDepth_data_eq_spec_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity) :
    (executeQueryAtDepth schema resolvers variableValues operation 0 source).data =
      (GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
        operation 0 source).data := by
  unfold executeQueryAtDepth GraphQL.Execution.executeQueryAtDepth
  by_cases hsource :
      rootSourceAppliesBool schema operation source = true
  · simp [hsource]
    have hvisit :
        visitSubfields schema resolvers variableValues 0 operation.rootType
            source operation.selectionSet (.object []) =
          (.object [],
            depthZeroVisitStatus
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  operation.rootType source operation.selectionSet)).length) := by
      simpa using
        visitSubfields_depth_zero_count schema resolvers variableValues
          operation.rootType source operation.selectionSet (.object [])
    unfold executeRootSelectionSet GraphQL.Execution.executeRootSelectionSet
    rw [hvisit]
    cases hgroups :
        GraphQL.Execution.collectFields schema variableValues operation.rootType
          source operation.selectionSet with
    | nil =>
        have hspec :
            GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 source [] =
              .ok ([], 0) := by
          simp [GraphQL.Execution.executeCollectedFields]
        simp [hgroups, hspec, collectedExecutableFields, depthZeroVisitStatus,
          visitOk]
    | cons group rest =>
        rcases group with ⟨responseName, fields⟩
        have hnonempty :
            CollectedGroupsFieldsNonempty ((responseName, fields) :: rest) := by
          simpa [hgroups] using
            collectFields_fieldsNonempty schema variableValues operation.rootType
              source operation.selectionSet
        have hspec :
            GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 source ((responseName, fields) :: rest) =
              .error (((responseName, fields) :: rest).length) := by
          simpa using
            executeCollectedFields_depth_zero_nonempty schema resolvers
              variableValues source ((responseName, fields) :: rest)
              hnonempty
        have hfields : fields ≠ [] := hnonempty responseName fields (by simp)
        cases fields with
        | nil =>
            exact False.elim (hfields rfl)
        | cons _field _fields =>
            simp [hgroups, hspec, collectedExecutableFields,
              depthZeroVisitStatus]
  · simp [hsource]

end ExecutionUngrouped
end Algorithms

end GraphQL
