import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList

/-!
Group-list proof helpers that carry final merged-complete evidence per group.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

structure ExecutedFieldGroupComplete
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
  mergedComplete :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields resolved

namespace ExecutedFieldGroupComplete

theorem mergedComplete_resolved
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroupComplete schema resolvers variableValues depth
        parentType source responseName field fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source) := by
  rw [group.resolved_eq]
  exact group.mergedComplete

def of_containedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hinvariant :
      CollectedFieldGroupContainedAppendInvariant schema resolvers
        variableValues depth source groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups) :
    ExecutedFieldGroupComplete schema resolvers variableValues depth parentType
      source responseName field fields where
  resolved :=
    resolvers.resolve field.parentType field.fieldName field.arguments source
  responseName_eq := hresponses responseName (field :: fields) hgroup
  parent_eq := hparents responseName (field :: fields) hgroup
  resolved_eq := rfl
  mergedComplete := by
    have hfieldResponse :
        field.responseName = responseName :=
      hresponses responseName (field :: fields) hgroup field (by simp)
    have hfieldParent :
        field.parentType = parentType :=
      hparents responseName (field :: fields) hgroup field (by simp)
    apply ExecutableFieldsMergedComplete_of_contained_appendSteps schema
      resolvers variableValues depth parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl
    · intro childDepth runtimeType identity hlt hcontains hincludes
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        hinvariant.prefixChildren responseName field fields [] hgroup
          (by intro candidate hmem; simp at hmem)
          childDepth runtimeType identity hlt hcontains hincludes
    · exact
        ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant
          hinvariant hresponses hparents hcompatible hstable responseName field
          fields hgroup

end ExecutedFieldGroupComplete

def ExecutedFieldGroupsComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    List (Name × List ExecutableField) -> Type
  | [] => Unit
  | (_responseName, []) :: _rest => Empty
  | (responseName, field :: fields) :: rest =>
      ExecutedFieldGroupComplete schema resolvers variableValues depth
        parentType source responseName field fields ×
      ExecutedFieldGroupsComplete schema resolvers variableValues depth
        parentType source rest

namespace ExecutedFieldGroupsComplete

theorem no_empty_head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {responseName : Name} {rest : List (Name × List ExecutableField)} :
    ExecutedFieldGroupsComplete schema resolvers variableValues depth
      parentType source ((responseName, []) :: rest) ->
    False := by
  intro hgroups
  exact nomatch hgroups

theorem fieldsNonempty
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity} :
    ∀ {groups : List (Name × List ExecutableField)},
      ExecutedFieldGroupsComplete schema resolvers variableValues depth
        parentType source groups ->
      CollectedGroupsFieldsNonempty groups
  | [], _hgroups => CollectedGroupsFieldsNonempty_nil
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (no_empty_head hgroups)
  | (groupResponseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        subst candidateFields
        simp
      · exact fieldsNonempty hgroups.2 candidateResponseName candidateFields
          htail

theorem responseName
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity} :
    ∀ {groups : List (Name × List ExecutableField)},
      ExecutedFieldGroupsComplete schema resolvers variableValues depth
        parentType source groups ->
      CollectedGroupsResponseName groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (no_empty_head hgroups)
  | (groupResponseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem candidate hcandidate
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponseName, hfields⟩
        subst candidateResponseName
        subst candidateFields
        exact hgroups.1.responseName_eq candidate hcandidate
      · exact responseName hgroups.2 candidateResponseName candidateFields
          htail candidate hcandidate

theorem parent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity} :
    ∀ {groups : List (Name × List ExecutableField)},
      ExecutedFieldGroupsComplete schema resolvers variableValues depth
        parentType source groups ->
      CollectedGroupsParent parentType groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (responseName, []) :: rest, hgroups =>
      False.elim (no_empty_head hgroups)
  | (responseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem candidate hcandidate
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        subst candidateFields
        exact hgroups.1.parent_eq candidate hcandidate
      · exact parent hgroups.2 candidateResponseName candidateFields htail
          candidate hcandidate

theorem visitSubfields_executableFieldSelections_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    ∀ (groups : List (Name × List ExecutableField)),
      ExecutedFieldGroupsComplete schema resolvers variableValues depth
        parentType source groups ->
      PairKeysNodup groups ->
      CollectedGroupsResponseName groups ->
      visitSubfields schema resolvers variableValues (depth + 1) parentType
        source
        (executableFieldSelections (collectedExecutableFields groups))
        (.object []) =
      .object
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues (depth + 1) source groups)
  | [], _hgroups, _hnodup, _hresponses => by
      simp [collectedExecutableFields, executableFieldSelections,
        visitSubfields, GraphQL.Execution.executeCollectedFields]
  | (responseName, []) :: rest, hgroups, _hnodup, _hresponses => by
      exact False.elim (no_empty_head hgroups)
  | (responseName, field :: fields) :: rest, hgroups, hnodup, hresponses => by
      rcases hgroups with ⟨headGroup, restGroups⟩
      have hrestNodup : PairKeysNodup rest :=
        PairKeysNodup.tail hnodup
      have hrestResponses : CollectedGroupsResponseName rest :=
        CollectedGroupsResponseName_tail hresponses
      have hrestVisit :=
        visitSubfields_executableFieldSelections_eq_spec schema resolvers
          variableValues depth parentType source rest restGroups hrestNodup
          hrestResponses
      let headResponse : Response :=
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
      have hheadVisit :
          visitSubfields schema resolvers variableValues (depth + 1)
            parentType source (executableFieldSelections (field :: fields))
            (.object []) =
          .object [(responseName, headResponse)] := by
        simpa [headResponse] using
          visitSubfields_executableFieldSelections_group_fresh_appends_of_mergedComplete
            schema resolvers variableValues depth parentType source responseName
            field fields
            (resolvers.resolve field.parentType field.fieldName field.arguments
              source)
            [] headGroup.responseName_eq (by simp)
            headGroup.mergedComplete_resolved
      have hfreshRest :
          ∀ candidate, candidate ∈ collectedExecutableFields rest ->
            candidate.responseName ∉ [(responseName, headResponse)].map
              Prod.fst := by
        intro candidate hmem hprefix
        have hcandidateName :
            candidate.responseName ∈ rest.map Prod.fst :=
          collectedExecutableFields_responseName_mem rest hrestResponses
            candidate hmem
        have hcandidateEq : candidate.responseName = responseName := by
          simpa using hprefix
        have hheadFresh : responseName ∉ rest.map Prod.fst :=
          PairKeysNodup.head_not_mem_tail hnodup
        exact hheadFresh (by simpa [hcandidateEq] using hcandidateName)
      have hrestPrefix :
          visitSubfields schema resolvers variableValues (depth + 1)
            parentType source
            (executableFieldSelections (collectedExecutableFields rest))
            (.object ([(responseName, headResponse)] ++ [])) =
          .object
            ([(responseName, headResponse)] ++
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues (depth + 1) source rest) :=
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues (depth + 1) parentType source
          (collectedExecutableFields rest) [(responseName, headResponse)] []
          (GraphQL.Execution.executeCollectedFields schema resolvers
            variableValues (depth + 1) source rest)
          hfreshRest hrestVisit
      rw [show
          executableFieldSelections
              (collectedExecutableFields
                ((responseName, field :: fields) :: rest)) =
            executableFieldSelections (field :: fields) ++
              executableFieldSelections (collectedExecutableFields rest) by
        simp [collectedExecutableFields, executableFieldSelections]]
      rw [visitSubfields_append_equivalence schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields))
        (executableFieldSelections (collectedExecutableFields rest))
        (.object [])]
      rw [hheadVisit]
      simpa [headResponse, GraphQL.Execution.executeCollectedFields,
        GraphQL.Execution.executeField, headGroup.resolved_eq,
        GraphQL.NormalForm.completeValue_eq_mergedFieldSelectionSet] using
        hrestPrefix

def of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant :
      CollectedFieldGroupContainedAppendInvariant schema resolvers
        variableValues depth source groups) :
    ExecutedFieldGroupsComplete schema resolvers variableValues depth parentType
      source groups :=
  match groups with
  | [] => ()
  | (responseName, []) :: _rest =>
      False.elim (hnonempty responseName [] (by simp) rfl)
  | (responseName, field :: fields) :: rest =>
      let tailInvariant :
          CollectedFieldGroupContainedAppendInvariant schema resolvers
            variableValues depth source rest :=
        { prefixChildren := by
            intro tailResponseName tailField tailFields prefixTail hgroup
              hprefix childDepth runtimeType identity hlt hcontains hincludes
            exact hinvariant.prefixChildren tailResponseName tailField
              tailFields prefixTail (by simp [hgroup]) hprefix childDepth
              runtimeType identity hlt hcontains hincludes
          absorbs := by
            intro tailResponseName tailField tailFields prefixTail later hgroup
              hprefix hlater childDepth runtimeType identity hlt hcontains
            exact hinvariant.absorbs tailResponseName tailField tailFields
              prefixTail later (by simp [hgroup]) hprefix hlater childDepth
              runtimeType identity hlt hcontains
          extendedChildren := by
            intro tailResponseName tailField tailFields prefixTail later hgroup
              hprefix hlater childDepth runtimeType identity hlt hcontains
              hincludes
            exact hinvariant.extendedChildren tailResponseName tailField
              tailFields prefixTail later (by simp [hgroup]) hprefix hlater
              childDepth runtimeType identity hlt hcontains hincludes }
      ⟨ExecutedFieldGroupComplete.of_containedAppendInvariant hinvariant
          hresponses hparents hcompatible hstable responseName field fields
          (by simp),
        of_collected_groups_containedAppendInvariant schema resolvers
          variableValues depth parentType source rest
          (CollectedGroupsFieldsNonempty_tail hnonempty)
          (CollectedGroupsResponseName_tail hresponses)
          (CollectedGroupsParent_tail hparents)
          (CollectedGroupsFieldValidationMergeCompatible_tail hcompatible)
          (CollectedGroupsResolveStable.tail resolvers source
            (responseName, field :: fields) rest hstable)
          tailInvariant⟩

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hgroups :
      ExecutedFieldGroupsComplete schema resolvers variableValues depth
        parentType source groups)
    (hnodup : PairKeysNodup groups) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source groups := by
  unfold ExecutableGroupsFlatSpecEquivalent
  unfold ExecutableFieldsFlatSpecEquivalent
  unfold executeRootSelectionSet
  rw [visitSubfields_executableFieldSelections_eq_spec schema resolvers
    variableValues depth parentType source groups hgroups hnodup
    (responseName hgroups)]
  unfold GraphQL.Execution.executeRootSelectionSet
  change
    GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source groups =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (collectedExecutableFields groups)))
  rw [collectFields_executableFieldSelections_collectedExecutableFields schema
    variableValues parentType source groups hnodup
    (fieldsNonempty hgroups) (responseName hgroups) (parent hgroups)]

end ExecutedFieldGroupsComplete

theorem executeRootSelectionSet_eq_spec_of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hflat :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hcollected :
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
    (happend :
      CollectedFieldGroupContainedAppendInvariant schema resolvers
        variableValues depth source groups) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
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
  have hnonempty : CollectedGroupsFieldsNonempty groups := by
    rw [← hcollect]
    exact collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
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
        hcollected hcollect
  have hnodup : PairKeysNodup groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.pairKeysNodup_of_collect_eq state
        groups hcollected hcollect
  apply executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
    schema resolvers variableValues (depth + 1) parentType source selectionSet
    hflat
  rw [hcollect]
  exact
    ExecutedFieldGroupsComplete.groupFlatSpecEquivalent
      (ExecutedFieldGroupsComplete.of_collected_groups_containedAppendInvariant
        schema resolvers variableValues depth parentType source groups
        hnonempty hresponses hparents hcompatible hstable happend)
      hnodup

theorem executeQueryAtDepth_eq_spec_of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : Value ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hflat :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hcollected :
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
    (happend :
      CollectedFieldGroupContainedAppendInvariant schema resolvers
        variableValues depth source groups) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_collected_groups_containedAppendInvariant
      hcollect hflat hcollected hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : Value ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hflat :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hcollected :
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
    (happend :
      CollectedFieldGroupContainedAppendInvariant schema resolvers
        variableValues depth source groups) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_groups_containedAppendInvariant
      hroot hcollect hflat hcollected hcompatible happend

end ExecutionUngrouped
end Algorithms

end GraphQL
