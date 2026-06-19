import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList

/-!
Final proof-boundary statements for ungrouped execution equivalence.

The main public bridge derives spec equivalence from the collected-field invariants
and a proof that each collected group can append its duplicate-field slices.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

structure ExecutedGroupedSelectionSetState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) : Type where
  groups : List (Name × List ExecutableField)
  collect_eq :
    GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet = groups
  flatCollects :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source selectionSet (.object [])
  flatSpec :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
      parentType source groups

namespace ExecutedGroupedSelectionSetState

theorem visitSubfields_eq_spec_of_executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (hroot :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source selectionSet) :
    visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object [])
      =
    .object
      (GraphQL.Execution.executeSelectionSet schema resolvers variableValues
        depth parentType source selectionSet) := by
  rw [visitSubfields_empty_eq_executeRootSelectionSet_object]
  simpa [GraphQL.Execution.executeSelectionSet] using
    congrArg Response.object hroot

theorem executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet := by
  apply executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
    schema resolvers variableValues depth parentType source selectionSet
    state.flatCollects
  rw [state.collect_eq]
  exact state.flatSpec

theorem visitSubfields_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet) :
    visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object [])
      =
    .object
      (GraphQL.Execution.executeSelectionSet schema resolvers variableValues
        depth parentType source selectionSet) :=
  visitSubfields_eq_spec_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source selectionSet
    state.executeRootSelectionSet_eq_spec

theorem stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source selectionSet
    state.executeRootSelectionSet_eq_spec

def depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues 0
      parentType source selectionSet :=
  { groups :=
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet
    collect_eq := rfl
    flatCollects :=
      VisitSubfieldsFlatCollects_depth_zero schema resolvers variableValues
        parentType source selectionSet (.object [])
    flatSpec :=
      ExecutableGroupsFlatSpecEquivalent_depth_zero schema resolvers
        variableValues parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) }

def of_empty_collect
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [])
    (hflat :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source selectionSet (.object [])) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues depth
      parentType source selectionSet :=
  { groups := []
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec :=
      ExecutableGroupsFlatSpecEquivalent_nil schema resolvers variableValues
        depth parentType source }

def of_group_flat_spec
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
      VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source selectionSet (.object []))
    (hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source groups) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues depth
      parentType source selectionSet :=
  { groups := groups
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec := hgroups }

def of_executedGroups
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
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source groups)
    (hnodup : PairKeysNodup groups) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  { groups := groups
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec := ExecutedFieldGroups.groupFlatSpecEquivalent hgroups hnodup }

def of_collected_groups_state
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
    (hplanStates :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ExecutedFieldAppendPlanState schema resolvers variableValues depth
            field fields [] fields) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
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
        hinvariant hcollect
  have hnodup : PairKeysNodup groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.pairKeysNodup_of_collect_eq state
        groups hinvariant hcollect
  exact
    of_executedGroups hcollect hflat
      (ExecutedFieldGroups.of_collected_groups_state schema resolvers
        variableValues depth parentType source groups hnonempty hresponses
        hparents hcompatible hstable hplanStates)
      hnodup

def of_collected_groups_appendInvariant
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
      FieldGroupAppendInvariant schema resolvers variableValues depth) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  of_collected_groups_state hcollect hflat hcollected hcompatible
    (by
      intro _responseName field fields _hmem
      exact ExecutedFieldAppendPlanState.of_appendInvariant happend field
        fields)

def of_collected_groups_collectedAppendInvariant
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
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  of_collected_groups_state hcollect hflat hcollected hcompatible
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedAppendInvariant happend
          responseName field fields hgroup)

def of_collected_groups_collectedLocalAppendInvariant
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
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  of_collected_groups_state hcollect hflat hcollected hcompatible
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant happend
          responseName field fields hgroup)

end ExecutedGroupedSelectionSetState

structure CollectedFieldGroupRecursiveAppendState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (groups : List (Name × List ExecutableField)) : Type where
  prefixChildren :
    ∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutedGroupedSelectionSetState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))

namespace CollectedFieldGroupRecursiveAppendState

def depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (groups : List (Name × List ExecutableField)) :
    CollectedFieldGroupRecursiveAppendState schema resolvers variableValues 0
      groups :=
  { prefixChildren := by
      intro _responseName _field _fields _prefixTail _hgroup _hprefix
        childDepth _runtimeType _identity hlt _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt) }

def localAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (state :
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
      depth groups :=
  { prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt hincludes
      exact
        (state.prefixChildren responseName field fields prefixTail hgroup
          hprefix childDepth runtimeType identity hlt
          hincludes).stateEquivalent }

end CollectedFieldGroupRecursiveAppendState

def ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
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
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  ExecutedGroupedSelectionSetState.of_collected_groups_collectedLocalAppendInvariant
    hcollect hflat hcollected hcompatible happend.localAppendInvariant

structure RecursiveGroupedSelectionSetState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) : Type where
  groups : List (Name × List ExecutableField)
  collect_eq :
    GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet = groups
  flatCollects :
    VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
      parentType source selectionSet (.object [])
  collected :
    ExecutionCollectedFieldInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] }
  compatible : CollectedGroupsFieldValidationMergeCompatible groups
  recursiveAppend :
    CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
      depth groups

namespace RecursiveGroupedSelectionSetState

def of_root_equivalences
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (horiginal :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source selectionSet)
    (hflat :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))))
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
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    RecursiveGroupedSelectionSetState schema resolvers variableValues depth
      parentType source selectionSet :=
  { groups := groups
    collect_eq := hcollect
    flatCollects :=
      VisitSubfieldsFlatCollects.of_root_equivalences schema resolvers
        variableValues (depth + 1) parentType source selectionSet horiginal
        hflat
    collected := hcollected
    compatible := hcompatible
    recursiveAppend := happend }

def of_allOutputs
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
      VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues
        (depth + 1) parentType source selectionSet)
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
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    RecursiveGroupedSelectionSetState schema resolvers variableValues depth
      parentType source selectionSet :=
  { groups := groups
    collect_eq := hcollect
    flatCollects := hflat (.object [])
    collected := hcollected
    compatible := hcompatible
    recursiveAppend := happend }

def toExecutedGroupedSelectionSetState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutedGroupedSelectionSetState schema resolvers variableValues (depth + 1)
      parentType source selectionSet :=
  ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
    state.collect_eq state.flatCollects state.collected state.compatible
    state.recursiveAppend

theorem executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  state.toExecutedGroupedSelectionSetState.executeRootSelectionSet_eq_spec

theorem visitSubfields_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet) :
    visitSubfields schema resolvers variableValues (depth + 1) parentType
        source selectionSet (.object [])
      =
    .object
      (GraphQL.Execution.executeSelectionSet schema resolvers variableValues
        (depth + 1) parentType source selectionSet) :=
  state.toExecutedGroupedSelectionSetState.visitSubfields_eq_spec

theorem stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      RecursiveGroupedSelectionSetState schema resolvers variableValues depth
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
        initial := .object [] } :=
  state.toExecutedGroupedSelectionSetState.stateEquivalent

end RecursiveGroupedSelectionSetState

namespace CollectedFieldGroupRecursiveAppendState

def of_positiveRecursiveChildren
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hchildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈ groups ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childDepth runtimeType identity,
          childDepth + 1 < depth ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            runtimeType = true ->
          RecursiveGroupedSelectionSetState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))) :
    CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
      depth groups :=
  { prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt hincludes
      cases childDepth with
      | zero =>
          exact
            ExecutedGroupedSelectionSetState.depth_zero schema resolvers
              variableValues runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
      | succ childDepth =>
          exact
            (hchildren responseName field fields prefixTail hgroup hprefix
              childDepth runtimeType identity hlt
              hincludes).toExecutedGroupedSelectionSetState }

end CollectedFieldGroupRecursiveAppendState

theorem executeRootSelectionSet_eq_spec_of_executedGroups
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
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source groups)
    (hnodup : PairKeysNodup groups) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_executedGroups hcollect hflat hgroups
    hnodup).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_state_of_invariant
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
    (hplanStates :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ExecutedFieldAppendPlanState schema resolvers variableValues depth
            field fields [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_state hcollect hflat
    hinvariant hcompatible hplanStates).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_appendInvariant
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
      FieldGroupAppendInvariant schema resolvers variableValues depth) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_appendInvariant
    hcollect hflat hcollected hcompatible happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_collectedAppendInvariant
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
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_collectedAppendInvariant
    hcollect hflat hcollected hcompatible happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_collectedLocalAppendInvariant
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
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_collectedLocalAppendInvariant
    hcollect hflat hcollected hcompatible happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_recursiveAppendState
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
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
    hcollect hflat hcollected hcompatible happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_child_state
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
    (hchildren :
      ∀ childDepth runtimeType identity childSelectionSet,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := childSelectionSet }
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_groups_collectedLocalAppendInvariant
    hcollect hflat hcollected hcompatible
    (CollectedFieldGroupLocalAppendInvariant.of_child_state hchildren)

theorem executeRootSelectionSet_eq_spec_of_collected_groups_depth_one
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hflat :
      VisitSubfieldsFlatCollects schema resolvers variableValues 1 parentType
        source selectionSet (.object []))
    (hcollected :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := 0
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups) :
    executeRootSelectionSet schema resolvers variableValues 1 parentType source
      selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues 1
      parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_groups_collectedAppendInvariant
    hcollect hflat hcollected hcompatible
    (CollectedFieldGroupAppendInvariant.depth_zero schema resolvers
      variableValues groups)

structure ExecutedGroupedOperationState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity) : Type where
  root :
    rootSourceAppliesBool schema operation source = true
  selectionSet :
    ExecutedGroupedSelectionSetState schema resolvers variableValues depth
      operation.rootType source operation.selectionSet

namespace ExecutedGroupedOperationState

theorem executeQueryAtDepth_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : Value ObjectIdentity}
    (state :
      ExecutedGroupedOperationState schema resolvers variableValues operation
        depth source) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source state.root
  exact state.selectionSet.executeRootSelectionSet_eq_spec

theorem executeQuery_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {source : Value ObjectIdentity}
    (state :
      ExecutedGroupedOperationState schema resolvers variableValues operation
        (GraphQL.Execution.executeQueryDepthBound operation) source) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact state.executeQueryAtDepth_eq_spec

end ExecutedGroupedOperationState

def ExecutedGroupedOperationState.of_executedGroups
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
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth
        operation.rootType source groups)
    (hnodup : PairKeysNodup groups) :
    ExecutedGroupedOperationState schema resolvers variableValues operation
      (depth + 1) source :=
  { root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_executedGroups hcollect hflat
        hgroups hnodup }

def ExecutedGroupedOperationState.of_collected_groups_state
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
    (hplanStates :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ExecutedFieldAppendPlanState schema resolvers variableValues depth
            field fields [] fields) :
    ExecutedGroupedOperationState schema resolvers variableValues operation
      (depth + 1) source :=
  { root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_state hcollect
        hflat hinvariant hcompatible hplanStates }

def ExecutedGroupedOperationState.of_collected_groups_appendInvariant
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
      FieldGroupAppendInvariant schema resolvers variableValues depth) :
    ExecutedGroupedOperationState schema resolvers variableValues operation
      (depth + 1) source :=
  { root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_appendInvariant
        hcollect hflat hcollected hcompatible happend }

def ExecutedGroupedOperationState.of_collected_groups_collectedAppendInvariant
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
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups) :
    ExecutedGroupedOperationState schema resolvers variableValues operation
      (depth + 1) source :=
  { root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_collectedAppendInvariant
        hcollect hflat hcollected hcompatible happend }

def ExecutedGroupedOperationState.of_collected_groups_collectedLocalAppendInvariant
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
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups) :
    ExecutedGroupedOperationState schema resolvers variableValues operation
      (depth + 1) source :=
  { root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_collectedLocalAppendInvariant
        hcollect hflat hcollected hcompatible happend }

def ExecutedGroupedOperationState.of_collected_groups_recursiveAppendState
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
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    ExecutedGroupedOperationState schema resolvers variableValues operation
      (depth + 1) source :=
  { root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
        hcollect hflat hcollected hcompatible happend }

theorem executeQueryAtDepth_eq_spec_of_executedGroups
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
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth
        operation.rootType source groups)
    (hnodup : PairKeysNodup groups) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_executedGroups hroot hcollect hflat hgroups
    hnodup).executeQueryAtDepth_eq_spec

theorem executeQueryAtDepth_eq_spec_of_collected_groups_state_of_invariant
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
    (hplanStates :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ExecutedFieldAppendPlanState schema resolvers variableValues depth
            field fields [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_state hroot hcollect
    hflat hinvariant hcompatible hplanStates).executeQueryAtDepth_eq_spec

theorem executeQueryAtDepth_eq_spec_of_collected_groups_appendInvariant
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
      FieldGroupAppendInvariant schema resolvers variableValues depth) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_appendInvariant hroot
    hcollect hflat hcollected hcompatible happend).executeQueryAtDepth_eq_spec

theorem executeQueryAtDepth_eq_spec_of_collected_groups_collectedAppendInvariant
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
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_collectedAppendInvariant
    hroot hcollect hflat hcollected hcompatible happend).executeQueryAtDepth_eq_spec

theorem executeQueryAtDepth_eq_spec_of_collected_groups_collectedLocalAppendInvariant
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
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_collectedLocalAppendInvariant
    hroot hcollect hflat hcollected hcompatible happend).executeQueryAtDepth_eq_spec

theorem executeQueryAtDepth_eq_spec_of_collected_groups_recursiveAppendState
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
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_recursiveAppendState
    hroot hcollect hflat hcollected hcompatible happend).executeQueryAtDepth_eq_spec

theorem executeQueryAtDepth_eq_spec_of_collected_groups_child_state
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
    (hchildren :
      ∀ childDepth runtimeType identity childSelectionSet,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := childSelectionSet }
              initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  executeQueryAtDepth_eq_spec_of_collected_groups_collectedLocalAppendInvariant
    hroot hcollect hflat hcollected hcompatible
    (CollectedFieldGroupLocalAppendInvariant.of_child_state hchildren)

theorem executeQueryAtDepth_eq_spec_of_collected_groups_depth_one
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {source : Value ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hflat :
      VisitSubfieldsFlatCollects schema resolvers variableValues 1
        operation.rootType source operation.selectionSet (.object []))
    (hcollected :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := 0
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups) :
    executeQueryAtDepth schema resolvers variableValues operation 1 source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation 1 source :=
  executeQueryAtDepth_eq_spec_of_collected_groups_collectedAppendInvariant
    hroot hcollect hflat hcollected hcompatible
    (CollectedFieldGroupAppendInvariant.depth_zero schema resolvers
      variableValues groups)

theorem executeQuery_eq_spec_of_executedGroups
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
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth
        operation.rootType source groups)
    (hnodup : PairKeysNodup groups) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact executeQueryAtDepth_eq_spec_of_executedGroups hroot hcollect hflat
    hgroups hnodup

theorem executeQuery_eq_spec_of_collected_groups_state_of_invariant
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
    (hplanStates :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ExecutedFieldAppendPlanState schema resolvers variableValues depth
            field fields [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_groups_state_of_invariant hroot
      hcollect hflat hinvariant hcompatible hplanStates

theorem executeQuery_eq_spec_of_collected_groups_appendInvariant
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
      FieldGroupAppendInvariant schema resolvers variableValues depth) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_groups_appendInvariant hroot
      hcollect hflat hcollected hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_collectedAppendInvariant
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
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_groups_collectedAppendInvariant
      hroot hcollect hflat hcollected hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_collectedLocalAppendInvariant
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
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_groups_collectedLocalAppendInvariant
      hroot hcollect hflat hcollected hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_recursiveAppendState
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
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_groups_recursiveAppendState hroot
      hcollect hflat hcollected hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_child_state
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
    (hchildren :
      ∀ childDepth runtimeType identity childSelectionSet,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := childSelectionSet }
              initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_groups_child_state hroot hcollect
      hflat hcollected hcompatible hchildren

end ExecutionUngrouped
end Algorithms

end GraphQL
