import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def ExecutedSingleGroupSelectionState.of_collected_two_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    ExecutedSingleGroupSelectionState schema resolvers variableValues depth
      parentType source selectionSet := by
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
  have hgroupResponses :
      ExecutableFieldsResponseName responseName [first, later] :=
    hresponses responseName [first, later] hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType [first, later] :=
    hparents responseName [first, later] hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible [first, later] :=
    hcompatible responseName [first, later] hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable resolvers source [first, later] :=
    hstable responseName [first, later] hgroup
  have hfirstResponse : first.responseName = responseName :=
    hgroupResponses first (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later (by simp)
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later (by simp)
  have hsameResponse : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  have hfieldName : later.fieldName = first.fieldName :=
    (hgroupCompatible first later (by simp) (by simp) hsameResponse).1.symm
  have hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source :=
    (hgroupStable first later (by simp) (by simp) hsameResponse).symm
  apply ExecutedSingleGroupSelectionState.of_collected_appendPlan schema
    resolvers variableValues depth parentType source selectionSet groups
    responseName first [later] hcollect hgroup hexact hdirect
    (by
      intro childDepth runtimeType identity hlt _hincludes
      exact hfirstChildren childDepth runtimeType identity hlt)
  exact
    ExecutedFieldAppendPlan_two_of_visit_absorbs schema resolvers
      variableValues depth parentType source responseName first later
      (resolvers.resolve first.parentType first.fieldName first.arguments source)
      hlaterParent hlaterResponse hfieldName hresolveLater hfirstChildren
      hobjects hchildren

theorem stateEquivalent_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
  have hprefixChildren :
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
                  GraphQL.Execution.mergedFieldSelectionSet (first :: []) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hfirstChildren childDepth runtimeType identity hlt
  have hobjectsMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
                (.object []))) := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hobjects childDepth runtimeType identity hlt
  have hchildrenMerged :
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
                    ((first :: []) ++ [later]) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildren childDepth runtimeType identity hlt
  exact
    stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName first [later] hcollect hgroup hexact hdirect hinvariant
      hcompatible
      (ExecutedFieldAppendPlanState.singleton
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hprefixChildren childDepth runtimeType identity hlt)
        (by simp)
        hobjectsMerged
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hchildrenMerged childDepth runtimeType identity hlt))

theorem stateEquivalent_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    (hobjectSteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object [])))
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
  have hprefixChildren :
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
                  GraphQL.Execution.mergedFieldSelectionSet (first :: []) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hfirstChildren childDepth runtimeType identity hlt
  have hstepsMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object [])) := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hobjectSteps childDepth runtimeType identity hlt
  have hchildrenMerged :
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
                    ((first :: []) ++ [later]) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildren childDepth runtimeType identity hlt
  exact
    stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName first [later] hcollect hgroup hexact hdirect hinvariant
      hcompatible
      (ExecutedFieldAppendPlanState.singleton_of_visit_absorbs
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hprefixChildren childDepth runtimeType identity hlt)
        (by simp) hstepsMerged
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hchildrenMerged childDepth runtimeType identity hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    (hobjectSteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object [])))
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
    (stateEquivalent_of_collected_two_field_group_invariant_steps schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName first later hcollect hgroup hexact hdirect hinvariant
      hcompatible hfirstChildren hobjectSteps hchildren)

theorem executeQueryAtDepth_eq_spec_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    (hobjectSteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object [])))
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
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_two_field_group_invariant_steps schema
      resolvers variableValues depth operation.rootType source
      operation.selectionSet groups responseName first later hcollect hgroup
      hexact hdirect hinvariant hcompatible hfirstChildren hobjectSteps
      hchildren

theorem executeQuery_eq_spec_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    (hobjectSteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object [])))
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
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_two_field_group_invariant_steps
      schema resolvers variableValues operation depth source groups
      responseName first later hroot hcollect hgroup hexact hdirect hinvariant
      hcompatible hfirstChildren hobjectSteps hchildren

theorem executeRootSelectionSet_eq_spec_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    (stateEquivalent_of_collected_two_field_group_invariant schema resolvers
      variableValues depth parentType source selectionSet groups responseName
      first later hcollect hgroup hexact hdirect hinvariant hcompatible
      hfirstChildren hobjects hchildren)

theorem executeQueryAtDepth_eq_spec_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_two_field_group_invariant schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      groups responseName first later hcollect hgroup hexact hdirect hinvariant
      hcompatible hfirstChildren hobjects hchildren

theorem executeQuery_eq_spec_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_two_field_group_invariant schema
      resolvers variableValues operation depth source groups responseName first
      later hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hfirstChildren hobjects hchildren

def ExecutedFieldGroup.two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveFirst :
      resolvers.resolve first.parentType first.fieldName first.arguments source =
        resolved)
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
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName first [later] :=
  ExecutedFieldGroup.of_appendPlan schema resolvers variableValues depth
    parentType source responseName first [later] resolved
    (by
      intro candidate hmem
      simp at hmem
      rcases hmem with rfl | hmem
      · exact hfirstResponse
      · rcases hmem with rfl | hfalse
        · exact hlaterResponse)
    (by
      intro candidate hmem
      simp at hmem
      rcases hmem with rfl | hmem
      · exact hfirstParent
      · rcases hmem with rfl | hfalse
        · exact hlaterParent)
    hresolveFirst
    (by
      intro childDepth runtimeType identity hlt _hincludes
      exact hfirstChildren childDepth runtimeType identity hlt)
    (ExecutedFieldAppendPlan_two_of_visit_absorbs schema resolvers
      variableValues depth parentType source responseName first later resolved
      hlaterParent hlaterResponse hfieldName hresolveLater hfirstChildren
      hobjects hchildren)

def ExecutedFieldGroup.collected_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName first [later] := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName [first, later] :=
    hresponses responseName [first, later] hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType [first, later] :=
    hparents responseName [first, later] hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible [first, later] :=
    hcompatible responseName [first, later] hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable resolvers source [first, later] :=
    hstable responseName [first, later] hgroup
  have hfirstResponse : first.responseName = responseName :=
    hgroupResponses first (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later (by simp)
  have hfirstParent : first.parentType = parentType :=
    hgroupParents first (by simp)
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later (by simp)
  have hsameResponse : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  have hfieldName : later.fieldName = first.fieldName :=
    (hgroupCompatible first later (by simp) (by simp) hsameResponse).1.symm
  have hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source :=
    (hgroupStable first later (by simp) (by simp) hsameResponse).symm
  exact
    ExecutedFieldGroup.two_of_visit_absorbs schema resolvers variableValues
      depth parentType source responseName first later
      (resolvers.resolve first.parentType first.fieldName first.arguments source)
      hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName rfl
      hresolveLater hfirstChildren hobjects hchildren

theorem executeRootSelectionSet_eq_spec_of_exact_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source)
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName first
      [later] hcollect hdirect
      (ExecutedFieldGroup.two_of_visit_absorbs schema resolvers variableValues
        depth parentType source responseName first later
        (resolvers.resolve first.parentType first.fieldName first.arguments
          source)
        hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName rfl
        hresolveLater hfirstChildren hobjects hchildren)

theorem executeRootSelectionSet_eq_spec_of_collected_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName first
      [later] hcollect hdirect
      (ExecutedFieldGroup.collected_two_of_visit_absorbs schema resolvers
        variableValues depth parentType source [(responseName, [first, later])]
        responseName first later hgroup hresponses hparents hcompatible hstable
        hfirstChildren hobjects hchildren)

theorem executeQueryAtDepth_eq_spec_of_collected_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent operation.rootType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_collected_two_field_group_appendPlan
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet groups responseName first later hcollect hgroup
      hexact hdirect hresponses hparents hcompatible hstable hfirstChildren
      hobjects hchildren

theorem executeQuery_eq_spec_of_collected_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent operation.rootType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_two_field_group_appendPlan schema
      resolvers variableValues operation depth source groups responseName first
      later hroot hcollect hgroup hexact hdirect hresponses hparents
      hcompatible hstable hfirstChildren hobjects hchildren

theorem executeRootSelectionSet_executableFieldSelections_two_fields_eq_spec_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveFirst :
      resolvers.resolve first.parentType first.fieldName first.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [first, later]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (executableFieldSelections [first, later]) := by
  cases first with
  | mk firstParent firstResponse firstFieldName firstArguments firstSelectionSet =>
      cases later with
      | mk laterParent laterResponse laterFieldName laterArguments
          laterSelectionSet =>
          dsimp at hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName hresolveFirst hresolveLater hobjects hchildren ⊢
          subst firstParent
          subst laterParent
          subst firstResponse
          subst laterResponse
          subst laterFieldName
          change
            executeRootSelectionSet schema resolvers variableValues
              (depth + 1) parentType source
              (executableFieldSelections
                [ executableField parentType responseName firstFieldName
                    firstArguments firstSelectionSet
                , executableField parentType responseName firstFieldName
                    laterArguments laterSelectionSet ]) =
            GraphQL.Execution.executeRootSelectionSet schema resolvers
              variableValues (depth + 1) parentType source
              (executableFieldSelections
                [ executableField parentType responseName firstFieldName
                    firstArguments firstSelectionSet
                , executableField parentType responseName firstFieldName
                    laterArguments laterSelectionSet ])
          rw [specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
            schema resolvers variableValues depth parentType source
            responseName
            (executableField parentType responseName firstFieldName
              firstArguments firstSelectionSet)
            [executableField parentType responseName firstFieldName
              laterArguments laterSelectionSet]
              resolved
              (by
                intro candidate hmem
                simp [executableField] at hmem ⊢
                rcases hmem with rfl | hmem
                · rfl
                · rcases hmem with rfl | hfalse
                  · rfl
                  )
              (by
                intro candidate hmem
                simp [executableField] at hmem ⊢
                rcases hmem with rfl | hmem
                · rfl
                · rcases hmem with rfl | hfalse
                  · rfl
                  )
              (by
                simpa [executableField] using hresolveFirst)]
          have hcomplete :
              mergeResponse
                (completeValue schema resolvers variableValues depth
                  ((schema.fieldReturnType? parentType firstFieldName).getD
                    firstFieldName)
                  firstSelectionSet resolved .null)
                (completeValue schema resolvers variableValues depth
                  ((schema.fieldReturnType? parentType firstFieldName).getD
                    firstFieldName)
                  laterSelectionSet resolved
                  (completeValue schema resolvers variableValues depth
                    ((schema.fieldReturnType? parentType firstFieldName).getD
                      firstFieldName)
                    firstSelectionSet resolved .null)) =
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth
                ((schema.fieldReturnType? parentType firstFieldName).getD
                  firstFieldName)
                (GraphQL.Execution.mergedFieldSelectionSet
                  [ executableField parentType responseName firstFieldName
                      firstArguments firstSelectionSet
                  , executableField parentType responseName firstFieldName
                      laterArguments laterSelectionSet ])
                resolved := by
            calc
              mergeResponse
                  (completeValue schema resolvers variableValues depth
                    ((schema.fieldReturnType? parentType firstFieldName).getD
                      firstFieldName)
                    firstSelectionSet resolved .null)
                  (completeValue schema resolvers variableValues depth
                    ((schema.fieldReturnType? parentType firstFieldName).getD
                      firstFieldName)
                    laterSelectionSet resolved
                    (completeValue schema resolvers variableValues depth
                      ((schema.fieldReturnType? parentType firstFieldName).getD
                        firstFieldName)
                      firstSelectionSet resolved .null)
                  ) =
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth
                    ((schema.fieldReturnType? parentType firstFieldName).getD
                      firstFieldName)
                    [ executableField parentType responseName firstFieldName
                        firstArguments firstSelectionSet
                    , executableField parentType responseName firstFieldName
                        laterArguments laterSelectionSet ]
                    resolved := by
                exact
                  completeValue_two_fields_merge_eq_spec_of_visit_absorbs
                    schema resolvers variableValues depth
                    ((schema.fieldReturnType? parentType firstFieldName).getD
                      firstFieldName)
                    (executableField parentType responseName firstFieldName
                        firstArguments firstSelectionSet)
                    (executableField parentType responseName firstFieldName
                      laterArguments laterSelectionSet)
                    resolved hobjects
                    (by
                      intro childDepth runtimeType identity hlt _hincludes
                      exact hchildren childDepth runtimeType identity hlt)
              _ =
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth
                    ((schema.fieldReturnType? parentType firstFieldName).getD
                      firstFieldName)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      [ executableField parentType responseName firstFieldName
                          firstArguments firstSelectionSet
                      , executableField parentType responseName firstFieldName
                          laterArguments laterSelectionSet ])
                    resolved := by
                exact
                  GraphQL.NormalForm.completeValue_eq_mergedFieldSelectionSet
                    schema resolvers variableValues depth
                    ((schema.fieldReturnType? parentType firstFieldName).getD
                      firstFieldName)
                    [ executableField parentType responseName firstFieldName
                        firstArguments firstSelectionSet
                    , executableField parentType responseName firstFieldName
                        laterArguments laterSelectionSet ]
                    resolved
          simp [executeRootSelectionSet, visitSubfields, visitSelection,
            executeField, executableFieldSelections,
            executableFieldSelection, executableField, responseObjectField?,
            lookupResponseField?, mergeResponseFieldIntoObject,
            mergeResponseField, GraphQL.Execution.mergedFieldSelectionSet,
            selectionDirectivesAllowBool_empty, hresolveFirst,
            hresolveLater, hcomplete]

theorem executeRootSelectionSet_executableFieldSelections_two_fields_eq_merged_complete_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveFirst :
      resolvers.resolve first.parentType first.fieldName first.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [first, later]) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? first.parentType first.fieldName).getD
          first.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet [first, later])
        resolved)] := by
  calc
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [first, later]) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source
        (executableFieldSelections [first, later]) := by
        exact
          executeRootSelectionSet_executableFieldSelections_two_fields_eq_spec_of_visit_absorbs
            schema resolvers variableValues depth parentType source
            responseName first later resolved hfirstParent hlaterParent
            hfirstResponse hlaterResponse hfieldName hresolveFirst
            hresolveLater hobjects hchildren
    _ =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? first.parentType first.fieldName).getD
            first.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet [first, later])
          resolved)] := by
        rw [specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
          schema resolvers variableValues depth parentType source responseName
          first [later] resolved]
        · intro candidate hmem
          simp at hmem
          rcases hmem with rfl | hmem
          · exact hfirstResponse
          · rcases hmem with rfl | hfalse
            · exact hlaterResponse
        · intro candidate hmem
          simp at hmem
          rcases hmem with rfl | hmem
          · exact hfirstParent
          · rcases hmem with rfl | hfalse
            · exact hlaterParent
        · exact hresolveFirst

theorem ExecutableFieldsMergedComplete_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveFirst :
      resolvers.resolve first.parentType first.fieldName first.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
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
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName first [later] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_two_fields_eq_merged_complete_of_visit_absorbs
      schema resolvers variableValues depth parentType source responseName
      first later resolved hfirstParent hlaterParent hfirstResponse
      hlaterResponse hfieldName hresolveFirst hresolveLater hobjects hchildren

theorem ExecutableFieldsMergedComplete_collected_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName first [later]
      (resolvers.resolve first.parentType first.fieldName first.arguments
        source) := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName [first, later] :=
    hresponses responseName [first, later] hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType [first, later] :=
    hparents responseName [first, later] hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible [first, later] :=
    hcompatible responseName [first, later] hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable resolvers source [first, later] :=
    hstable responseName [first, later] hgroup
  have hfirstResponse : first.responseName = responseName :=
    hgroupResponses first (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later (by simp)
  have hfirstParent : first.parentType = parentType :=
    hgroupParents first (by simp)
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later (by simp)
  have hsameResponse : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  have hfieldName : later.fieldName = first.fieldName :=
    (hgroupCompatible first later (by simp) (by simp) hsameResponse).1.symm
  have hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source :=
    (hgroupStable first later (by simp) (by simp) hsameResponse).symm
  exact
    ExecutableFieldsMergedComplete_two_of_visit_absorbs
      schema resolvers variableValues depth parentType source responseName first
      later
      (resolvers.resolve first.parentType first.fieldName first.arguments source)
      hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName rfl
      hresolveLater hobjects hchildren

theorem ExecutableGroupsFlatSpecEquivalent_two_field_group_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType responseName : Name) (source : Value ObjectIdentity)
    (first later : ExecutableField)
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source)
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
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, [first, later])] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    executeRootSelectionSet_executableFieldSelections_two_fields_eq_spec_of_visit_absorbs
      schema resolvers variableValues depth parentType source responseName first
      later
      (resolvers.resolve first.parentType first.fieldName first.arguments source)
      hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName rfl
      hresolveLater hobjects hchildren

theorem executeRootSelectionSet_eq_spec_of_exact_two_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source)
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  have hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    rw [hcollect]
    exact
      ExecutableGroupsFlatSpecEquivalent_two_field_group_of_visit_absorbs
        schema resolvers variableValues depth parentType responseName source
        first later hfirstParent hlaterParent hfirstResponse hlaterResponse
        hfieldName hresolveLater hobjects hchildren
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (depth + 1) parentType source
      selectionSet hdirect hgroups

theorem stateEquivalent_of_exact_two_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source)
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
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
    (executeRootSelectionSet_eq_spec_of_exact_two_field_group schema
      resolvers variableValues depth parentType source selectionSet
      responseName first later hcollect hdirect hfirstParent hlaterParent
      hfirstResponse hlaterResponse hfieldName hresolveLater hobjects
      hchildren)

theorem stateEquivalent_of_collected_two_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
  have hgroupResponses :
      ExecutableFieldsResponseName responseName [first, later] :=
    hresponses responseName [first, later] hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType [first, later] :=
    hparents responseName [first, later] hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible [first, later] :=
    hcompatible responseName [first, later] hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable resolvers source [first, later] :=
    hstable responseName [first, later] hgroup
  have hfirstResponse : first.responseName = responseName :=
    hgroupResponses first (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later (by simp)
  have hfirstParent : first.parentType = parentType :=
    hgroupParents first (by simp)
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later (by simp)
  have hsameResponse : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  have hfieldName : later.fieldName = first.fieldName :=
    (hgroupCompatible first later (by simp) (by simp) hsameResponse).1.symm
  have hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source :=
    (hgroupStable first later (by simp) (by simp) hsameResponse).symm
  exact
    stateEquivalent_of_exact_two_field_group schema resolvers variableValues
      depth parentType source selectionSet responseName first later
      (by simpa [hexact] using hcollect) hdirect hfirstParent hlaterParent
      hfirstResponse hlaterResponse hfieldName hresolveLater hobjects
      hchildren

theorem stateEquivalent_of_collected_two_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
  exact
    stateEquivalent_of_collected_two_field_group schema resolvers variableValues
      depth parentType source selectionSet groups responseName first later
      hcollect hgroup hexact hdirect hresponses hparents hcompatible hstable
      hobjects hchildren

theorem executeQueryAtDepth_eq_spec_of_collected_two_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_two_field_group_of_invariant schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      groups responseName first later hcollect hgroup hexact hdirect hinvariant
      hcompatible hobjects hchildren

theorem executeQuery_eq_spec_of_collected_two_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
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
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_two_field_group_of_invariant schema
      resolvers variableValues operation depth source groups responseName first
      later hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hobjects hchildren

theorem executeQueryAtDepth_eq_spec_of_exact_two_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hfirstParent : first.parentType = operation.rootType)
    (hlaterParent : later.parentType = operation.rootType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source)
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
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact stateEquivalent_of_exact_two_field_group schema resolvers
    variableValues depth operation.rootType source operation.selectionSet
    responseName first later hcollect hdirect hfirstParent hlaterParent
    hfirstResponse hlaterResponse hfieldName hresolveLater hobjects hchildren

theorem executeQuery_eq_spec_of_exact_two_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, [first, later])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hfirstParent : first.parentType = operation.rootType)
    (hlaterParent : later.parentType = operation.rootType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source)
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
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact executeQueryAtDepth_eq_spec_of_exact_two_field_group schema resolvers
    variableValues operation depth source responseName first later hroot hcollect
    hdirect hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName
    hresolveLater hobjects hchildren

theorem executeRootSelectionSet_executableFieldSelections_collected_two_field_group_eq_spec_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [first, later]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (executableFieldSelections [first, later]) := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName [first, later] :=
    hresponses responseName [first, later] hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType [first, later] :=
    hparents responseName [first, later] hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible [first, later] :=
    hcompatible responseName [first, later] hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable resolvers source [first, later] :=
    hstable responseName [first, later] hgroup
  have hfirstResponse : first.responseName = responseName :=
    hgroupResponses first (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later (by simp)
  have hfirstParent : first.parentType = parentType :=
    hgroupParents first (by simp)
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later (by simp)
  have hsameResponse : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  have hfieldName : later.fieldName = first.fieldName :=
    (hgroupCompatible first later (by simp) (by simp) hsameResponse).1.symm
  have hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve first.parentType first.fieldName first.arguments source :=
    (hgroupStable first later (by simp) (by simp) hsameResponse).symm
  exact
    executeRootSelectionSet_executableFieldSelections_two_fields_eq_spec_of_visit_absorbs
      schema resolvers variableValues depth parentType source responseName first
      later
      (resolvers.resolve first.parentType first.fieldName first.arguments source)
      hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName rfl
      hresolveLater hobjects hchildren

theorem ExecutableFieldsFlatSpecEquivalent_collected_two_field_group_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [first, later] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact
    executeRootSelectionSet_executableFieldSelections_collected_two_field_group_eq_spec_of_visit_absorbs
      schema resolvers variableValues depth parentType source groups
      responseName first later hgroup hresponses hparents hcompatible
      hstable hobjects hchildren

theorem ExecutableGroupsFlatSpecEquivalent_collected_two_field_group_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
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
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, [first, later])] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_collected_two_field_group_of_visit_absorbs
      schema resolvers variableValues depth parentType source groups
      responseName first later hgroup hresponses hparents hcompatible
      hstable hobjects hchildren


end ExecutionUngrouped
end Algorithms

end GraphQL
