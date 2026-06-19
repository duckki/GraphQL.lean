import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldExecution

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def VisitSubfieldsAbsorbsFrom
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (base : Response) :
    List Selection -> Response -> Prop
  | [], current => ResponseAbsorbs base current
  | selection :: rest, current =>
      let next :=
        visitSelection schema resolvers variableValues depth parentType source
          selection current
      ResponseAbsorbs base next ∧
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source base rest next

def VisitSubfieldsLocalAbsorbsFrom
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
    List Selection -> Response -> Prop
  | [], current => ResponseMergeReady current
  | selection :: rest, current =>
      let next :=
        visitSelection schema resolvers variableValues depth parentType source
          selection current
      ResponseMergeReady current ∧
      ResponseMergeReady next ∧
      ResponseAbsorbs current next ∧
      VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
        parentType source rest next

theorem visitSubfields_absorbs_from_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (base : Response) :
    ∀ (selectionSet : List Selection) (current : Response),
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source base selectionSet current ->
        ResponseAbsorbs base
          (visitSubfields schema resolvers variableValues depth parentType
            source selectionSet current)
  | [], current, hsteps => by
      simpa [visitSubfields, VisitSubfieldsAbsorbsFrom] using hsteps
  | selection :: rest, current, hsteps => by
      simp [VisitSubfieldsAbsorbsFrom] at hsteps
      rcases hsteps with ⟨_hnext, hrest⟩
      simp [visitSubfields]
      exact visitSubfields_absorbs_from_steps schema resolvers variableValues
        depth parentType source base rest
        (visitSelection schema resolvers variableValues depth parentType source
          selection current)
        hrest

theorem visitSubfields_absorbs_from_local_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (base : Response) :
    ∀ (selectionSet : List Selection) (current : Response),
      ResponseMergeReady base ->
      ResponseAbsorbs base current ->
      VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
        parentType source selectionSet current ->
        VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source base selectionSet current
  | [], current, _hbaseReady, hbaseCurrent, _hlocal => by
      simpa [VisitSubfieldsAbsorbsFrom] using hbaseCurrent
  | selection :: rest, current, hbaseReady, hbaseCurrent, hlocal => by
      simp [VisitSubfieldsLocalAbsorbsFrom] at hlocal
      rcases hlocal with
        ⟨hcurrentReady, hnextReady, hcurrentNext, hrestLocal⟩
      let next :=
        visitSelection schema resolvers variableValues depth parentType source
          selection current
      have hbaseNext : ResponseAbsorbs base next :=
        ResponseAbsorbs_trans_of_ready base current next hbaseReady hcurrentReady
          hnextReady hbaseCurrent hcurrentNext
      simp [VisitSubfieldsAbsorbsFrom, next, hbaseNext]
      exact visitSubfields_absorbs_from_local_steps schema resolvers
        variableValues depth parentType source base rest next
        hbaseReady hbaseNext hrestLocal

theorem duplicateFieldSubselections_absorb_of_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (first later : ExecutableField)
    (hsteps :
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
              (.object []))) :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
        ResponseAbsorbs
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) first.selectionSet (.object []))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))) := by
  intro childDepth runtimeType identity hlt
  exact
    visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity)
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) first.selectionSet (.object []))
      later.selectionSet
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) first.selectionSet (.object []))
      (hsteps childDepth runtimeType identity hlt)

theorem VisitSubfieldsAbsorbsFrom_single_field_allowed_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
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
        parentType source (.object fields)
        [.field responseName fieldName arguments directives selectionSet]
        (.object fields) := by
  intro hfieldsReady hcollisionAbsorbs
  have hstep :
      ResponseAbsorbs (.object fields)
        (visitSelection schema resolvers variableValues (depth + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet)
          (.object fields)) :=
    visitSelection_field_allowed_succ_absorbs schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet fields hallowed hfieldsReady hcollisionAbsorbs
  simp [VisitSubfieldsAbsorbsFrom, hstep]

theorem VisitSubfieldsAbsorbsFrom_single_field_allowed_succ_of_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × Response))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst) :
    ResponseMergeReady (.object fields) ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues (depth + 1)
        parentType source (.object fields)
        [.field responseName fieldName arguments directives selectionSet]
        (.object fields) := by
  intro hfieldsReady
  have hstep :
      ResponseAbsorbs (.object fields)
        (visitSelection schema resolvers variableValues (depth + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet)
          (.object fields)) :=
    visitSelection_field_allowed_succ_absorbs_of_fresh schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfresh hfieldsReady
  simp [VisitSubfieldsAbsorbsFrom, hstep]

theorem VisitSubfieldsAbsorbsFrom_nil_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : Value ObjectIdentity)
    (output : Response) :
    ResponseMergeReady output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output [] output := by
  intro hready
  simpa [VisitSubfieldsAbsorbsFrom] using
    ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_field_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output
        [.field responseName fieldName arguments directives selectionSet]
        output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_field_directives_blocked schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_field_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ResponseMergeReady output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues 0
        parentType source output
        [.field responseName fieldName arguments directives selectionSet]
        output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_field_depth_zero schema resolvers variableValues parentType
      source responseName fieldName arguments directives selectionSet output
      hallowed]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_inline_none_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output
        [.inlineFragment none directives selectionSet]
        output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_inline_none_directives_blocked schema resolvers
      variableValues depth parentType source directives selectionSet output
      hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_inline_some_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false) :
    ResponseMergeReady output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output
        [.inlineFragment (some typeCondition) directives selectionSet]
        output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_inline_some_directives_blocked schema resolvers
      variableValues depth parentType source typeCondition directives
      selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_inline_some_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition = false) :
    ResponseMergeReady output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output
        [.inlineFragment (some typeCondition) directives selectionSet]
        output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_inline_some_type_not_apply schema resolvers variableValues
      depth parentType source typeCondition directives selectionSet output
      hallowed hnotApply]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_inline_none_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
      parentType source output selectionSet output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output
        [.inlineFragment none directives selectionSet] output := by
  intro hchild
  have habsorbs :=
    visitSubfields_absorbs_from_steps schema resolvers variableValues depth
      parentType source output selectionSet output hchild
  simp [VisitSubfieldsAbsorbsFrom, visitSelection, hallowed]
  exact habsorbs

theorem VisitSubfieldsAbsorbsFrom_single_inline_some_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : Response)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition = true) :
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
      parentType source output selectionSet output ->
      VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output
        [.inlineFragment (some typeCondition) directives selectionSet]
        output := by
  intro hchild
  have habsorbs :=
    visitSubfields_absorbs_from_steps schema resolvers variableValues depth
      parentType source output selectionSet output hchild
  simp [VisitSubfieldsAbsorbsFrom, visitSelection, hallowed, happly]
  exact habsorbs

mutual
  theorem visitSelection_preserves_object
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selection : Selection) (fields : List (Name × Response)),
        ∃ outputFields,
          visitSelection schema resolvers variableValues depth parentType source
            selection (.object fields) =
          .object outputFields
  | .field responseName fieldName arguments directives selectionSet, fields => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · cases depth with
        | zero =>
            exact ⟨fields, by simp [visitSelection, hallowed]⟩
        | succ depth =>
            refine
              ⟨mergeResponseField responseName
                (executeField schema resolvers variableValues depth source
                  (.object fields)
                  (executableField parentType responseName fieldName arguments
                    selectionSet))
                fields, ?_⟩
            simp [visitSelection, hallowed, mergeResponseFieldIntoObject]
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        exact
          ⟨fields,
            visitSelection_field_directives_blocked schema resolvers
              variableValues depth parentType source responseName fieldName
              arguments directives selectionSet (.object fields) hblocked⟩
  | .inlineFragment none directives selectionSet, fields => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · simpa [visitSelection, hallowed] using
          visitSubfields_preserves_object schema resolvers variableValues depth
            parentType source selectionSet fields
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        exact ⟨fields, by simp [visitSelection, hblocked]⟩
  | .inlineFragment (some typeCondition) directives selectionSet, fields => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · by_cases happly :
            doesFragmentTypeApplyBool schema parentType source typeCondition =
              true
        · simpa [visitSelection, hallowed, happly] using
            visitSubfields_preserves_object schema resolvers variableValues
              depth parentType source selectionSet fields
        · have hnotApply :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                false := by
            cases h :
              doesFragmentTypeApplyBool schema parentType source typeCondition <;>
              simp [h] at happly ⊢
          exact ⟨fields, by simp [visitSelection, hallowed, hnotApply]⟩
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        exact ⟨fields, by simp [visitSelection, hblocked]⟩

  theorem visitSubfields_preserves_object
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selectionSet : List Selection) (fields : List (Name × Response)),
        ∃ outputFields,
          visitSubfields schema resolvers variableValues depth parentType source
            selectionSet (.object fields) =
          .object outputFields
  | [], fields => by
      exact ⟨fields, by simp [visitSubfields]⟩
  | selection :: rest, fields => by
      obtain ⟨selectionFields, hselection⟩ :=
        visitSelection_preserves_object schema resolvers variableValues depth
          parentType source selection fields
      obtain ⟨restFields, hrest⟩ :=
        visitSubfields_preserves_object schema resolvers variableValues depth
          parentType source rest selectionFields
      exact ⟨restFields, by simp [visitSubfields, hselection, hrest]⟩
end

theorem VisitSubfieldsFlatCollects.of_root_equivalences
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (horiginal :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source selectionSet)
    (hflat :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))) :
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source selectionSet (.object []) := by
  unfold VisitSubfieldsFlatCollects
  obtain ⟨originalFields, horiginalFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  obtain ⟨flatFields, hflatFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) []
  have horiginalFields_eq :
      originalFields =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source selectionSet := by
    unfold executeRootSelectionSet at horiginal
    simpa [horiginalFields] using horiginal
  have hflatFields_eq :
      flatFields =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) := by
    unfold executeRootSelectionSet at hflat
    simpa [hflatFields] using hflat
  rw [horiginalFields, hflatFields]
  congr
  exact horiginalFields_eq.trans
    ((specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields_collectFields
      schema resolvers variableValues depth parentType source selectionSet).symm.trans
        hflatFields_eq.symm)

mutual
  theorem visitSelection_pairKeysNodup
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selection : Selection) (fields : List (Name × Response)),
        PairKeysNodup fields ->
          PairKeysNodup
            (match
              visitSelection schema resolvers variableValues depth parentType
                source selection (.object fields)
             with
             | .object outputFields => outputFields
             | _ => fields)
  | .field responseName fieldName arguments directives selectionSet, fields,
      hnodup => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · cases depth with
        | zero =>
            simpa [visitSelection, hallowed] using hnodup
        | succ depth =>
            simp [visitSelection, hallowed, mergeResponseFieldIntoObject]
            exact mergeResponseField_pairKeysNodup responseName
              (executeField schema resolvers variableValues depth source
                (.object fields)
                (executableField parentType responseName fieldName arguments
                  selectionSet))
              fields hnodup
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        have hvisit :=
          visitSelection_field_directives_blocked schema resolvers
            variableValues depth parentType source responseName fieldName
            arguments directives selectionSet (.object fields) hblocked
        simpa [hvisit] using hnodup
  | .inlineFragment none directives selectionSet, fields, hnodup => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · simpa [visitSelection, hallowed] using
          visitSubfields_pairKeysNodup schema resolvers variableValues depth
            parentType source selectionSet fields hnodup
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        simpa [visitSelection, hblocked] using hnodup
  | .inlineFragment (some typeCondition) directives selectionSet, fields,
      hnodup => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · by_cases happly :
            doesFragmentTypeApplyBool schema parentType source typeCondition =
              true
        · simpa [visitSelection, hallowed, happly] using
            visitSubfields_pairKeysNodup schema resolvers variableValues depth
              parentType source selectionSet fields hnodup
        · have hnotApply :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                false := by
            cases h :
              doesFragmentTypeApplyBool schema parentType source typeCondition <;>
              simp [h] at happly ⊢
          simpa [visitSelection, hallowed, hnotApply] using hnodup
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        simpa [visitSelection, hblocked] using hnodup

  theorem visitSubfields_pairKeysNodup
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selectionSet : List Selection) (fields : List (Name × Response)),
        PairKeysNodup fields ->
          PairKeysNodup
            (match
              visitSubfields schema resolvers variableValues depth parentType
                source selectionSet (.object fields)
             with
             | .object outputFields => outputFields
             | _ => fields)
  | [], fields, hnodup => by
      simpa [visitSubfields] using hnodup
  | selection :: rest, fields, hnodup => by
      obtain ⟨selectionFields, hselectionObject⟩ :=
        visitSelection_preserves_object schema resolvers variableValues depth
          parentType source selection fields
      have hselectionNodup :
          PairKeysNodup selectionFields := by
        simpa [hselectionObject] using
          visitSelection_pairKeysNodup schema resolvers variableValues depth
            parentType source selection fields hnodup
      obtain ⟨restFields, hrestObject⟩ :=
        visitSubfields_preserves_object schema resolvers variableValues depth
          parentType source rest selectionFields
      have hrestNodup :
          PairKeysNodup restFields := by
        simpa [hrestObject] using
          visitSubfields_pairKeysNodup schema resolvers variableValues depth
            parentType source rest selectionFields hselectionNodup
      simpa [visitSubfields, hselectionObject, hrestObject] using hrestNodup
end

mutual
  theorem visitSelection_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selection : Selection) (fields : List (Name × Response)),
        ResponseMergeReady (.object fields) ->
          ResponseMergeReady
            (visitSelection schema resolvers variableValues depth parentType
              source selection (.object fields))
  | .field responseName fieldName arguments directives selectionSet, fields,
      hfieldsReady => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · cases depth with
        | zero =>
            simpa [visitSelection, hallowed] using hfieldsReady
        | succ depth =>
            apply visitSelection_field_allowed_succ_ready schema resolvers
              variableValues depth parentType source responseName fieldName
              arguments directives selectionSet fields hallowed hfieldsReady
            exact executeField_response_ready schema resolvers variableValues
              depth source fields
              (executableField parentType responseName fieldName arguments
                selectionSet)
              hfieldsReady
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        simpa [visitSelection_field_directives_blocked schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet (.object fields) hblocked] using
          hfieldsReady
  | .inlineFragment none directives selectionSet, fields, hfieldsReady => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · simpa [visitSelection, hallowed] using
          visitSubfields_response_ready schema resolvers variableValues depth
            parentType source selectionSet fields hfieldsReady
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        simpa [visitSelection, hblocked] using hfieldsReady
  | .inlineFragment (some typeCondition) directives selectionSet, fields,
      hfieldsReady => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · by_cases happly :
            doesFragmentTypeApplyBool schema parentType source typeCondition =
              true
        · simpa [visitSelection, hallowed, happly] using
            visitSubfields_response_ready schema resolvers variableValues depth
              parentType source selectionSet fields hfieldsReady
        · have hnotApply :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                false := by
            cases h :
              doesFragmentTypeApplyBool schema parentType source typeCondition <;>
              simp [h] at happly ⊢
          simpa [visitSelection, hallowed, hnotApply] using hfieldsReady
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        simpa [visitSelection, hblocked] using hfieldsReady

  theorem visitSubfields_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selectionSet : List Selection) (fields : List (Name × Response)),
        ResponseMergeReady (.object fields) ->
          ResponseMergeReady
            (visitSubfields schema resolvers variableValues depth parentType
              source selectionSet (.object fields))
  | [], fields, hfieldsReady => by
      simpa [visitSubfields] using hfieldsReady
  | selection :: rest, fields, hfieldsReady => by
      obtain ⟨selectionFields, hselectionObject⟩ :=
        visitSelection_preserves_object schema resolvers variableValues depth
          parentType source selection fields
      have hselectionReady :
          ResponseMergeReady (.object selectionFields) := by
        simpa [hselectionObject] using
          visitSelection_response_ready schema resolvers variableValues depth
            parentType source selection fields hfieldsReady
      simpa [visitSubfields, hselectionObject] using
        visitSubfields_response_ready schema resolvers variableValues depth
          parentType source rest selectionFields hselectionReady

  theorem executeField_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (source : Value ObjectIdentity) (fields : List (Name × Response))
      (field : ExecutableField) :
      ResponseMergeReady (.object fields) ->
        ResponseMergeReady
          (executeField schema resolvers variableValues depth source
            (.object fields) field) := by
    intro hfieldsReady
    unfold executeField
    let childType :=
      (schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName
    let previous :=
      (responseObjectField? field.responseName (.object fields)).getD .null
    have hpreviousReady : ResponseMergeReady previous := by
      unfold previous
      cases hlookup :
          responseObjectField? field.responseName (.object fields) with
      | none =>
          simp
          exact ResponseMergeReady.null
      | some response =>
          simpa [hlookup] using
            responseObjectField?_some_ready field.responseName response fields
              hfieldsReady hlookup
    exact completeValue_response_ready schema resolvers variableValues depth
      childType field.selectionSet
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source)
      previous hpreviousReady

  theorem completeValue_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) :
      ∀ (depth : Nat) (parentType : Name) (selectionSet : List Selection)
        (value : Value ObjectIdentity) (previous : Response),
        ResponseMergeReady previous ->
          ResponseMergeReady
            (completeValue schema resolvers variableValues depth parentType
              selectionSet value previous)
  | 0, _parentType, _selectionSet, value, _previous, _hprevious => by
      simp [completeValue]
      exact ResponseMergeReady_shallowResponse value
  | depth + 1, _parentType, _selectionSet, .null, _previous, _hprevious => by
      simp [completeValue]
      exact ResponseMergeReady.null
  | depth + 1, _parentType, _selectionSet, .scalar value, _previous,
      _hprevious => by
      simp [completeValue]
      exact ResponseMergeReady.scalar value
  | depth + 1, parentType, selectionSet, .object runtimeType _identity,
      previous, hprevious => by
      by_cases hincludes :
          schema.typeIncludesObjectBool parentType runtimeType = true
      · cases previous with
        | object fields =>
            simpa [completeValue, hincludes] using
              visitSubfields_response_ready schema resolvers variableValues
                depth runtimeType (.object runtimeType _identity) selectionSet
                fields hprevious
        | null =>
            simpa [completeValue, hincludes] using
              visitSubfields_response_ready schema resolvers variableValues
                depth runtimeType (.object runtimeType _identity) selectionSet []
                ResponseMergeReady_empty_object
        | scalar value =>
            simpa [completeValue, hincludes] using
              visitSubfields_response_ready schema resolvers variableValues
                depth runtimeType (.object runtimeType _identity) selectionSet []
                ResponseMergeReady_empty_object
        | list values =>
            simpa [completeValue, hincludes] using
              visitSubfields_response_ready schema resolvers variableValues
                depth runtimeType (.object runtimeType _identity) selectionSet []
                ResponseMergeReady_empty_object
      · have hnotIncludes :
            schema.typeIncludesObjectBool parentType runtimeType = false := by
          cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
            simp [h] at hincludes ⊢
        cases previous <;>
          simpa [completeValue, hnotIncludes] using ResponseMergeReady.null
  | depth + 1, parentType, selectionSet, .list values, previous, hprevious => by
      have hpreviousValuesReady :
          ∀ response,
            response ∈
              (match previous with
               | .list previousValues => previousValues
               | _ => []) ->
              ResponseMergeReady response := by
        cases previous with
        | list previousValues =>
            intro response hmem
            exact ResponseMergeReady_list_value previousValues response
              hprevious hmem
        | null =>
            intro response hmem
            simp at hmem
        | scalar value =>
            intro response hmem
            simp at hmem
        | object fields =>
            intro response hmem
            simp at hmem
      unfold completeValue
      let step :=
        fun (state : List Response × List Response)
            (value : Value ObjectIdentity) =>
          let previous :=
            match state.snd with
            | [] => .null
            | previous :: _rest => previous
          let remainingPrevious :=
            match state.snd with
            | [] => []
            | _previous :: rest => rest
          (completeValue schema resolvers variableValues depth parentType
            selectionSet value previous :: state.fst, remainingPrevious)
      have hfoldReady :
          ∀ values acc remaining response,
            (∀ accResponse,
              accResponse ∈ acc ->
                ResponseMergeReady accResponse) ->
            (∀ previousResponse,
              previousResponse ∈ remaining ->
                ResponseMergeReady previousResponse) ->
            response ∈ (List.foldl step (acc, remaining) values).fst ->
              ResponseMergeReady response := by
        intro values
        induction values with
        | nil =>
            intro acc remaining response haccReady _hremainingReady hmem
            simpa [step] using haccReady response hmem
        | cons value rest ih =>
            intro acc remaining response haccReady hremainingReady hmem
            cases remaining with
            | nil =>
                apply ih
                · intro accResponse haccMem
                  change
                    accResponse ∈
                      completeValue schema resolvers variableValues depth
                        parentType selectionSet value .null :: acc at haccMem
                  rcases List.mem_cons.mp haccMem with hhead | htail
                  · rw [hhead]
                    exact completeValue_response_ready schema resolvers
                      variableValues depth parentType selectionSet value .null
                      ResponseMergeReady.null
                  · exact haccReady accResponse htail
                · intro previousResponse hpreviousMem
                  change previousResponse ∈ ([] : List Response) at hpreviousMem
                  cases hpreviousMem
                · simpa [step] using hmem
            | cons previous remainingRest =>
                have hpreviousReady :
                    ResponseMergeReady previous :=
                  hremainingReady previous (by simp)
                apply ih
                · intro accResponse haccMem
                  change
                    accResponse ∈
                      completeValue schema resolvers variableValues depth
                        parentType selectionSet value previous :: acc at haccMem
                  rcases List.mem_cons.mp haccMem with hhead | htail
                  · rw [hhead]
                    exact completeValue_response_ready schema resolvers
                      variableValues depth parentType selectionSet value
                      previous hpreviousReady
                  · exact haccReady accResponse htail
                · intro previousResponse hpreviousMem
                  change previousResponse ∈ remainingRest at hpreviousMem
                  have hmemRest : previousResponse ∈ remainingRest := hpreviousMem
                  exact hremainingReady previousResponse
                    (List.mem_cons.mpr (Or.inr hmemRest))
                · simpa [step] using hmem
      apply ResponseMergeReady.list
      intro response hmem
      apply hfoldReady values [] (match previous with
        | .list previousValues => previousValues
        | _ => []) response
      · intro accResponse haccMem
        simp at haccMem
      · exact hpreviousValuesReady
      · simpa [step] using List.mem_reverse.mp hmem
end

mutual
  theorem visitSelection_local_absorbs_from_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selection : Selection) (fields : List (Name × Response)),
        ResponseMergeReady (.object fields) ->
          let next :=
            visitSelection schema resolvers variableValues depth parentType
              source selection (.object fields)
          ResponseMergeReady (.object fields) ∧
          ResponseMergeReady next ∧
          ResponseAbsorbs (.object fields) next
  | .field responseName fieldName arguments directives selectionSet, fields,
      hfieldsReady => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · cases depth with
        | zero =>
            have hnextReady :
                ResponseMergeReady
                  (visitSelection schema resolvers variableValues 0 parentType
                    source
                    (.field responseName fieldName arguments directives
                      selectionSet)
                    (.object fields)) := by
              rw [visitSelection_field_depth_zero schema resolvers variableValues
                parentType source responseName fieldName arguments directives
                selectionSet (.object fields) hallowed]
              exact hfieldsReady
            have habsorbs :
                ResponseAbsorbs (.object fields)
                  (visitSelection schema resolvers variableValues 0 parentType
                    source
                    (.field responseName fieldName arguments directives
                      selectionSet)
                    (.object fields)) :=
              visitSelection_field_depth_zero_absorbs_of_ready schema resolvers
                variableValues parentType source responseName fieldName
                arguments directives selectionSet (.object fields) hallowed
                hfieldsReady
            exact ⟨hfieldsReady, hnextReady, habsorbs⟩
        | succ depth =>
            let field :=
              executableField parentType responseName fieldName arguments
                selectionSet
            have hfieldReady :
                ResponseMergeReady
                  (executeField schema resolvers variableValues depth source
                    (.object fields) field) :=
              executeField_response_ready schema resolvers variableValues depth
                source fields field hfieldsReady
            have hnextReady :
                ResponseMergeReady
                  (visitSelection schema resolvers variableValues (depth + 1)
                    parentType source
                    (.field responseName fieldName arguments directives
                      selectionSet)
                    (.object fields)) :=
              visitSelection_field_allowed_succ_ready schema resolvers
                variableValues depth parentType source responseName fieldName
                arguments directives selectionSet fields hallowed hfieldsReady
                (by simpa [field] using hfieldReady)
            have habsorbs :
                ResponseAbsorbs (.object fields)
                  (visitSelection schema resolvers variableValues (depth + 1)
                    parentType source
                    (.field responseName fieldName arguments directives
                      selectionSet)
                    (.object fields)) :=
              visitSelection_field_allowed_succ_absorbs schema resolvers
                variableValues depth parentType source responseName fieldName
                arguments directives selectionSet fields hallowed hfieldsReady
                (by
                  intro existing hmem
                  exact ResponseAbsorbs_merge_of_ready existing
                    (executeField schema resolvers variableValues depth source
                      (.object fields) field)
                    (ResponseMergeReady_object_field fields responseName
                      existing hfieldsReady hmem)
                    hfieldReady)
            exact ⟨hfieldsReady, hnextReady, habsorbs⟩
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        have hnextReady :
            ResponseMergeReady
              (visitSelection schema resolvers variableValues depth parentType
                source
                (.field responseName fieldName arguments directives selectionSet)
                (.object fields)) := by
          rw [visitSelection_field_directives_blocked schema resolvers
            variableValues depth parentType source responseName fieldName
            arguments directives selectionSet (.object fields) hblocked]
          exact hfieldsReady
        have habsorbs :
            ResponseAbsorbs (.object fields)
              (visitSelection schema resolvers variableValues depth parentType
                source
                (.field responseName fieldName arguments directives selectionSet)
                (.object fields)) :=
          visitSelection_field_blocked_absorbs_of_ready schema resolvers
            variableValues depth parentType source responseName fieldName
            arguments directives selectionSet (.object fields) hblocked
            hfieldsReady
        exact ⟨hfieldsReady, hnextReady, habsorbs⟩
  | .inlineFragment none directives selectionSet, fields, hfieldsReady => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · have hlocal :
            VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
              parentType source selectionSet (.object fields) :=
          visitSubfields_local_absorbs_from_ready schema resolvers
            variableValues depth parentType source selectionSet fields
            hfieldsReady
        have hnextReady :
            ResponseMergeReady
              (visitSelection schema resolvers variableValues depth parentType
                source (.inlineFragment none directives selectionSet)
                (.object fields)) := by
          simpa [visitSelection, hallowed] using
            visitSubfields_response_ready schema resolvers variableValues depth
              parentType source selectionSet fields hfieldsReady
        have habsorbs :
            ResponseAbsorbs (.object fields)
              (visitSelection schema resolvers variableValues depth parentType
                source (.inlineFragment none directives selectionSet)
                (.object fields)) := by
          simpa [visitSelection, hallowed] using
            visitSubfields_absorbs_from_steps schema resolvers variableValues
              depth parentType source (.object fields) selectionSet
              (.object fields)
              (visitSubfields_absorbs_from_local_steps schema resolvers
                variableValues depth parentType source (.object fields)
                selectionSet (.object fields) hfieldsReady
                (ResponseAbsorbs_refl_of_ready (.object fields) hfieldsReady)
                hlocal)
        exact ⟨hfieldsReady, hnextReady, habsorbs⟩
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        have hnextReady :
            ResponseMergeReady
              (visitSelection schema resolvers variableValues depth parentType
                source (.inlineFragment none directives selectionSet)
                (.object fields)) := by
          rw [visitSelection_inline_none_directives_blocked schema resolvers
            variableValues depth parentType source directives selectionSet
            (.object fields) hblocked]
          exact hfieldsReady
        have habsorbs :
            ResponseAbsorbs (.object fields)
              (visitSelection schema resolvers variableValues depth parentType
                source (.inlineFragment none directives selectionSet)
                (.object fields)) :=
          visitSelection_inline_none_blocked_absorbs_of_ready schema resolvers
            variableValues depth parentType source directives selectionSet
            (.object fields) hblocked hfieldsReady
        exact ⟨hfieldsReady, hnextReady, habsorbs⟩
  | .inlineFragment (some typeCondition) directives selectionSet, fields,
      hfieldsReady => by
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · by_cases happly :
            doesFragmentTypeApplyBool schema parentType source typeCondition =
              true
        · have hlocal :
              VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
                parentType source selectionSet (.object fields) :=
            visitSubfields_local_absorbs_from_ready schema resolvers
              variableValues depth parentType source selectionSet fields
              hfieldsReady
          have hnextReady :
              ResponseMergeReady
                (visitSelection schema resolvers variableValues depth parentType
                  source
                  (.inlineFragment (some typeCondition) directives selectionSet)
                  (.object fields)) := by
            simpa [visitSelection, hallowed, happly] using
              visitSubfields_response_ready schema resolvers variableValues depth
                parentType source selectionSet fields hfieldsReady
          have habsorbs :
              ResponseAbsorbs (.object fields)
                (visitSelection schema resolvers variableValues depth parentType
                  source
                  (.inlineFragment (some typeCondition) directives selectionSet)
                  (.object fields)) := by
            simpa [visitSelection, hallowed, happly] using
              visitSubfields_absorbs_from_steps schema resolvers variableValues
                depth parentType source (.object fields) selectionSet
                (.object fields)
                (visitSubfields_absorbs_from_local_steps schema resolvers
                  variableValues depth parentType source (.object fields)
                  selectionSet (.object fields) hfieldsReady
                (ResponseAbsorbs_refl_of_ready (.object fields) hfieldsReady)
                  hlocal)
          exact ⟨hfieldsReady, hnextReady, habsorbs⟩
        · have hnotApply :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                false := by
            cases h :
              doesFragmentTypeApplyBool schema parentType source typeCondition <;>
              simp [h] at happly ⊢
          have hnextReady :
              ResponseMergeReady
                (visitSelection schema resolvers variableValues depth parentType
                  source
                  (.inlineFragment (some typeCondition) directives selectionSet)
                  (.object fields)) := by
            rw [visitSelection_inline_some_type_not_apply schema resolvers
              variableValues depth parentType source typeCondition directives
              selectionSet (.object fields) hallowed hnotApply]
            exact hfieldsReady
          have habsorbs :
              ResponseAbsorbs (.object fields)
                (visitSelection schema resolvers variableValues depth parentType
                  source
                  (.inlineFragment (some typeCondition) directives selectionSet)
                  (.object fields)) :=
            visitSelection_inline_some_not_apply_absorbs_of_ready schema
              resolvers variableValues depth parentType source typeCondition
              directives selectionSet (.object fields) hallowed hnotApply
              hfieldsReady
          exact ⟨hfieldsReady, hnextReady, habsorbs⟩
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives <;>
            simp [h] at hallowed ⊢
        have hnextReady :
            ResponseMergeReady
              (visitSelection schema resolvers variableValues depth parentType
                source
                (.inlineFragment (some typeCondition) directives selectionSet)
                (.object fields)) := by
          rw [visitSelection_inline_some_directives_blocked schema resolvers
            variableValues depth parentType source typeCondition directives
            selectionSet (.object fields) hblocked]
          exact hfieldsReady
        have habsorbs :
            ResponseAbsorbs (.object fields)
              (visitSelection schema resolvers variableValues depth parentType
                source
                (.inlineFragment (some typeCondition) directives selectionSet)
                (.object fields)) :=
          visitSelection_inline_some_blocked_absorbs_of_ready schema resolvers
            variableValues depth parentType source typeCondition directives
            selectionSet (.object fields) hblocked hfieldsReady
        exact ⟨hfieldsReady, hnextReady, habsorbs⟩

  theorem visitSubfields_local_absorbs_from_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : Value ObjectIdentity) :
      ∀ (selectionSet : List Selection) (fields : List (Name × Response)),
        ResponseMergeReady (.object fields) ->
          VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
            parentType source selectionSet (.object fields)
  | [], fields, hfieldsReady => by
      simpa [VisitSubfieldsLocalAbsorbsFrom] using hfieldsReady
  | selection :: rest, fields, hfieldsReady => by
      obtain ⟨selectionFields, hselectionObject⟩ :=
        visitSelection_preserves_object schema resolvers variableValues depth
          parentType source selection fields
      have hstep :=
        visitSelection_local_absorbs_from_ready schema resolvers variableValues
          depth parentType source selection fields hfieldsReady
      have hselectionReady :
          ResponseMergeReady (.object selectionFields) := by
        simpa [hselectionObject] using hstep.2.1
      have hrest :
          VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
            parentType source rest (.object selectionFields) :=
        visitSubfields_local_absorbs_from_ready schema resolvers variableValues
          depth parentType source rest selectionFields hselectionReady
      simp [VisitSubfieldsLocalAbsorbsFrom, hstep.1, hstep.2.1, hstep.2.2]
      simpa [hselectionObject] using hrest
end

theorem VisitSubfieldsAbsorbsFrom_single_field_allowed_succ_of_visit_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (firstSelectionSet : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh :
      ∀ fields,
        visitSubfields schema resolvers variableValues (depth + 1)
          parentType source firstSelectionSet (.object []) =
        .object fields ->
          responseName ∉ fields.map Prod.fst) :
    VisitSubfieldsAbsorbsFrom schema resolvers variableValues (depth + 1)
      parentType source
      (visitSubfields schema resolvers variableValues (depth + 1)
        parentType source firstSelectionSet (.object []))
      [.field responseName fieldName arguments directives selectionSet]
      (visitSubfields schema resolvers variableValues (depth + 1)
        parentType source firstSelectionSet (.object [])) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (depth + 1) parentType source firstSelectionSet []
  rw [hfields]
  apply VisitSubfieldsAbsorbsFrom_single_field_allowed_succ_of_fresh
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet fields hallowed
    (hfresh fields hfields)
  simpa [hfields] using
    visitSubfields_response_ready schema resolvers variableValues (depth + 1)
      parentType source firstSelectionSet [] ResponseMergeReady_empty_object

theorem visitSubfields_depth_zero_equivalence
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity) :
    ∀ selectionSet output,
      visitSubfields schema resolvers variableValues 0 parentType source
        selectionSet output = output
  | [], output => by
      simp [visitSubfields]
  | selection :: rest, output => by
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          by_cases hallowed :
              selectionDirectivesAllowBool variableValues directives = true
          · simp [visitSubfields,
              visitSelection_field_depth_zero schema resolvers variableValues
                parentType source responseName fieldName arguments directives
                selectionSet output hallowed,
              visitSubfields_depth_zero_equivalence schema resolvers variableValues
                parentType source rest output]
          · have hblocked :
                selectionDirectivesAllowBool variableValues directives = false := by
              cases h :
                selectionDirectivesAllowBool variableValues directives <;>
                  simp [h] at hallowed ⊢
            simp [visitSubfields,
              visitSelection_field_directives_blocked schema resolvers
                variableValues 0 parentType source responseName fieldName
                arguments directives selectionSet output hblocked,
              visitSubfields_depth_zero_equivalence schema resolvers variableValues
                parentType source rest output]
      | inlineFragment typeCondition directives selectionSet =>
          by_cases hallowed :
              selectionDirectivesAllowBool variableValues directives = true
          · cases typeCondition with
            | none =>
                simp [visitSubfields, visitSelection, hallowed,
                  visitSubfields_depth_zero_equivalence schema resolvers variableValues
                    parentType source selectionSet output,
                  visitSubfields_depth_zero_equivalence schema resolvers variableValues
                    parentType source rest output]
            | some typeCondition =>
                by_cases happly :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = true
                · simp [visitSubfields, visitSelection, hallowed, happly,
                    visitSubfields_depth_zero_equivalence schema resolvers variableValues
                      parentType source selectionSet output,
                    visitSubfields_depth_zero_equivalence schema resolvers variableValues
                      parentType source rest output]
                · have hnotApply :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition = false := by
                    cases h :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition <;>
                        simp [h] at happly ⊢
                  simp [visitSubfields,
                    visitSelection_inline_some_type_not_apply schema resolvers
                      variableValues 0 parentType source typeCondition
                      directives selectionSet output hallowed hnotApply,
                    visitSubfields_depth_zero_equivalence schema resolvers variableValues
                      parentType source rest output]
          · have hblocked :
                selectionDirectivesAllowBool variableValues directives = false := by
              cases h :
                selectionDirectivesAllowBool variableValues directives <;>
                  simp [h] at hallowed ⊢
            cases typeCondition with
            | none =>
                simp [visitSubfields,
                  visitSelection_inline_none_directives_blocked schema
                    resolvers variableValues 0 parentType source directives
                    selectionSet output hblocked,
                  visitSubfields_depth_zero_equivalence schema resolvers variableValues
                    parentType source rest output]
            | some typeCondition =>
                simp [visitSubfields,
                  visitSelection_inline_some_directives_blocked schema
                    resolvers variableValues 0 parentType source typeCondition
                    directives selectionSet output hblocked,
                  visitSubfields_depth_zero_equivalence schema resolvers variableValues
                    parentType source rest output]

theorem executeCollectedFields_depth_zero_equivalence
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (source : Value ObjectIdentity) :
    ∀ groups,
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        0 source groups = []
  | [] => by
      simp [GraphQL.Execution.executeCollectedFields]
  | (_responseName, fields) :: rest => by
      cases fields <;>
        simp [GraphQL.Execution.executeCollectedFields,
          GraphQL.Execution.executeField,
          executeCollectedFields_depth_zero_equivalence schema resolvers variableValues
            source rest]

theorem VisitSubfieldsFlatCollects_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (output : Response) :
    VisitSubfieldsFlatCollects schema resolvers variableValues 0 parentType
      source selectionSet output := by
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_depth_zero_equivalence schema resolvers variableValues parentType
    source selectionSet output]
  rw [visitSubfields_depth_zero_equivalence schema resolvers variableValues parentType
    source
    (executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)))
    output]

theorem VisitSubfieldsFlatCollectsAllOutputs_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues 0
      parentType source selectionSet := by
  intro output
  exact VisitSubfieldsFlatCollects_depth_zero schema resolvers variableValues
    parentType source selectionSet output

theorem ExecutableFieldsFlatSpecEquivalent_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (fields : List ExecutableField) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues 0
      parentType source fields := by
  unfold ExecutableFieldsFlatSpecEquivalent
  simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
    visitSubfields_depth_zero_equivalence schema resolvers variableValues parentType source
      (executableFieldSelections fields) (.object []),
    executeCollectedFields_depth_zero_equivalence schema resolvers variableValues source]

theorem ExecutableGroupsFlatSpecEquivalent_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField)) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues 0
      parentType source groups := by
  unfold ExecutableGroupsFlatSpecEquivalent
  exact ExecutableFieldsFlatSpecEquivalent_depth_zero schema resolvers
    variableValues parentType source (collectedExecutableFields groups)

theorem depthZeroStateEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (initial : Response) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := 0
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := initial } := by
  simp [ExecutionStateEquivalent, ResponseDataEquivalent,
    ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection,
    visitSubfields_depth_zero_equivalence schema resolvers variableValues parentType
      source selectionSet initial,
    executeCollectedFields_depth_zero_equivalence schema resolvers variableValues source,
    mergeResponse_empty_object_right]

end ExecutionUngrouped
end Algorithms

end GraphQL
