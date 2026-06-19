import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Absorption

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

inductive ValueContainsObject {ObjectIdentity : Type} :
    Value ObjectIdentity -> Name -> Option ObjectIdentity -> Prop where
  | here {runtimeType : Name} {identity : Option ObjectIdentity} :
      ValueContainsObject (.object runtimeType identity) runtimeType identity
  | list {values : List (Value ObjectIdentity)} {value : Value ObjectIdentity}
      {runtimeType : Name} {identity : Option ObjectIdentity} :
      value ∈ values ->
      ValueContainsObject value runtimeType identity ->
        ValueContainsObject (.list values) runtimeType identity

theorem specExecuteCollectedFields_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) :
    ∀ left right : List (Name × List ExecutableField),
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        depth source (left ++ right) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        depth source left ++
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        depth source right
  | [], right => by
      simp [GraphQL.Execution.executeCollectedFields]
  | (responseName, fields) :: rest, right => by
      simp [GraphQL.Execution.executeCollectedFields,
        specExecuteCollectedFields_append schema resolvers variableValues depth
          source rest right, List.append_assoc]

theorem specExecuteRootSelectionSet_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left right : List Selection)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right)) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ right) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source left ++
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source right := by
  simp [GraphQL.Execution.executeRootSelectionSet]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint]
  · exact specExecuteCollectedFields_append schema resolvers variableValues
      depth source
      (GraphQL.Execution.collectFields schema variableValues parentType source
        left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        right)
  · exact hdisjoint
  · exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source right

theorem visitSubfields_empty_eq_executeRootSelectionSet_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    visitSubfields schema resolvers variableValues depth parentType source
      selectionSet (.object []) =
    .object
      (executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  rw [hfields]
  simp [executeRootSelectionSet, hfields]

structure ExecutedAppendSelectionState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left right : List Selection) : Prop where
  leftEquivalent :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source left =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source left
  rightEquivalent :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source right =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source right
  namesDisjoint :
    GraphQL.NormalForm.executableGroupNamesDisjoint
      (GraphQL.Execution.collectFields schema variableValues parentType source
        left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        right)
  rightAppends :
    visitSubfields schema resolvers variableValues depth parentType source right
      (.object
        (executeRootSelectionSet schema resolvers variableValues depth
          parentType source left)) =
    .object
      (executeRootSelectionSet schema resolvers variableValues depth parentType
        source left ++
       executeRootSelectionSet schema resolvers variableValues depth parentType
        source right)

theorem executeRootSelectionSet_eq_spec_of_appendState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left right : List Selection)
    (state :
      ExecutedAppendSelectionState schema resolvers variableValues depth
        parentType source left right) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ right) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ right) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [visitSubfields_empty_eq_executeRootSelectionSet_object]
  rw [state.rightAppends]
  simp
  rw [state.leftEquivalent, state.rightEquivalent]
  rw [specExecuteRootSelectionSet_append_of_namesDisjoint schema resolvers
    variableValues depth parentType source left right state.namesDisjoint]

theorem executeCollectedFields_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) :
    ∀ {responseName groups},
      responseName ∈
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues depth source groups).map Prod.fst ->
      responseName ∈ groups.map Prod.fst
  | _responseName, [], hmem => by
      simp [GraphQL.Execution.executeCollectedFields] at hmem
  | responseName, group :: rest, hmem => by
      cases group with
      | mk groupResponseName fields =>
          cases fields with
          | nil =>
              simp [GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField] at hmem
              simpa using Or.inr
                (executeCollectedFields_key_mem schema resolvers variableValues
                  depth source (by simpa [List.mem_map] using hmem))
          | cons field fieldsRest =>
              cases depth with
              | zero =>
                  simp [GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.executeField] at hmem
                  simpa using Or.inr
                    (executeCollectedFields_key_mem schema resolvers
                      variableValues 0 source
                      (by simpa [List.mem_map] using hmem))
              | succ depth' =>
                  simp [GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.executeField] at hmem
                  rcases hmem with hhead | htail
                  · simpa using Or.inl hhead
                  · simpa using Or.inr
                      (executeCollectedFields_key_mem schema resolvers
                        variableValues (depth' + 1) source
                        (by simpa [List.mem_map] using htail))

theorem specExecuteRootSelectionSet_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name) :
    responseName ∈
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues depth parentType source selectionSet).map Prod.fst ->
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet).map Prod.fst := by
  intro hmem
  simpa [GraphQL.Execution.executeRootSelectionSet] using
    executeCollectedFields_key_mem schema resolvers variableValues depth source
      hmem

theorem executeRootSelectionSet_key_mem_of_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name)
    (hroot :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source selectionSet) :
    responseName ∈
        (executeRootSelectionSet schema resolvers variableValues depth
          parentType source selectionSet).map Prod.fst ->
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet).map Prod.fst := by
  intro hmem
  apply specExecuteRootSelectionSet_key_mem schema resolvers variableValues
    depth parentType source selectionSet responseName
  simpa [hroot] using hmem

theorem responseName_fresh_of_disjoint_single_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hleftEq :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source left =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    responseName ∉
      (executeRootSelectionSet schema resolvers variableValues depth parentType
        source left).map Prod.fst := by
  intro hmem
  have hleftMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst :=
    executeRootSelectionSet_key_mem_of_eq_spec schema resolvers variableValues
      depth parentType source left responseName hleftEq hmem
  have hrightMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]).map
          Prod.fst := by
    simp [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      hallowed]
  exact hdisjoint responseName hleftMem hrightMem

theorem executableGroupNamesDisjoint_single_field_of_responseName_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst) :
    GraphQL.NormalForm.executableGroupNamesDisjoint
      (GraphQL.Execution.collectFields schema variableValues parentType
        source left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        [.field responseName fieldName arguments directives selectionSet]) := by
  intro candidate hleft hright
  simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups, hallowed] at hright
  exact hfresh (by simpa [hright] using hleft)

theorem executeCollectedFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : Value ObjectIdentity) :
    ∀ groups,
      PairKeysNodup groups ->
        PairKeysNodup
          (GraphQL.Execution.executeCollectedFields schema resolvers
            variableValues depth source groups)
  | [], _hnodup => by
      simp [PairKeysNodup, GraphQL.Execution.executeCollectedFields]
  | group :: rest, hnodup => by
      cases group with
      | mk groupResponseName fields =>
          have hparts := List.nodup_cons.mp hnodup
          have hgroupNotRest : groupResponseName ∉ rest.map Prod.fst := hparts.1
          have hrestNodup : PairKeysNodup rest := hparts.2
          have htailNodup :=
            executeCollectedFields_pairKeysNodup schema resolvers
              variableValues depth source rest hrestNodup
          cases fields with
          | nil =>
              simpa [PairKeysNodup, GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField]
                using htailNodup
          | cons field fieldsRest =>
              cases depth with
              | zero =>
                  simpa [PairKeysNodup, GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.executeField] using htailNodup
              | succ depth' =>
                  unfold PairKeysNodup at htailNodup ⊢
                  simp [GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.executeField]
                  constructor
                  · intro response hmem
                    exact hgroupNotRest
                      (executeCollectedFields_key_mem schema resolvers
                        variableValues (depth' + 1) source
                        (by simpa [List.mem_map] using Exists.intro response hmem))
                  · exact htailNodup

theorem collectFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    PairKeysNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet) :=
  PairKeysNodup_of_executableGroupNamesNodup
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (NormalForm.collectFields_namesNodup schema variableValues parentType
      source selectionSet)

theorem collectSubfields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : Value ObjectIdentity)
    (fields : List ExecutableField) :
    PairKeysNodup
      (GraphQL.Execution.collectSubfields schema variableValues objectType
        objectValue fields) := by
  simpa [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
    using
      collectFields_pairKeysNodup schema variableValues objectType objectValue
        (GraphQL.Execution.mergedFieldSelectionSet fields)

mutual
  theorem specExecuteCollectedFields_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (source : Value ObjectIdentity) :
      ∀ groups,
        PairKeysNodup groups ->
          ResponseMergeReady
            (.object
              (GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source groups))
    | [], _hnodup => by
        simp [GraphQL.Execution.executeCollectedFields]
        exact ResponseMergeReady_empty_object
    | (responseName, fields) :: rest, hnodup => by
        have hrestNodup : PairKeysNodup rest := by
          exact (List.nodup_cons.mp hnodup).2
        have hrestReady :
            ResponseMergeReady
              (.object
                (GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues depth source rest)) :=
          specExecuteCollectedFields_response_ready schema resolvers
            variableValues depth source rest hrestNodup
        cases fields with
        | nil =>
            simpa [GraphQL.Execution.executeCollectedFields,
              GraphQL.Execution.executeField] using hrestReady
        | cons field fieldsRest =>
            cases depth with
            | zero =>
                simpa [GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField] using hrestReady
            | succ depth' =>
                let resolved :=
                  resolvers.resolve field.parentType field.fieldName
                    field.arguments source
                let childType :=
                  (schema.fieldReturnType? field.parentType
                    field.fieldName).getD field.fieldName
                have hfieldReady :
                    ResponseMergeReady
                      (GraphQL.Execution.completeValue schema resolvers
                        variableValues depth' childType (field :: fieldsRest)
                        resolved) := by
                  exact specCompleteValue_response_ready schema resolvers
                    variableValues depth' childType (field :: fieldsRest)
                    resolved
                have houtputNodup :
                    PairKeysNodup
                      (GraphQL.Execution.executeCollectedFields schema
                        resolvers variableValues (depth' + 1) source
                        ((responseName, field :: fieldsRest) :: rest)) :=
                  executeCollectedFields_pairKeysNodup schema resolvers
                    variableValues (depth' + 1) source
                    ((responseName, field :: fieldsRest) :: rest) hnodup
                apply ResponseMergeReady_object
                · simpa [GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.executeField, resolved, childType]
                    using houtputNodup
                · intro fieldResponseName response hmem
                  simp [GraphQL.Execution.executeCollectedFields,
                    GraphQL.Execution.executeField] at hmem
                  rcases hmem with hhead | htail
                  · rcases hhead with ⟨_hname, hresponse⟩
                    cases hresponse
                    exact hfieldReady
                  · exact ResponseMergeReady_object_field
                      (GraphQL.Execution.executeCollectedFields schema
                        resolvers variableValues (depth' + 1) source rest)
                      fieldResponseName response hrestReady htail

  theorem specCompleteValue_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) :
      ∀ (depth : Nat) (parentType : Name) (fields : List ExecutableField)
        (value : Value ObjectIdentity),
        ResponseMergeReady
          (GraphQL.Execution.completeValue schema resolvers variableValues
            depth parentType fields value)
    | 0, _parentType, _fields, value => by
        simp [GraphQL.Execution.completeValue]
        exact ResponseMergeReady_shallowResponse value
    | depth + 1, _parentType, _fields, .null => by
        simp [GraphQL.Execution.completeValue]
        exact ResponseMergeReady.null
    | depth + 1, _parentType, _fields, .scalar value => by
        simp [GraphQL.Execution.completeValue]
        exact ResponseMergeReady.scalar value
    | depth + 1, parentType, fields, source@(.object runtimeType _identity) => by
        by_cases hincludes :
            schema.typeIncludesObjectBool parentType runtimeType = true
        · simp [GraphQL.Execution.completeValue, hincludes]
          simpa
            [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
            using
              specExecuteCollectedFields_response_ready schema resolvers
                variableValues depth (.object runtimeType _identity)
                (GraphQL.Execution.collectSubfields schema variableValues
                  runtimeType (.object runtimeType _identity) fields)
                (collectSubfields_pairKeysNodup schema variableValues runtimeType
                  (.object runtimeType _identity) fields)
        · have hfalse :
              schema.typeIncludesObjectBool parentType runtimeType = false := by
            cases h :
              schema.typeIncludesObjectBool parentType runtimeType <;>
              simp [h] at hincludes ⊢
          simp [GraphQL.Execution.completeValue, hfalse]
          exact ResponseMergeReady.null
    | depth + 1, parentType, fields, .list values => by
        simp [GraphQL.Execution.completeValue]
        apply ResponseMergeReady.list
        intro response hmem
        rcases List.mem_map.mp hmem with ⟨value, _hvalue, hresponse⟩
        rw [← hresponse]
        exact specCompleteValue_response_ready schema resolvers variableValues
          depth parentType fields value
end

theorem specExecuteCollectedFields_collectFields_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    ResponseMergeReady
      (.object
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues depth source
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :=
  specExecuteCollectedFields_response_ready schema resolvers variableValues
    depth source
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (collectFields_pairKeysNodup schema variableValues parentType source
      selectionSet)

theorem specExecuteRootSelectionSet_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    ResponseMergeReady
      (.object
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues depth parentType source selectionSet)) := by
  simpa [GraphQL.Execution.executeRootSelectionSet] using
    specExecuteCollectedFields_collectFields_response_ready schema resolvers
      variableValues depth parentType source selectionSet

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hcompatible :
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · exact collectFields_pairKeysNodup state.window.schema
      state.window.variableValues state.window.parentType state.window.source
      state.window.selectionSet
  · exact hcompatible
  · exact collectFields_argumentsNodup_of_selectionSetValid state.window.schema
      variableDefinitions state.window.variableValues state.window.parentType
      state.window.parentType state.window.source state.window.selectionSet
      hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_validationCompatible
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hcompatible :
      CollectedGroupsValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType
          state.window.source state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact CollectedGroupsValidationMergeCompatible.fieldCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      (collectFields_sameResponseParent state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hcompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hscopedCompatible :
      ScopedFieldsFieldValidationMergeCompatible
        (FieldMerge.collectFields state.window.schema state.window.parentType
          state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact collectFields_fieldCompatible_of_selectionSetValid_scopedCompatible
      state.window.schema variableDefinitions state.window.variableValues
      state.window.parentType state.window.parentType state.window.source
      state.window.selectionSet hselectionSet hscopedCompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_sameScopedParent
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
        state.window.selectionSet)
    (hsameParent :
      ScopedFieldsSameResponseParent
        (FieldMerge.collectFields state.window.schema state.window.parentType
          state.window.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    state variableDefinitions hselectionSet
  · exact fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
      state.window.schema state.window.parentType state.window.selectionSet
      hmerge hsameParent
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeApplies
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (runtimeType : Name)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
        state.window.selectionSet)
    (hruntimeApplies :
      ∀ scopedField,
        scopedField ∈
            FieldMerge.collectFields state.window.schema state.window.parentType
              state.window.selectionSet ->
          ScopedFieldRuntimeApplies state.window.schema runtimeType
            scopedField)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    state variableDefinitions hselectionSet
  · exact
      fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_runtimeApplies
        state.window.schema state.window.parentType runtimeType
        state.window.selectionSet hmerge hruntimeApplies
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (runtimeType : Name)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        state.window.parentType state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
        state.window.selectionSet)
    (hruntimeScoped :
      ExecutableFieldsRuntimeScopedBy state.window.schema runtimeType
        (FieldMerge.collectFields state.window.schema state.window.parentType
          state.window.selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet)))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact collectFields_fieldCompatible_of_canMerge_runtimeScoped
      state.window.schema state.window.variableValues state.window.parentType
      state.window.parentType runtimeType state.window.source
      state.window.selectionSet hmerge hruntimeScoped
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScopedBy
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (validParent runtimeType : Name)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet :
      Validation.selectionSetValid state.window.schema variableDefinitions
        validParent state.window.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge state.window.schema validParent
        state.window.selectionSet)
    (hruntimeScoped :
      ExecutableFieldsRuntimeScopedBy state.window.schema runtimeType
        (FieldMerge.collectFields state.window.schema validParent
          state.window.selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet)))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source) :
    ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · exact collectFields_pairKeysNodup state.window.schema
      state.window.variableValues state.window.parentType state.window.source
      state.window.selectionSet
  · exact collectFields_fieldCompatible_of_canMerge_runtimeScoped
      state.window.schema state.window.variableValues state.window.parentType
      validParent runtimeType state.window.source state.window.selectionSet
      hmerge hruntimeScoped
  · exact collectFields_argumentsNodup_of_selectionSetValid state.window.schema
      variableDefinitions state.window.variableValues state.window.parentType
      validParent state.window.source state.window.selectionSet hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (initial : Response)
    (variableDefinitions : List VariableDefinition)
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType parentType)
    (hselectionSet :
      Validation.selectionSetValid schema variableDefinitions parentType
        selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType (some identity))) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType (some identity)
          selectionSet := selectionSet }
        initial := initial } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType (some identity)
          selectionSet := selectionSet }
        initial := initial }
      runtimeType variableDefinitions hselectionSet hmerge
  · exact collectFields_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues parentType parentType runtimeType
      identity selectionSet hparentRuntime hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge_optional
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : Option ObjectIdentity)
    (selectionSet : List Selection) (initial : Response)
    (variableDefinitions : List VariableDefinition)
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType parentType)
    (hselectionSet :
      Validation.selectionSetValid schema variableDefinitions parentType
        selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType identity)) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial }
      runtimeType variableDefinitions hselectionSet hmerge
  · exact collectFields_runtimeScopedBy_of_selectionSetValid_object schema
      variableDefinitions variableValues parentType parentType runtimeType
      identity selectionSet hparentRuntime hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : Response)
    (hparentRuntime :
      ScopedParentRuntimeApplies schema runtimeType operation.rootType)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType (some identity))) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := .object runtimeType (some identity)
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge
    schema resolvers variableValues depth operation.rootType runtimeType
    identity operation.selectionSet initial operation.variableDefinitions
    hparentRuntime
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : Response)
    (hroot :
      rootSourceAppliesBool schema operation (.object runtimeType (some identity)) =
        true)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType (some identity))) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := .object runtimeType (some identity)
          selectionSet := operation.selectionSet }
        initial := initial } := by
  exact ExecutionValidFieldSemanticStateInvariant.of_valid_object_operation_canMerge
    schema resolvers variableValues depth operation runtimeType identity initial
    (ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      runtimeType identity hroot)
    hvalid hresolvers

theorem ExecutionCollectedFieldInvariant.of_valid_root_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : Response)
    (hroot :
      rootSourceAppliesBool schema operation (.object runtimeType (some identity)) =
        true)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers
        (.object runtimeType (some identity))) :
    ExecutionCollectedFieldInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := .object runtimeType (some identity)
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply ExecutionCollectedFieldInvariant.of_validFieldSemantic
  exact ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
    schema resolvers variableValues depth operation runtimeType identity
    initial hroot hvalid hresolvers

theorem OperationNoAliasCollision.of_valid_sameScopedParent
    (schema : Schema) (operation : Operation) :
    Validation.operationDefinitionValid schema operation ->
    ScopedFieldsSameResponseParent
      (FieldMerge.collectFields schema operation.rootType
        operation.selectionSet) ->
      OperationNoAliasCollision schema operation := by
  intro hvalid hsameParent
  unfold OperationNoAliasCollision ScopedFieldsNoAliasCollision
  exact fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
    schema operation.rootType operation.selectionSet
    (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
    hsameParent

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_operation_noAliasCollision
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (source : Value ObjectIdentity)
    (initial : Response)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hnoAlias : OperationNoAliasCollision schema operation)
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers source) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := source
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := operation.rootType
        source := source
        selectionSet := operation.selectionSet }
      initial := initial }
    operation.variableDefinitions
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact ScopedFieldsNoAliasCollision.fieldCompatible
      (FieldMerge.collectFields schema operation.rootType operation.selectionSet)
      hnoAlias
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_operation_sameScopedParent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (source : Value ObjectIdentity)
    (initial : Response)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hsameParent :
      ScopedFieldsSameResponseParent
        (FieldMerge.collectFields schema operation.rootType
          operation.selectionSet))
    (hresolvers :
      ResolversRespectValidFieldAndArgumentEquivalence resolvers source) :
    ExecutionValidFieldSemanticStateInvariant
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := operation.rootType
          source := source
          selectionSet := operation.selectionSet }
        initial := initial } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_operation_noAliasCollision
      schema resolvers variableValues depth operation source initial hvalid
  · exact OperationNoAliasCollision.of_valid_sameScopedParent schema operation
      hvalid hsameParent
  · exact hresolvers

theorem executeCollectedFields_collectFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    PairKeysNodup
      (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        depth source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)) :=
  executeCollectedFields_pairKeysNodup schema resolvers variableValues depth
    source
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (collectFields_pairKeysNodup schema variableValues parentType source
      selectionSet)

theorem executeRootSelectionSet_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    PairKeysNodup
      (executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet) := by
  unfold executeRootSelectionSet
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  have hnodup :
      PairKeysNodup fields := by
    simpa [hfields] using
      visitSubfields_pairKeysNodup schema resolvers variableValues depth
        parentType source selectionSet [] (by simp [PairKeysNodup])
  simp [hfields, hnodup]

theorem executeRootSelectionSet_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection) :
    ResponseMergeReady
      (.object
        (executeRootSelectionSet schema resolvers variableValues depth
          parentType source selectionSet)) := by
  unfold executeRootSelectionSet
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  have hready :
      ResponseMergeReady (.object fields) := by
    simpa [hfields] using
      visitSubfields_response_ready schema resolvers variableValues depth
        parentType source selectionSet [] ResponseMergeReady_empty_object
  simp [hfields, hready]

theorem ExecutionWindowEquivalent.ext
    (window : ExecutionWindow ObjectIdentity)
    (hfields :
      window.ungroupedResponseFields = window.specResponseFields) :
    ExecutionWindowEquivalent window := by
  change window.ungroupedResponse = window.specResponse
  simp [ExecutionWindow.ungroupedResponse, ExecutionWindow.specResponse,
    hfields]

theorem ExecutionStateEquivalent.ext
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hresponse : state.ungroupedProjection = state.specProjection) :
    ExecutionStateEquivalent state := by
  simpa [ExecutionStateEquivalent, ResponseDataEquivalent] using hresponse

theorem stateEquivalent_of_executeRootSelectionSet_eq_spec
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
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  apply ExecutionStateEquivalent.ext
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  have hfieldsEq :
      fields =
        GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues depth parentType source selectionSet := by
    unfold executeRootSelectionSet at hroot
    simpa [hfields] using hroot
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection, hfields]
  rw [mergeResponse_empty_object_left_of_pairKeysNodup]
  exact congrArg Response.object hfieldsEq
  exact
    executeCollectedFields_collectFields_pairKeysNodup schema resolvers
      variableValues depth parentType source selectionSet

theorem stateEquivalent_of_appendState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left right : List Selection)
    (state :
      ExecutedAppendSelectionState schema resolvers variableValues depth
        parentType source left right) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left ++ right }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source (left ++ right)
    (executeRootSelectionSet_eq_spec_of_appendState schema resolvers
      variableValues depth parentType source left right state)

theorem stateEquivalent_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        parentType source selectionSet (.object [])) :
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
    (executeRootSelectionSet_eq_spec_of_exact_empty_group schema resolvers
      variableValues depth parentType source selectionSet hcollect hdirect)

theorem executeRootSelectionSet_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate :
      ExecutionStateEquivalent
        { window := window, initial := .object [] })
    (hmerge :
      mergeResponse (.object [])
        (.object
          (GraphQL.Execution.executeCollectedFields window.schema
            window.resolvers window.variableValues window.depth window.source
            (GraphQL.Execution.collectFields window.schema window.variableValues
              window.parentType window.source window.selectionSet))) =
      .object
        (GraphQL.Execution.executeCollectedFields window.schema
          window.resolvers window.variableValues window.depth window.source
          (GraphQL.Execution.collectFields window.schema window.variableValues
            window.parentType window.source window.selectionSet))) :
    window.ungroupedResponseFields = window.specResponseFields := by
  unfold ExecutionStateEquivalent ResponseDataEquivalent at hstate
  simp [ExecutionEquivalenceState.ungroupedProjection,
    ExecutionEquivalenceState.specProjection, hmerge] at hstate
  unfold ExecutionWindow.ungroupedResponseFields
  unfold ExecutionWindow.specResponseFields
  simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet]
  cases hvisit :
    visitSubfields window.schema window.resolvers window.variableValues
      window.depth window.parentType window.source window.selectionSet (.object []) <;>
    simp [hvisit] at hstate ⊢
  exact hstate

theorem executeRootSelectionSet_eq_spec_of_state_equivalent_nodup
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate :
      ExecutionStateEquivalent
        { window := window, initial := .object [] })
    (hnodup :
      PairKeysNodup
        (GraphQL.Execution.executeCollectedFields window.schema
          window.resolvers window.variableValues window.depth window.source
          (GraphQL.Execution.collectFields window.schema window.variableValues
            window.parentType window.source window.selectionSet))) :
    window.ungroupedResponseFields = window.specResponseFields :=
  executeRootSelectionSet_eq_spec_of_state_equivalent window hstate
    (mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFields window.schema
        window.resolvers window.variableValues window.depth window.source
        (GraphQL.Execution.collectFields window.schema window.variableValues
          window.parentType window.source window.selectionSet))
      hnodup)

theorem executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate :
      ExecutionStateEquivalent
        { window := window, initial := .object [] }) :
    window.ungroupedResponseFields = window.specResponseFields :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_nodup window hstate
    (executeCollectedFields_collectFields_pairKeysNodup window.schema
      window.resolvers window.variableValues window.depth window.parentType
      window.source window.selectionSet)

theorem ExecutedAppendSelectionState.of_stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left right : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hright :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := right }
          initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right))
    (hrightAppends :
      visitSubfields schema resolvers variableValues depth parentType source
        right
        (.object
          (executeRootSelectionSet schema resolvers variableValues depth
            parentType source left)) =
      .object
        (executeRootSelectionSet schema resolvers variableValues depth
          parentType source left ++
         executeRootSelectionSet schema resolvers variableValues depth
          parentType source right)) :
    ExecutedAppendSelectionState schema resolvers variableValues depth
      parentType source left right := by
  refine
    { leftEquivalent := ?_
      rightEquivalent := ?_
      namesDisjoint := hdisjoint
      rightAppends := hrightAppends }
  · simpa [ExecutionWindow.ungroupedResponseFields,
      ExecutionWindow.specResponseFields] using
      executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left }
        hleft
  · simpa [ExecutionWindow.ungroupedResponseFields,
      ExecutionWindow.specResponseFields] using
      executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := right }
        hright

theorem ExecutedAppendSelectionState.of_stateEquivalent_single_fresh_field
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hright :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet :=
              [.field responseName fieldName arguments directives selectionSet] }
          initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh :
      responseName ∉
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source left).map Prod.fst) :
    ExecutedAppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      [.field responseName fieldName arguments directives selectionSet] := by
  apply ExecutedAppendSelectionState.of_stateEquivalent hleft hright hdisjoint
  exact
    visitSubfields_single_field_allowed_succ_fresh_appends_executeRootSelectionSet
      schema resolvers variableValues depth parentType source responseName
      fieldName arguments directives selectionSet
      (executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source left)
      hallowed hfresh

theorem stateEquivalent_of_append_single_fresh_field
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hright :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet :=
              [.field responseName fieldName arguments directives selectionSet] }
          initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh :
      responseName ∉
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source left).map Prod.fst) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.field responseName fieldName arguments directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_appendState schema resolvers variableValues (depth + 1)
    parentType source left
    [.field responseName fieldName arguments directives selectionSet]
    (ExecutedAppendSelectionState.of_stateEquivalent_single_fresh_field hleft
      hright hdisjoint hallowed hfresh)

theorem executeRootSelectionSet_eq_spec_of_append_single_fresh_field
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hright :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet :=
              [.field responseName fieldName arguments directives selectionSet] }
          initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh :
      responseName ∉
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source left).map Prod.fst) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet :=
        left ++ [.field responseName fieldName arguments directives selectionSet] }
    (stateEquivalent_of_append_single_fresh_field hleft hright hdisjoint
      hallowed hfresh)

theorem stateEquivalent_of_append_single_field_of_disjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hright :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet :=
              [.field responseName fieldName arguments directives selectionSet] }
          initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.field responseName fieldName arguments directives selectionSet] }
        initial := .object [] } := by
  have hleftEq :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source left =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source left := by
    simpa [ExecutionWindow.ungroupedResponseFields,
      ExecutionWindow.specResponseFields] using
      executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := left }
        hleft
  exact stateEquivalent_of_append_single_fresh_field hleft hright hdisjoint
    hallowed
    (responseName_fresh_of_disjoint_single_field schema resolvers
      variableValues (depth + 1) parentType source left responseName fieldName
      arguments directives selectionSet hleftEq hdisjoint hallowed)

theorem executeRootSelectionSet_eq_spec_of_append_single_field_of_disjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hright :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth + 1
            parentType := parentType
            source := source
            selectionSet :=
              [.field responseName fieldName arguments directives selectionSet] }
          initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet :=
        left ++ [.field responseName fieldName arguments directives selectionSet] }
    (stateEquivalent_of_append_single_field_of_disjoint hleft hright
      hdisjoint hallowed)

theorem executeRootSelectionSet_append_single_field_blocked_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source left := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [hfields]
  simp [visitSubfields,
    visitSelection_field_directives_blocked schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet (.object fields) hblocked]

theorem specExecuteRootSelectionSet_append_single_field_blocked_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source left := by
  simp [GraphQL.Execution.executeRootSelectionSet]
  rw [GraphQL.NormalForm.collectFields_append]
  simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups, hblocked]

theorem executeRootSelectionSet_eq_spec_of_append_single_field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.field responseName fieldName arguments directives selectionSet]) := by
  have hleftEq :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source left =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left := by
    simpa [ExecutionWindow.ungroupedResponseFields,
      ExecutionWindow.specResponseFields] using
      executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left }
        hleft
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source left := by
        exact executeRootSelectionSet_append_single_field_blocked_eq_left
          schema resolvers variableValues depth parentType source left
          responseName fieldName arguments directives selectionSet hblocked
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left := hleftEq
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) := by
        rw [specExecuteRootSelectionSet_append_single_field_blocked_eq_left
          schema resolvers variableValues depth parentType source left
          responseName fieldName arguments directives selectionSet hblocked]

theorem stateEquivalent_of_append_single_field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.field responseName fieldName arguments directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.field responseName fieldName arguments directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_field_blocked hleft
      hblocked)

theorem executeRootSelectionSet_append_single_selection_noop_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection) (selection : Selection)
    (hvisit :
      ∀ fields,
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object fields) = .object fields) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [selection]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source left := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [hfields]
  simp [visitSubfields, hvisit fields]

theorem specExecuteRootSelectionSet_append_single_selection_noop_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection) (selection : Selection)
    (hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType
        source selection = []) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ [selection]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source left := by
  simp [GraphQL.Execution.executeRootSelectionSet]
  rw [GraphQL.NormalForm.collectFields_append]
  simp [GraphQL.Execution.collectFields, GraphQL.Execution.mergeExecutableGroups,
    hcollect]

theorem executeRootSelectionSet_eq_spec_of_append_single_selection_noop
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hvisit :
      ∀ fields,
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object fields) = .object fields)
    (hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType
        source selection = []) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [selection]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ [selection]) := by
  have hleftEq :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source left =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left := by
    simpa [ExecutionWindow.ungroupedResponseFields,
      ExecutionWindow.specResponseFields] using
      executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left }
        hleft
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [selection]) =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source left := by
        exact executeRootSelectionSet_append_single_selection_noop_eq_left
          schema resolvers variableValues depth parentType source left selection
          hvisit
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source left := hleftEq
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ [selection]) := by
        rw [specExecuteRootSelectionSet_append_single_selection_noop_eq_left
          schema resolvers variableValues depth parentType source left selection
          hcollect]

theorem stateEquivalent_of_append_single_selection_noop
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hvisit :
      ∀ fields,
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object fields) = .object fields)
    (hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType
        source selection = []) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left ++ [selection] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source (left ++ [selection])
    (executeRootSelectionSet_eq_spec_of_append_single_selection_noop hleft
      hvisit hcollect)

theorem stateEquivalent_of_append_single_inline_none_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++ [.inlineFragment none directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_none_directives_blocked schema resolvers
        variableValues depth parentType source directives selectionSet
        (.object fields) hblocked)
    (by
      simp [GraphQL.Execution.collectSelection, hblocked])

theorem stateEquivalent_of_append_single_inline_some_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.inlineFragment (some typeCondition) directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_some_directives_blocked schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet (.object fields) hblocked)
    (by
      simp [GraphQL.Execution.collectSelection, hblocked])

theorem stateEquivalent_of_append_single_inline_some_not_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hallowed :
      selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        false) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.inlineFragment (some typeCondition) directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_some_type_not_apply schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet (.object fields) hallowed hnotApply)
    (by
      simp [GraphQL.Execution.collectSelection, hallowed, hnotApply])

theorem executeRootSelectionSet_append_single_inline_none_allowed_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left selectionSet : List Selection)
    (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [.inlineFragment none directives selectionSet]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ selectionSet) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [visitSubfields_append_equivalence]
  rw [hfields]
  simp [visitSubfields, visitSelection, hallowed]

theorem specExecuteRootSelectionSet_append_single_inline_none_allowed_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left selectionSet : List Selection)
    (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment none directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ selectionSet) := by
  simp [GraphQL.Execution.executeRootSelectionSet]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [GraphQL.NormalForm.collectFields_append]
  simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups, hallowed]

theorem executeRootSelectionSet_eq_spec_of_append_single_inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left selectionSet : List Selection}
    {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ [.inlineFragment none directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment none directives selectionSet]) := by
  have hbodyEq :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ selectionSet) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ selectionSet) := by
    simpa [ExecutionWindow.ungroupedResponseFields,
      ExecutionWindow.specResponseFields] using
      executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left ++ selectionSet }
        hbody
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [.inlineFragment none directives selectionSet]) =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ selectionSet) := by
        exact
          executeRootSelectionSet_append_single_inline_none_allowed_eq_body_append
            schema resolvers variableValues depth parentType source left
            selectionSet directives hallowed
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ selectionSet) := hbodyEq
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++ [.inlineFragment none directives selectionSet]) := by
        rw [specExecuteRootSelectionSet_append_single_inline_none_allowed_eq_body_append
          schema resolvers variableValues depth parentType source left
          selectionSet directives hallowed]

theorem stateEquivalent_of_append_single_inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left selectionSet : List Selection}
    {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++ [.inlineFragment none directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.inlineFragment none directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_inline_none_allowed
      hbody hallowed)

theorem executeRootSelectionSet_append_single_inline_some_apply_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left selectionSet : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (left ++ selectionSet) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [visitSubfields_append_equivalence]
  rw [hfields]
  simp [visitSubfields, visitSelection, hallowed, happly]

theorem specExecuteRootSelectionSet_append_single_inline_some_apply_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left selectionSet : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (left ++ selectionSet) := by
  simp [GraphQL.Execution.executeRootSelectionSet]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [GraphQL.NormalForm.collectFields_append]
  simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups, hallowed, happly]

theorem executeRootSelectionSet_eq_spec_of_append_single_inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left selectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source
      (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) := by
  have hbodyEq :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ selectionSet) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ selectionSet) := by
    simpa [ExecutionWindow.ungroupedResponseFields,
      ExecutionWindow.specResponseFields] using
      executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left ++ selectionSet }
        hbody
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (left ++
          [.inlineFragment (some typeCondition) directives selectionSet]) =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ selectionSet) := by
        exact
          executeRootSelectionSet_append_single_inline_some_apply_eq_body_append
            schema resolvers variableValues depth parentType source left
            selectionSet typeCondition directives hallowed happly
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ selectionSet) := hbodyEq
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++
          [.inlineFragment (some typeCondition) directives selectionSet]) := by
        rw [specExecuteRootSelectionSet_append_single_inline_some_apply_eq_body_append
          schema resolvers variableValues depth parentType source left
          selectionSet typeCondition directives hallowed happly]

theorem stateEquivalent_of_append_single_inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left selectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            left ++
              [.inlineFragment (some typeCondition) directives selectionSet] }
        initial := .object [] } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_inline_some_apply
      hbody hallowed happly)

structure AppendAllowedFieldState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection) (childDepth : Nat) : Prop where
  depth_eq : depth = childDepth + 1
  allowed : selectionDirectivesAllowBool variableValues directives = true
  rightEquivalent :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet :=
            [.field responseName fieldName arguments directives selectionSet] }
        initial := .object [] }
  namesDisjoint :
    GraphQL.NormalForm.executableGroupNamesDisjoint
      (GraphQL.Execution.collectFields schema variableValues parentType
        source left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        [.field responseName fieldName arguments directives selectionSet])

def AppendSelectionState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left : List Selection) : Selection -> Prop
  | .field responseName fieldName arguments directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false ∨
      depth = 0 ∨
      ∃ childDepth,
        AppendAllowedFieldState schema resolvers variableValues depth parentType
          source left responseName fieldName arguments directives selectionSet
          childDepth
  | .inlineFragment none directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false ∨
      selectionDirectivesAllowBool variableValues directives = true ∧
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] }
  | .inlineFragment (some typeCondition) directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false ∨
      (selectionDirectivesAllowBool variableValues directives = true ∧
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          false) ∨
      (selectionDirectivesAllowBool variableValues directives = true ∧
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          true ∧
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := left ++ selectionSet }
            initial := .object [] })

theorem AppendSelectionState.field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.field responseName fieldName arguments directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.field_depth_zero
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection} :
    AppendSelectionState schema resolvers variableValues 0 parentType
      source left
      (.field responseName fieldName arguments directives selectionSet) := by
  simp [AppendSelectionState]

theorem AppendSelectionState.field_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth childDepth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hstate :
      AppendAllowedFieldState schema resolvers variableValues depth parentType
        source left responseName fieldName arguments directives selectionSet
        childDepth) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.field responseName fieldName arguments directives selectionSet) := by
  simp [AppendSelectionState]
  right
  exact Or.inr ⟨childDepth, hstate⟩

theorem AppendSelectionState.inline_none_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left (.inlineFragment none directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] }) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left (.inlineFragment none directives selectionSet) := by
  simp [AppendSelectionState, hallowed, hbody]

theorem AppendSelectionState.inline_some_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked :
      selectionDirectivesAllowBool variableValues directives = false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.inline_some_not_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        false) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hallowed, hnotApply]

theorem AppendSelectionState.inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true)
    (hbody :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          initial := .object [] }) :
    AppendSelectionState schema resolvers variableValues depth parentType
      source left
      (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hallowed, happly, hbody]

theorem stateEquivalent_of_append_single_selection_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} (selection : Selection)
    (hleft :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] })
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := left ++ [selection] }
        initial := .object [] } := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simp [AppendSelectionState] at hselection
      rcases hselection with hblocked | hrest
      · exact stateEquivalent_of_append_single_field_blocked hleft hblocked
      rcases hrest with hzero | hallowedStep
      · subst depth
        exact depthZeroStateEquivalent schema resolvers variableValues
          parentType source
          (left ++
            [.field responseName fieldName arguments directives selectionSet])
          (.object [])
      · rcases hallowedStep with ⟨childDepth, hstep⟩
        rcases hstep with ⟨hdepth, hallowed, hright, hdisjoint⟩
        subst depth
        exact stateEquivalent_of_append_single_field_of_disjoint hleft hright
          hdisjoint hallowed
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          simp [AppendSelectionState] at hselection
          rcases hselection with hblocked | hallowedBody
          · exact stateEquivalent_of_append_single_inline_none_blocked hleft
              hblocked
          · rcases hallowedBody with ⟨hallowed, hbody⟩
            exact stateEquivalent_of_append_single_inline_none_allowed hbody
              hallowed
      | some typeCondition =>
          simp [AppendSelectionState] at hselection
          rcases hselection with hblocked | hnotApplyStep | happlyStep
          · exact stateEquivalent_of_append_single_inline_some_blocked hleft
              hblocked
          · rcases hnotApplyStep with ⟨hallowed, hnotApply⟩
            exact stateEquivalent_of_append_single_inline_some_not_apply hleft
              hallowed hnotApply
          · rcases happlyStep with ⟨hallowed, happly, hbody⟩
            exact stateEquivalent_of_append_single_inline_some_apply hbody
              hallowed happly

def AppendSelectionSetState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity) :
    List Selection -> List Selection -> Prop
  | _left, [] => True
  | left, selection :: rest =>
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection ∧
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source (left ++ [selection]) rest

theorem AppendSelectionSetState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} :
    AppendSelectionSetState schema resolvers variableValues depth parentType
      source left [] := by
  simp [AppendSelectionSetState]

theorem AppendSelectionSetState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {selection : Selection} {rest : List Selection}
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection)
    (hrest :
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source (left ++ [selection]) rest) :
    AppendSelectionSetState schema resolvers variableValues depth parentType
      source left (selection :: rest) := by
  exact ⟨hselection, hrest⟩

def AppendSelectionSetPrefixState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (left selectionSet : List Selection) : Prop :=
  ∀ prefixSelections selection suffix,
    selectionSet = prefixSelections ++ selection :: suffix ->
      AppendSelectionState schema resolvers variableValues depth parentType
        source (left ++ prefixSelections) selection

theorem AppendSelectionSetPrefixState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} :
    AppendSelectionSetPrefixState schema resolvers variableValues depth
      parentType source left [] := by
  intro prefixSelections selection suffix hselectionSet
  have hlength := congrArg List.length hselectionSet
  simp at hlength

theorem AppendSelectionSetPrefixState.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection) :
    AppendSelectionSetPrefixState schema resolvers variableValues depth
      parentType source left [selection] := by
  intro prefixSelections nextSelection suffix hselectionSet
  cases prefixSelections with
  | nil =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, rfl⟩
      simpa using hselection
  | cons _head _tail =>
      have hlength := congrArg List.length hselectionSet
      simp at hlength

theorem AppendSelectionSetPrefixState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection} {selection : Selection}
    {rest : List Selection}
    (hselection :
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection)
    (hrest :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source (left ++ [selection]) rest) :
    AppendSelectionSetPrefixState schema resolvers variableValues depth
      parentType source left (selection :: rest) := by
  intro prefixSelections nextSelection suffix hselectionSet
  cases prefixSelections with
  | nil =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, _hrest⟩
      simpa using hselection
  | cons head tail =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, hrestSet⟩
      have hstep := hrest tail nextSelection suffix hrestSet
      simpa [List.append_assoc] using hstep

theorem AppendSelectionSetState.of_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity} :
    ∀ (left selectionSet : List Selection),
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source left selectionSet ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left selectionSet
  | _left, [], _hstate => by
      exact AppendSelectionSetState.nil
  | left, selection :: rest, hstate => by
      apply AppendSelectionSetState.cons
      · simpa using hstate [] selection rest rfl
      · apply AppendSelectionSetState.of_prefix_state
        intro prefixSelections tailSelection suffix htail
        have hselectionSet :
            selection :: rest =
              (selection :: prefixSelections) ++ tailSelection :: suffix := by
          simp [htail]
        have hstep :=
          hstate (selection :: prefixSelections) tailSelection suffix hselectionSet
        simpa [List.append_assoc] using hstep

theorem AppendSelectionSetState.append
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity} :
    ∀ (left middle right : List Selection),
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left middle ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source (left ++ middle) right ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left (middle ++ right)
  | _left, [], right, _hmiddle, hright => by
      simpa using hright
  | left, selection :: rest, right, hmiddle, hright => by
      rcases hmiddle with ⟨hselection, hrest⟩
      apply AppendSelectionSetState.cons hselection
      apply AppendSelectionSetState.append (left ++ [selection]) rest right hrest
      simpa [List.append_assoc] using hright

theorem stateEquivalent_of_append_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity} :
    ∀ (left right : List Selection),
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          initial := .object [] } ->
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source left right ->
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ right }
          initial := .object [] }
  | left, [], hleft, _hstate => by
      simpa using hleft
  | left, selection :: rest, hleft, hstate => by
      simp [AppendSelectionSetState] at hstate
      rcases hstate with ⟨hselection, hrest⟩
      have hfirst :
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ [selection] }
              initial := .object [] } :=
        stateEquivalent_of_append_single_selection_state selection hleft
          hselection
      have htail :=
        stateEquivalent_of_append_selectionSet_state
          (left ++ [selection]) rest hfirst hrest
      simpa [List.append_assoc] using htail

theorem stateEquivalent_of_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source [] selectionSet) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  simpa using
    stateEquivalent_of_append_selectionSet_state
      ([] : List Selection) selectionSet
      (emptySelectionStateEquivalent schema resolvers variableValues depth
        parentType source (.object []))
      hstate

theorem stateEquivalent_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source [] selectionSet) :
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
  stateEquivalent_of_selectionSet_state
    (AppendSelectionSetState.of_prefix_state [] selectionSet hstate)

theorem executeRootSelectionSet_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetState schema resolvers variableValues depth parentType
        source [] selectionSet) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth
      parentType := parentType
      source := source
      selectionSet := selectionSet }
    (stateEquivalent_of_selectionSet_state hstate)

theorem executeRootSelectionSet_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {selectionSet : List Selection}
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source [] selectionSet) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_selectionSet_state
    (AppendSelectionSetState.of_prefix_state [] selectionSet hstate)

theorem executeQueryAtDepth_eq_spec_of_root_fields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hfields :
      executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth operation.rootType source operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  simp [executeQueryAtDepth, GraphQL.Execution.executeQueryAtDepth, hroot,
    hfields]

theorem executeQueryAtDepth_eq_spec_of_root_false
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = false) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  simp [executeQueryAtDepth, GraphQL.Execution.executeQueryAtDepth, hroot]

theorem executeQueryAtDepth_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact
    executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := operation.rootType
        source := source
        selectionSet := operation.selectionSet }
      hstate

theorem executeQueryAtDepth_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetState schema resolvers variableValues depth
        operation.rootType source [] operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source :=
  executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation depth source hroot
    (stateEquivalent_of_selectionSet_state hstate)

theorem executeQueryAtDepth_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues depth
        operation.rootType source [] operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source :=
  executeQueryAtDepth_eq_spec_of_selectionSet_state schema resolvers
    variableValues operation depth source hroot
    (AppendSelectionSetState.of_prefix_state [] operation.selectionSet hstate)

theorem executeQueryAtDepth_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hflat :
      executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth operation.rootType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues
              operation.rootType source operation.selectionSet)))) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact executeRootSelectionSet_eq_spec_of_flattened_collectFields_eq schema
    resolvers variableValues depth operation.rootType source
    operation.selectionSet hflat

theorem executeQueryAtDepth_eq_spec_of_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        operation.rootType source operation.selectionSet (.object []))
    (hflatSpec :
      ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
        operation.rootType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues
            operation.rootType source operation.selectionSet))) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact executeRootSelectionSet_eq_spec_of_flatCollects_and_flatSpecEquivalent
    schema resolvers variableValues depth operation.rootType source
    operation.selectionSet hdirect hflatSpec

theorem executeQueryAtDepth_eq_spec_of_group_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        operation.rootType source operation.selectionSet (.object []))
    (hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        operation.rootType source
        (GraphQL.Execution.collectFields schema variableValues operation.rootType
          source operation.selectionSet)) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet hdirect hgroups

theorem executeQueryAtDepth_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues depth
        operation.rootType source operation.selectionSet (.object [])) :
    executeQueryAtDepth schema resolvers variableValues operation depth source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues operation
      depth source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation depth source hroot
  exact stateEquivalent_of_exact_empty_group schema resolvers variableValues
    depth operation.rootType source operation.selectionSet hcollect hdirect

theorem executeQuery_eq_spec_of_root_fields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hfields :
      executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers variableValues
    operation (GraphQL.Execution.executeQueryDepthBound operation) source hroot
    hfields

theorem executeQuery_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := GraphQL.Execution.executeQueryDepthBound operation
            parentType := operation.rootType
            source := source
            selectionSet := operation.selectionSet }
          initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hstate

theorem executeQuery_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetState schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source [] operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_selectionSet_state schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hstate

theorem executeQuery_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate :
      AppendSelectionSetPrefixState schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source [] operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact
    executeQueryAtDepth_eq_spec_of_selectionSet_prefix_state schema resolvers
      variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
      source hroot hstate

theorem executeQuery_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hflat :
      executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues
              operation.rootType source operation.selectionSet)))) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_flattened_collectFields_eq schema
    resolvers variableValues operation
    (GraphQL.Execution.executeQueryDepthBound operation) source hroot hflat

theorem executeQuery_eq_spec_of_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet (.object []))
    (hflatSpec :
      ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues
            operation.rootType source operation.selectionSet))) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_flat_predicates schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hdirect hflatSpec

theorem executeQuery_eq_spec_of_group_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet (.object []))
    (hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source
        (GraphQL.Execution.collectFields schema variableValues operation.rootType
          source operation.selectionSet)) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_group_flat_predicates schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hdirect hgroups

theorem executeQuery_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : Value ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (GraphQL.Execution.executeQueryDepthBound operation)
        operation.rootType source operation.selectionSet (.object [])) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryAtDepth_eq_spec_of_exact_empty_group schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryDepthBound operation)
    source hroot hcollect hdirect

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hcomplete :
      completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        selectionSet
        (resolvers.resolve parentType fieldName arguments source)
        .null =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        [executableField parentType responseName fieldName arguments
          selectionSet]
        (resolvers.resolve parentType fieldName arguments source)) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
    GraphQL.Execution.executeRootSelectionSet, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
    GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
    executableField, responseObjectField?, lookupResponseField?,
    mergeResponseFieldIntoObject, mergeResponseField, hallowed, hcomplete]

theorem executeRootSelectionSet_duplicate_field_succ_eq_spec_of_completeValue_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (firstSelectionSet secondSelectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
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
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [ .field responseName fieldName arguments directives firstSelectionSet
      , .field responseName fieldName arguments directives secondSelectionSet ] := by
  simp [executeRootSelectionSet, visitSubfields, visitSelection, executeField,
    GraphQL.Execution.executeRootSelectionSet, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
    GraphQL.Execution.addExecutableGroup,
    GraphQL.Execution.executeCollectedFields, GraphQL.Execution.executeField,
    executableField, responseObjectField?, lookupResponseField?,
    mergeResponseFieldIntoObject, mergeResponseField, hallowed, hresolve,
    hcomplete]

theorem completeValue_duplicate_object_merge_eq_spec_of_child_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true)
    (hchild :
      mergeResponse
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType (some identity)) firstSelectionSet (.object []))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          secondSelectionSet (.object runtimeType (some identity))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType (some identity)) firstSelectionSet (.object []))) =
      .object
        (GraphQL.Execution.executeCollectedFields schema resolvers
          variableValues childDepth (.object runtimeType (some identity))
          (GraphQL.Execution.collectSubfields schema variableValues runtimeType
            (.object runtimeType (some identity))
            [ executableField parentType responseName fieldName arguments
                firstSelectionSet
            , executableField parentType responseName fieldName arguments
                secondSelectionSet ]))) :
    mergeResponse
      (completeValue schema resolvers variableValues (childDepth + 1)
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        firstSelectionSet (.object runtimeType (some identity)) .null)
      (completeValue schema resolvers variableValues (childDepth + 1)
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        secondSelectionSet (.object runtimeType (some identity))
        (completeValue schema resolvers variableValues (childDepth + 1)
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          firstSelectionSet (.object runtimeType (some identity)) .null)) =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 1)
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      [ executableField parentType responseName fieldName arguments
          firstSelectionSet
      , executableField parentType responseName fieldName arguments
          secondSelectionSet ]
      (.object runtimeType (some identity)) := by
  simpa [completeValue, GraphQL.Execution.completeValue, hincludes] using hchild

theorem completeValue_object_single_field_eq_spec_of_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType (some identity)
            selectionSet := selectionSet }
          initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 1)
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      selectionSet (.object runtimeType (some identity)) .null =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 1)
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      [executableField parentType responseName fieldName arguments
        selectionSet]
      (.object runtimeType (some identity)) := by
  by_cases hincludes :
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        runtimeType = true
  · unfold ExecutionStateEquivalent ResponseDataEquivalent at hchild
    simp [ExecutionEquivalenceState.ungroupedProjection,
      ExecutionEquivalenceState.specProjection,
      mergeResponse_empty_object_left_of_pairKeysNodup
        (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          childDepth (.object runtimeType (some identity))
          (GraphQL.Execution.collectFields schema variableValues runtimeType
            (.object runtimeType (some identity)) selectionSet))
        (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
          variableValues childDepth runtimeType (.object runtimeType (some identity))
          selectionSet)] at hchild
    simpa [completeValue, GraphQL.Execution.completeValue,
      GraphQL.Execution.collectSubfields, GraphQL.Execution.mergeExecutableGroups,
      executableField, hincludes] using hchild
  · have hnotIncludes :
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          runtimeType = false := by
      cases h :
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            runtimeType <;>
        simp [h] at hincludes ⊢
    simp [completeValue, GraphQL.Execution.completeValue, executableField,
      hnotIncludes]

theorem completeValue_object_group_eq_spec_of_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : Option ObjectIdentity)
    (fields : List ExecutableField)
    (hchild :
      ExecutionStateEquivalent
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := childDepth
            parentType := runtimeType
            source := .object runtimeType identity
            selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
          initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 1)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.object runtimeType identity) .null =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 1) parentType fields (.object runtimeType identity) := by
  by_cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true
  · unfold ExecutionStateEquivalent ResponseDataEquivalent at hchild
    simp [ExecutionEquivalenceState.ungroupedProjection,
      ExecutionEquivalenceState.specProjection,
      mergeResponse_empty_object_left_of_pairKeysNodup
        (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          childDepth (.object runtimeType identity)
          (GraphQL.Execution.collectFields schema variableValues runtimeType
            (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet fields)))
        (executeCollectedFields_collectFields_pairKeysNodup schema resolvers
          variableValues childDepth runtimeType (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet fields))] at hchild
    simpa [completeValue, GraphQL.Execution.completeValue,
      GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
      hincludes] using hchild
  · have hnotIncludes :
        schema.typeIncludesObjectBool parentType runtimeType = false := by
      cases h :
          schema.typeIncludesObjectBool parentType runtimeType <;>
        simp [h] at hincludes ⊢
    simp [completeValue, GraphQL.Execution.completeValue, hnotIncludes]

theorem completeValue_object_group_eq_spec_of_guarded_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : Option ObjectIdentity)
    (fields : List ExecutableField)
    (hchild :
      schema.typeIncludesObjectBool parentType runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
            initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 1)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.object runtimeType identity) .null =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 1) parentType fields (.object runtimeType identity) := by
  by_cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true
  · exact completeValue_object_group_eq_spec_of_merged_child_state schema
      resolvers variableValues childDepth parentType runtimeType identity fields
      (hchild hincludes)
  · have hnotIncludes :
        schema.typeIncludesObjectBool parentType runtimeType = false := by
      cases h :
          schema.typeIncludesObjectBool parentType runtimeType <;>
        simp [h] at hincludes ⊢
    simp [completeValue, GraphQL.Execution.completeValue, hnotIncludes]

theorem completeValue_object_list_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    (objects : List (Name × Option ObjectIdentity))
    (hchildren :
      ∀ object, object ∈ objects ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := object.fst
              source := .object object.fst object.snd
              selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
            initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 2)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : Value ObjectIdentity))))
      .null =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 2) parentType fields
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : Value ObjectIdentity)))) := by
  apply completeValue_list_empty_previous_eq_spec_of_values schema resolvers
    variableValues (childDepth + 1) parentType
    (GraphQL.Execution.mergedFieldSelectionSet fields) fields
  intro value hmem
  rcases List.mem_map.mp hmem with ⟨object, hobject, hvalue⟩
  rw [← hvalue]
  exact completeValue_object_group_eq_spec_of_merged_child_state schema
    resolvers variableValues childDepth parentType object.fst object.snd
    fields (hchildren object hobject)

theorem completeValue_object_list_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    (objects : List (Name × Option ObjectIdentity))
    (hchildren :
      ∀ object, object ∈ objects ->
        schema.typeIncludesObjectBool parentType object.fst = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := object.fst
                source := .object object.fst object.snd
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) :
    completeValue schema resolvers variableValues (childDepth + 2)
      parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : Value ObjectIdentity))))
      .null =
    GraphQL.Execution.completeValue schema resolvers variableValues
      (childDepth + 2) parentType fields
      (.list
        (objects.map
          (fun object => (.object object.fst object.snd : Value ObjectIdentity)))) := by
  apply completeValue_list_empty_previous_eq_spec_of_values schema resolvers
    variableValues (childDepth + 1) parentType
    (GraphQL.Execution.mergedFieldSelectionSet fields) fields
  intro value hmem
  rcases List.mem_map.mp hmem with ⟨object, hobject, hvalue⟩
  rw [← hvalue]
  exact
    completeValue_object_group_eq_spec_of_guarded_merged_child_state schema
      resolvers variableValues childDepth parentType object.fst object.snd
      fields (hchildren object hobject)

theorem completeValue_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField) :
    ∀ (depth : Nat) (parentType : Name) (value : Value ObjectIdentity),
      (∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields) value .null =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value := by
  intro depth
  induction depth with
  | zero =>
      intro parentType value _hchildren
      simp [completeValue, GraphQL.Execution.completeValue]
  | succ depth ih =>
      intro parentType value hchildren
      cases value with
      | null =>
          simp [completeValue, GraphQL.Execution.completeValue]
      | scalar value =>
          simp [completeValue, GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact completeValue_object_group_eq_spec_of_merged_child_state schema
            resolvers variableValues depth parentType runtimeType identity
            fields (hchildren depth runtimeType identity
              (Nat.lt_succ_self depth))
      | list values =>
          apply completeValue_list_empty_previous_eq_spec_of_values schema
            resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet fields) fields
          intro value hmem
          exact ih parentType value
            (by
              intro childDepth runtimeType identity hlt
              exact hchildren childDepth runtimeType identity
                (Nat.lt_trans hlt (Nat.lt_succ_self depth)))

theorem completeValue_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField) :
    ∀ (depth : Nat) (parentType : Name) (value : Value ObjectIdentity),
      (∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields) value .null =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value := by
  intro depth
  induction depth with
  | zero =>
      intro parentType value _hchildren
      simp [completeValue, GraphQL.Execution.completeValue]
  | succ depth ih =>
      intro parentType value hchildren
      cases value with
      | null =>
          simp [completeValue, GraphQL.Execution.completeValue]
      | scalar value =>
          simp [completeValue, GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_guarded_merged_child_state
              schema resolvers variableValues depth parentType runtimeType
              identity fields
              (hchildren depth runtimeType identity (Nat.lt_succ_self depth))
      | list values =>
          apply completeValue_list_empty_previous_eq_spec_of_values schema
            resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet fields) fields
          intro value hmem
          exact ih parentType value
            (by
              intro childDepth runtimeType identity hlt hincludes
              exact hchildren childDepth runtimeType identity
                (Nat.lt_trans hlt (Nat.lt_succ_self depth)) hincludes)

theorem completeValue_group_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField) :
    ∀ (depth : Nat) (parentType : Name) (value : Value ObjectIdentity),
      (∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject value runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields }
              initial := .object [] }) ->
        completeValue schema resolvers variableValues depth parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields) value .null =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          parentType fields value := by
  intro depth
  induction depth with
  | zero =>
      intro parentType value _hchildren
      simp [completeValue, GraphQL.Execution.completeValue]
  | succ depth ih =>
      intro parentType value hchildren
      cases value with
      | null =>
          simp [completeValue, GraphQL.Execution.completeValue]
      | scalar value =>
          simp [completeValue, GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_guarded_merged_child_state
              schema resolvers variableValues depth parentType runtimeType
              identity fields
              (by
                intro hincludes
                exact
                  hchildren depth runtimeType identity (Nat.lt_succ_self depth)
                    ValueContainsObject.here hincludes)
      | list values =>
          apply completeValue_list_empty_previous_eq_spec_of_values schema
            resolvers variableValues depth parentType
            (GraphQL.Execution.mergedFieldSelectionSet fields) fields
          intro value hmem
          exact ih parentType value
            (by
              intro childDepth runtimeType identity hlt hcontains hincludes
              exact hchildren childDepth runtimeType identity
                (Nat.lt_trans hlt (Nat.lt_succ_self depth))
                (ValueContainsObject.list hmem hcontains)
                hincludes)

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := selectionSet }
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  rw [hresolve]
  simpa [executableField, GraphQL.Execution.mergedFieldSelectionSet] using
    completeValue_group_eq_spec_of_merged_child_states schema resolvers
      variableValues
      [executableField parentType responseName fieldName arguments selectionSet]
      depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      resolved
      (by
        intro childDepth runtimeType identity hlt
        simpa [executableField] using
          hchildren childDepth runtimeType identity hlt)

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
                selectionSet := selectionSet }
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  rw [hresolve]
  simpa [executableField, GraphQL.Execution.mergedFieldSelectionSet] using
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues
      [executableField parentType responseName fieldName arguments selectionSet]
      depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      resolved
      (by
        intro childDepth runtimeType identity hlt hincludes
        simpa [executableField] using
          hchildren childDepth runtimeType identity hlt hincludes)

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Value ObjectIdentity)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
                selectionSet := selectionSet }
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source
      [.field responseName fieldName arguments directives selectionSet] =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  rw [hresolve]
  simpa [executableField, GraphQL.Execution.mergedFieldSelectionSet] using
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues
      [executableField parentType responseName fieldName arguments selectionSet]
      depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        simpa [executableField] using
          hchildren childDepth runtimeType identity hlt hcontains hincludes)

theorem AppendAllowedFieldState.of_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := selectionSet }
              initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendAllowedFieldState.of_guarded_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
                selectionSet := selectionSet }
              initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendAllowedFieldState.of_contained_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
                selectionSet := selectionSet }
              initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendSelectionState.field_allowed_of_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := selectionSet }
              initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_states hallowed hresolve hchildren
      hdisjoint)

theorem AppendSelectionState.field_allowed_of_guarded_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
                selectionSet := selectionSet }
              initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_guarded_child_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendSelectionState.field_allowed_of_contained_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
                selectionSet := selectionSet }
              initial := .object [] })
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_contained_child_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendAllowedFieldState.of_child_selectionSet_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetState schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) [] selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth :=
  AppendAllowedFieldState.of_child_states hallowed hresolve
    (by
      intro childDepth runtimeType identity hlt
      exact stateEquivalent_of_selectionSet_state
        (hchildren childDepth runtimeType identity hlt))
    hdisjoint

theorem AppendSelectionState.field_allowed_of_child_selectionSet_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetState schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) [] selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_selectionSet_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendAllowedFieldState.of_child_prefix_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetPrefixState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity) []
            selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendAllowedFieldState schema resolvers variableValues (depth + 1)
      parentType source left responseName fieldName arguments directives
      selectionSet depth :=
  AppendAllowedFieldState.of_child_states hallowed hresolve
    (by
      intro childDepth runtimeType identity hlt
      exact stateEquivalent_of_selectionSet_prefix_state
        (hchildren childDepth runtimeType identity hlt))
    hdisjoint

theorem AppendSelectionState.field_allowed_of_child_prefix_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetPrefixState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity) []
            selectionSet)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_prefix_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendSelectionState.field_allowed_of_child_prefix_states_fresh
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : Value ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : Value ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
          AppendSelectionSetPrefixState schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity) []
            selectionSet)
    (hfresh :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst) :
    AppendSelectionState schema resolvers variableValues (depth + 1)
      parentType source left
      (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed_of_child_prefix_states hallowed hresolve
    hchildren
    (executableGroupNamesDisjoint_single_field_of_responseName_fresh schema
      variableValues parentType source left responseName fieldName arguments
      directives selectionSet hallowed hfresh)

theorem executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) (resolved : Value ObjectIdentity)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) (resolved : Value ObjectIdentity)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) (resolved : Value ObjectIdentity)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) (resolved : Value ObjectIdentity)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) (resolved : Value ObjectIdentity)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (field : ExecutableField) (resolved : Value ObjectIdentity)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_collected_single_field_group_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (hgroup : (responseName, [field]) ∈ groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [field] := by
  have hgroupParents : ExecutableFieldsParent parentType [field] :=
    hparents responseName [field] hgroup
  have hparent : field.parentType = parentType :=
    hgroupParents field (by simp)
  exact ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    schema resolvers variableValues depth parentType source field
    (resolvers.resolve field.parentType field.fieldName field.arguments source)
    hparent rfl hchildren

theorem ExecutableGroupsFlatSpecEquivalent_single_field_group_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType responseName : Name) (source : Value ObjectIdentity)
    (field : ExecutableField)
    (hparent : field.parentType = parentType)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, [field])] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    schema resolvers variableValues depth parentType source field
    (resolvers.resolve field.parentType field.fieldName field.arguments source)
    hparent rfl hchildren

theorem executeRootSelectionSet_executableFieldSelections_group_eq_spec_of_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          resolved)]) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections (field :: fields)) =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source
      (executableFieldSelections (field :: fields)) := by
  calc
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          resolved)] := hungrouped
    _ =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source
        (executableFieldSelections (field :: fields)) := by
        rw [specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
          schema resolvers variableValues depth parentType source responseName
          field fields resolved hresponse hparent hresolve]

theorem executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet [field]) resolved)] := by
  calc
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source (executableFieldSelections [field]) := by
        exact
          executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
            schema resolvers variableValues depth parentType source field
            resolved hparent hresolve hchildren
    _ =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet [field]) resolved)] := by
        rw [specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
          schema resolvers variableValues depth parentType source responseName
          field [] resolved]
        · intro candidate hmem
          simp at hmem
          subst candidate
          exact hresponse
        · intro candidate hmem
          simp at hmem
          subst candidate
          exact hparent
        · exact hresolve

theorem executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet [field]) resolved)] := by
  calc
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source (executableFieldSelections [field]) := by
        exact
          executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
            schema resolvers variableValues depth parentType source field
            resolved hparent hresolve hchildren
    _ =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet [field]) resolved)] := by
        rw [specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
          schema resolvers variableValues depth parentType source responseName
          field [] resolved]
        · intro candidate hmem
          simp at hmem
          subst candidate
          exact hresponse
        · intro candidate hmem
          simp at hmem
          subst candidate
          exact hparent
        · exact hresolve

theorem executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source (executableFieldSelections [field]) =
    [(responseName,
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        (GraphQL.Execution.mergedFieldSelectionSet [field]) resolved)] := by
  calc
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source (executableFieldSelections [field]) := by
        exact
          executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
            schema resolvers variableValues depth parentType source field
            resolved hparent hresolve hchildren
    _ =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet [field]) resolved)] := by
        rw [specExecuteRootSelectionSet_executableFieldSelections_group_eq_merged
          schema resolvers variableValues depth parentType source responseName
          field [] resolved]
        · intro candidate hmem
          simp at hmem
          subst candidate
          exact hresponse
        · intro candidate hmem
          simp at hmem
          subst candidate
          exact hparent
        · exact hresolve

theorem ExecutableFieldsMergedComplete_single_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedComplete_single_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_guarded_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedComplete_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Value ObjectIdentity)
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_contained_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          resolved)]) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_group_eq_spec_of_merged_complete
    schema resolvers variableValues depth parentType source responseName field
    fields resolved hresponse hparent hresolve hungrouped

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  unfold ExecutableFieldsMergedComplete at hmerged
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          resolved)]) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hungrouped

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_collected_nonempty_group_of_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source))]) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  exact
    ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hgroupResponses hgroupParents rfl hungrouped

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source))]) :
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
      ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
        schema resolvers variableValues depth parentType source responseName
        field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        hresponse hparent rfl hungrouped
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (depth + 1) parentType source
      selectionSet hdirect hgroups

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  unfold ExecutableFieldsMergedComplete at hmerged
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        operation.rootType source
        (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source))]) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hungrouped

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        operation.rootType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hmerged

theorem executeQuery_eq_spec_of_exact_nonempty_group_merged_complete
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
    (hungrouped :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        operation.rootType source
        (executableFieldSelections (field :: fields)) =
      [(responseName,
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source))]) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hungrouped

theorem executeQuery_eq_spec_of_exact_nonempty_group_mergedComplete
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
    (hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        operation.rootType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hmerged

theorem executeRootSelectionSet_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hparent : field.parentType = parentType)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
      ExecutableGroupsFlatSpecEquivalent_single_field_group_of_child_states
        schema resolvers variableValues depth parentType responseName source
        field hparent hchildren
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (depth + 1) parentType source
      selectionSet hdirect hgroups

theorem stateEquivalent_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hparent : field.parentType = parentType)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
    (executeRootSelectionSet_eq_spec_of_exact_single_field_group schema
      resolvers variableValues depth parentType source selectionSet
      responseName field hcollect hdirect hparent hchildren)

theorem stateEquivalent_of_collected_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : Value ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, [field]) ∈ groups)
    (hexact : groups = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hparent : field.parentType = parentType :=
    (hparents responseName [field] hgroup) field (by simp)
  exact
    stateEquivalent_of_exact_single_field_group schema resolvers
      variableValues depth parentType source selectionSet responseName field
      (by simpa [hexact] using hcollect) hdirect hparent hchildren

theorem executeQueryAtDepth_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hparent : field.parentType = operation.rootType)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact stateEquivalent_of_exact_single_field_group schema resolvers
    variableValues depth operation.rootType source operation.selectionSet
    responseName field hcollect hdirect hparent hchildren

theorem executeQuery_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : Value ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, [field])])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hparent : field.parentType = operation.rootType)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
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
              initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact executeQueryAtDepth_eq_spec_of_exact_single_field_group schema
    resolvers variableValues operation depth source responseName field hroot
    hcollect hdirect hparent hchildren

end ExecutionUngrouped
end Algorithms

end GraphQL
