import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection

/-!
Semantic bridge lemmas for directive-free ground-type normalization.

The remaining hard proof is selection-set preservation for `normalizeSelectionSet`.
This module isolates the operation-level and store-backed lifts from that local
selection-set obligation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem executeSelectionSet_inlineFragment_some_directiveFree_skip
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition =
      false ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source rest := by
  intro hskip
  simp [Execution.executeSelectionSet,
    collectFields_inlineFragment_some_directiveFree_skip_eq schema
      variableValues parentType typeCondition source selectionSet rest hskip]

theorem executeSelectionSet_inlineFragment_none_directiveFree_flatten
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (Selection.inlineFragment none [] selectionSet :: rest)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (selectionSet ++ rest) := by
  simp [Execution.executeSelectionSet,
    collectFields_inlineFragment_none_directiveFree_flatten]

theorem executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition =
      true ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source (selectionSet ++ rest) := by
  intro happly
  simp [Execution.executeSelectionSet,
    collectFields_inlineFragment_some_directiveFree_apply_flatten, happly]

theorem lookupType_name_eq (schema : Schema) {typeName : Name}
    {typeDefinition : TypeDefinition} :
    schema.lookupType typeName = some typeDefinition ->
      typeDefinition.name = typeName := by
  intro hlookup
  have hmatch := List.find?_some hlookup
  simpa [Schema.lookupType] using hmatch

theorem typeIncludesObjectBool_eq_of_objectTypeNameBool_true
    (schema : Schema) {typeName runtimeType : Name} :
    objectTypeNameBool schema typeName = true ->
      schema.typeIncludesObjectBool typeName runtimeType = true ->
        runtimeType = typeName := by
  intro hobject hinclude
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = typeName :=
            lookupType_name_eq schema hlookup
          simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
            hlookup, hname] at hinclude
          exact hinclude
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_true_of_typesOverlapBool_true_of_object_source
    (schema : Schema) {parentType typeCondition : Name}
    {source : Execution.Value} :
    objectTypeNameBool schema parentType = true ->
      (∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
        schema.typesOverlapBool parentType typeCondition = true ->
          Execution.doesFragmentTypeApplyBool schema parentType source
            typeCondition = true := by
  intro hobject hsource hoverlap
  rcases hsource with ⟨runtimeType, identity, hsourceEq, hparent⟩
  subst source
  have hruntime :
      runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hparent
  subst runtimeType
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType parentType with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = parentType :=
            lookupType_name_eq schema hlookup
          unfold Schema.typesOverlapBool at hoverlap
          simp [Schema.getPossibleTypes, hlookup, hname] at hoverlap
          simpa [Execution.doesFragmentTypeApplyBool,
            Execution.runtimeObjectType?] using hoverlap
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_false_of_typesOverlapBool_false
    (schema : Schema) {parentType typeCondition runtimeType : Name}
    {identity : Nat} :
    schema.typeIncludesObjectBool parentType runtimeType = true ->
      schema.typesOverlapBool parentType typeCondition = false ->
        Execution.doesFragmentTypeApplyBool schema parentType
          (.object runtimeType identity) typeCondition = false := by
  intro hparent hoverlap
  unfold Execution.doesFragmentTypeApplyBool
  cases hcondition :
      schema.typeIncludesObjectBool typeCondition runtimeType
  · simp [Execution.runtimeObjectType?, hcondition]
  · have hparentMem :
        runtimeType ∈ schema.getPossibleTypes parentType := by
      exact List.contains_iff_mem.mp hparent
    have hoverlapTrue :
        schema.typesOverlapBool parentType typeCondition = true := by
      unfold Schema.typesOverlapBool
      exact List.any_eq_true.mpr
        ⟨runtimeType, hparentMem, hcondition⟩
    rw [hoverlap] at hoverlapTrue
    contradiction

theorem rootSourceAppliesBool_true_object
    (schema : Schema) (operation : Operation) (source : Execution.Value) :
    Execution.rootSourceAppliesBool schema operation source = true ->
      ∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool operation.rootType runtimeType = true := by
  intro hroot
  cases source with
  | null =>
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?] at hroot
  | scalar value =>
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?] at hroot
  | object runtimeType identity =>
      exact ⟨runtimeType, identity, rfl, hroot⟩
  | list values =>
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?] at hroot

theorem doesFragmentTypeApplyBool_false_of_typesOverlapBool_false_of_source
    (schema : Schema) {parentType typeCondition : Name}
    {source : Execution.Value} :
    (∃ runtimeType identity,
      source = .object runtimeType identity
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
      schema.typesOverlapBool parentType typeCondition = false ->
        Execution.doesFragmentTypeApplyBool schema parentType source
          typeCondition = false := by
  intro hsource hoverlap
  rcases hsource with ⟨runtimeType, identity, hsourceEq, hparent⟩
  subst source
  exact doesFragmentTypeApplyBool_false_of_typesOverlapBool_false schema
    hparent hoverlap

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_noOverlap_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    (∃ runtimeType identity,
      source = .object runtimeType identity
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
      schema.typesOverlapBool parentType typeCondition = false ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType rest)
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source rest ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
  intro hsource hoverlap hrest
  have happly :
      Execution.doesFragmentTypeApplyBool schema parentType source
        typeCondition = false :=
    doesFragmentTypeApplyBool_false_of_typesOverlapBool_false_of_source
      schema hsource hoverlap
  simp [normalizeSelectionSet, hoverlap]
  rw [hrest]
  exact (executeSelectionSet_inlineFragment_some_directiveFree_skip schema
    resolvers variableValues depth parentType typeCondition source
    selectionSet rest happly).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_none_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (normalizeSelectionSet schema parentType (selectionSet ++ rest))
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (selectionSet ++ rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (normalizeSelectionSet schema parentType
          (Selection.inlineFragment none [] selectionSet :: rest))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment none [] selectionSet :: rest) := by
  intro happend
  simp [normalizeSelectionSet]
  rw [happend]
  exact (executeSelectionSet_inlineFragment_none_directiveFree_flatten schema
    resolvers variableValues depth parentType source selectionSet rest).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_apply_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    schema.typesOverlapBool parentType typeCondition = true ->
      Execution.doesFragmentTypeApplyBool schema parentType source
        typeCondition = true ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType (selectionSet ++ rest))
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source (selectionSet ++ rest) ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
  intro hoverlap happly happend
  simp [normalizeSelectionSet, hoverlap]
  rw [happend]
  exact (executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
    schema resolvers variableValues depth parentType typeCondition source
    selectionSet rest happly).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_overlap_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    objectTypeNameBool schema parentType = true ->
      (∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
        schema.typesOverlapBool parentType typeCondition = true ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType (selectionSet ++ rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source (selectionSet ++ rest) ->
            Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (normalizeSelectionSet schema parentType
                (Selection.inlineFragment (some typeCondition) [] selectionSet
                  :: rest))
              =
            Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest) := by
  intro hobject hsource hoverlap happend
  exact normalizeSelectionSet_executeSelectionSet_inlineFragment_some_apply_case
    schema resolvers variableValues depth parentType typeCondition source
    selectionSet rest hoverlap
    (doesFragmentTypeApplyBool_true_of_typesOverlapBool_true_of_object_source
      schema hobject hsource hoverlap)
    happend

theorem normalizeSelectionSet_executeSelectionSet_field_lookup_none_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition)
    (depth : Nat) (parentType responseName fieldName : Name)
    (arguments : List Argument) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] selectionSet
        :: rest) ->
      schema.lookupField parentType fieldName = none ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest))
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (Selection.field responseName fieldName arguments []
            selectionSet :: rest) := by
  intro hvalid hlookup
  exact False.elim
    (Validation.selectionSetValid_field_head_lookup_none_false
      hvalid hlookup)

theorem normalizeOperation_executeQuery
    (schema : Schema) (operation : Operation) :
    (∀ resolvers variableValues source,
      Execution.rootSourceAppliesBool schema operation source = true ->
        Execution.executeSelectionSet schema resolvers variableValues
          (Execution.executeQueryDepthBound operation)
          operation.rootType source operation.selectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues
          (Execution.executeQueryDepthBound
            (normalizeOperation schema operation))
          operation.rootType source
          (normalizeOperation schema operation).selectionSet) ->
      groundTypeNormalFormSemanticsPreserved schema operation := by
  exact groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet schema
    operation

theorem groundTypeNormalFormSemanticsPreservation_of_selectionSet
    (schema : Schema) (operation : Operation) :
    (SchemaWellFormedness.schemaWellFormed schema ->
      Validation.operationDefinitionValid schema operation ->
        operationDirectiveFree operation ->
          ∀ resolvers variableValues source,
            Execution.rootSourceAppliesBool schema operation source = true ->
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound operation)
                operation.rootType source operation.selectionSet
                =
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound
                  (normalizeOperation schema operation))
                operation.rootType source
                (normalizeOperation schema operation).selectionSet) ->
      NormalForm.groundTypeNormalFormSemanticsPreservation schema operation := by
  intro hselection hschema hvalid hfree
  exact normalizeOperation_executeQuery schema operation
    (hselection hschema hvalid hfree)

theorem groundNormalFormCorrect_of_selectionSet
    (schema : Schema) (operation : Operation) :
    (SchemaWellFormedness.schemaWellFormed schema ->
      Validation.operationDefinitionValid schema operation ->
        operationDirectiveFree operation ->
          ∀ resolvers variableValues source,
            Execution.rootSourceAppliesBool schema operation source = true ->
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound operation)
                operation.rootType source operation.selectionSet
                =
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound
                  (normalizeOperation schema operation))
                operation.rootType source
                (normalizeOperation schema operation).selectionSet) ->
      SchemaWellFormedness.schemaWellFormed schema ->
        Validation.operationDefinitionValid schema operation ->
          operationDirectiveFree operation ->
            NormalForm.groundNormalFormCorrect schema operation := by
  intro hselection hschema hvalid hfree
  exact groundNormalFormCorrect_of_semanticsPreservation schema operation
    (groundTypeNormalFormSemanticsPreservation_of_selectionSet schema operation
      hselection)
    hschema hvalid hfree

end GroundTypeNormalization

end NormalForm

end GraphQL
