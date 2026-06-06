import GraphQL.NormalForm.GroundTypeNormalization.Normality

/-!
Operation-level semantic bridge facts for ground-type normalization.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem groundNormalFormCorrect_of_semanticsPreserved
    (schema : Schema) (operation : Operation) :
    groundTypeNormalFormSemanticsPreserved schema operation ->
      groundNormalFormCorrect schema operation := by
  intro hpreserved
  unfold groundNormalFormCorrect DataModel.operationsEquivalentOnData
    DataModel.executeOperationAtDepth
  intro store variableValues depth root _hstore _hroot
  exact hpreserved store.resolvers variableValues depth root.toExecutionValue

theorem groundNormalFormCorrect_of_semanticsPreservation
    (schema : Schema) (operation : Operation) :
    groundTypeNormalFormSemanticsPreservation schema operation ->
      SchemaWellFormedness.schemaWellFormed schema ->
        Validation.operationDefinitionValid schema operation ->
          operationDirectiveFree operation ->
            groundNormalFormCorrect schema operation := by
  intro hpreservation hschema hvalid hfree
  exact groundNormalFormCorrect_of_semanticsPreserved schema operation
    (hpreservation hschema hvalid hfree)

theorem selectionDirectivesAllowBool_nil
    (variableValues : Execution.VariableValues) :
    Execution.selectionDirectivesAllowBool variableValues [] = true := by
  rfl

theorem selectionDirectiveFree_directivesAllowBool
    (variableValues : Execution.VariableValues) {selection : Selection} :
    selectionDirectiveFree selection ->
      match selection with
      | .field _responseName _fieldName _arguments directives _selectionSet =>
          Execution.selectionDirectivesAllowBool variableValues directives = true
      | .inlineFragment _typeCondition directives _selectionSet =>
          Execution.selectionDirectivesAllowBool variableValues directives = true := by
  intro hfree
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      have hdirectives : directives = [] := hfree.1
      subst directives
      rfl
  | inlineFragment typeCondition directives selectionSet =>
      have hdirectives : directives = [] := hfree.1
      subst directives
      rfl

theorem collectSelection_field_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] selectionSet)
      =
      [(responseName, [{
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      }])] := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem collectSelection_inlineFragment_none_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.inlineFragment none [] selectionSet)
      =
      Execution.collectFields schema variableValues parentType source
        selectionSet := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem collectSelection_inlineFragment_some_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.inlineFragment (some typeCondition) [] selectionSet)
      =
      if Execution.doesFragmentTypeApplyBool schema parentType source
          typeCondition then
        Execution.collectFields schema variableValues parentType source
          selectionSet
      else
        [] := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem rootSourceAppliesBool_normalizeOperation
    (schema : Schema) (operation : Operation) (source : Execution.Value) :
    Execution.rootSourceAppliesBool schema (normalizeOperation schema operation)
        source =
      Execution.rootSourceAppliesBool schema operation source := by
  rfl

theorem executeQuery_normalizeOperation_of_rootSource_not_apply
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat) (source : Execution.Value) :
    Execution.rootSourceAppliesBool schema operation source = false ->
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (normalizeOperation schema operation) depth source := by
  intro hroot
  simp [Execution.executeQueryAtDepth, hroot,
    rootSourceAppliesBool_normalizeOperation]

theorem groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet
    (schema : Schema) (operation : Operation) :
    (∀ resolvers variableValues depth source,
      Execution.rootSourceAppliesBool schema operation source = true ->
        Execution.executeSelectionSet schema resolvers variableValues
          depth operation.rootType source operation.selectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues
          depth operation.rootType source
          (normalizeOperation schema operation).selectionSet) ->
      groundTypeNormalFormSemanticsPreserved schema operation := by
  intro hselection
  unfold groundTypeNormalFormSemanticsPreserved operationsEquivalent
  intro resolvers variableValues depth source
  by_cases hroot :
      Execution.rootSourceAppliesBool schema operation source = true
  · simp [Execution.executeQueryAtDepth, hroot,
      rootSourceAppliesBool_normalizeOperation]
    exact hselection resolvers variableValues depth source hroot
  · have hrootFalse :
        Execution.rootSourceAppliesBool schema operation source = false := by
      cases hmatch : Execution.rootSourceAppliesBool schema operation source
      · rfl
      · contradiction
    exact executeQuery_normalizeOperation_of_rootSource_not_apply schema
      resolvers variableValues operation depth source hrootFalse

theorem normalizeOperation_name (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).name = operation.name := by
  rfl

theorem normalizeOperation_rootType (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).rootType = operation.rootType := by
  rfl

theorem normalizeOperation_variableDefinitions (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).variableDefinitions
      = operation.variableDefinitions := by
  rfl



end GroundTypeNormalization

end NormalForm

end GraphQL
