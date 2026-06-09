import GraphQL.NormalForm.CompleteNormalization.OperationVariables

/-!
Operation projection and top-level correctness-wrapper facts for complete normalization.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem completeNormalizeOperation_rootType
    (schema : Schema) (operation : Operation) :
    (completeNormalizeOperation schema operation).rootType =
      operation.rootType := by
  rfl

theorem completeNormalizeOperation_name
    (schema : Schema) (operation : Operation) :
    (completeNormalizeOperation schema operation).name =
      operation.name := by
  rfl

theorem completeNormalizeOperation_variableDefinitions
    (schema : Schema) (operation : Operation) :
    (completeNormalizeOperation schema operation).variableDefinitions =
      operation.variableDefinitions := by
  rfl

theorem completeNormalizeOperation_selectionSet
    (schema : Schema) (operation : Operation) :
    (completeNormalizeOperation schema operation).selectionSet =
      normalizeForType schema
        (operationBoolVars operation)
        operation.rootType operation.selectionSet := by
  rfl

theorem completeNormalizeOperation_rootSourceAppliesBool
    (schema : Schema) (operation : Operation)
    (source : Execution.Value ObjectIdentity) :
    Execution.rootSourceAppliesBool schema
        (completeNormalizeOperation schema operation) source =
      Execution.rootSourceAppliesBool schema operation source := by
  rfl

theorem completeNormalizationSemanticsPreserved_of_selectionSet
    (schema : Schema) (operation : Operation) :
    (∀ (ObjectIdentity : Type) (resolvers : Execution.Resolvers ObjectIdentity)
      variableValues depth (source : Execution.Value ObjectIdentity),
      operationBoolVarsComplete operation variableValues ->
      Execution.rootSourceAppliesBool schema operation source = true ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (completeNormalizeOperation schema operation).selectionSet) ->
      completeNormalizationSemanticsPreserved schema operation := by
  intro hselection ObjectIdentity resolvers variableValues depth source hcomplete
  cases hroot : Execution.rootSourceAppliesBool schema operation source with
  | false =>
      have hnormalizedRoot :
          Execution.rootSourceAppliesBool schema
              (completeNormalizeOperation schema operation) source = false := by
        simpa [completeNormalizeOperation_rootSourceAppliesBool] using hroot
      simp [Execution.executeQueryAtDepth, hroot, hnormalizedRoot]
  | true =>
      have hnormalizedRoot :
          Execution.rootSourceAppliesBool schema
              (completeNormalizeOperation schema operation) source = true := by
        simpa [completeNormalizeOperation_rootSourceAppliesBool] using hroot
      have hselectionEq :=
        hselection ObjectIdentity resolvers variableValues depth source
          hcomplete hroot
      simp [Execution.executeQueryAtDepth, hroot, hnormalizedRoot]
      simpa [completeNormalizeOperation] using hselectionEq

theorem completeNormalizationCorrect_of_semanticsPreserved
    (schema : Schema) (operation : Operation) :
    completeNormalizationSemanticsPreserved schema operation ->
      completeNormalizationCorrect schema operation := by
  intro hpreserved store variableValues depth _hwellTyped hcomplete
  exact hpreserved DataModel.ObjectPath (store.resolvers schema) variableValues
    depth store.rootExecutionValue hcomplete

theorem completeNormalizationCorrect_of_selectionSet
    (schema : Schema) (operation : Operation) :
    (∀ (ObjectIdentity : Type) (resolvers : Execution.Resolvers ObjectIdentity)
      variableValues depth (source : Execution.Value ObjectIdentity),
      operationBoolVarsComplete operation variableValues ->
      Execution.rootSourceAppliesBool schema operation source = true ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (completeNormalizeOperation schema operation).selectionSet) ->
      completeNormalizationCorrect schema operation := by
  intro hselection
  exact completeNormalizationCorrect_of_semanticsPreserved schema operation
    (completeNormalizationSemanticsPreserved_of_selectionSet schema operation
      hselection)

end CompleteNormalization

end NormalForm

end GraphQL
