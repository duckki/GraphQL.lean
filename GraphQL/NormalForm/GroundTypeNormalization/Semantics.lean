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
