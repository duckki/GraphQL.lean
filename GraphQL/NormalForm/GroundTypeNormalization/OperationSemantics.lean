import GraphQL.NormalForm.GroundTypeNormalization.SelectionSetSemantics
import GraphQL.NormalForm.Shared.Execution

/-!
Operation-level semantic bridge facts for ground-type normalization.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectIdentity : Type}

theorem groundNormalFormCorrect_of_semanticsPreserved
    (schema : Schema) (operation : Operation) :
    groundTypeNormalFormSemanticsPreserved schema operation ->
      groundNormalFormCorrect schema operation := by
  intro hpreserved
  unfold groundNormalFormCorrect DataModel.operationsEquivalentOnData
    DataModel.executeOperationAtDepth
  intro store variableValues depth _hstore
  exact hpreserved DataModel.ObjectPath (store.resolvers schema)
    variableValues depth store.rootExecutionValue

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

theorem rootSourceAppliesBool_normalizeOperation
    (schema : Schema) (operation : Operation) (source : Execution.Value ObjectIdentity) :
    Execution.rootSourceAppliesBool schema (normalizeOperation schema operation)
        source =
      Execution.rootSourceAppliesBool schema operation source := by
  rfl

theorem executeQuery_normalizeOperation_of_rootSource_not_apply
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat) (source : Execution.Value ObjectIdentity) :
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
    (∀ (ObjectIdentity : Type) (resolvers : Execution.Resolvers ObjectIdentity)
      variableValues depth (source : Execution.Value ObjectIdentity),
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
  intro ObjectIdentity resolvers variableValues depth source
  by_cases hroot :
      Execution.rootSourceAppliesBool schema operation source = true
  · simp [Execution.executeQueryAtDepth, hroot,
      rootSourceAppliesBool_normalizeOperation]
    exact hselection ObjectIdentity resolvers variableValues depth source hroot
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

theorem normalizeOperation_executeQuery
    (schema : Schema) (operation : Operation) :
    (∀ (ObjectIdentity : Type) (resolvers : Execution.Resolvers ObjectIdentity)
      variableValues depth (source : Execution.Value ObjectIdentity),
      Execution.rootSourceAppliesBool schema operation source = true ->
        Execution.executeSelectionSet schema resolvers variableValues
          depth operation.rootType source operation.selectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues
          depth operation.rootType source
          (normalizeOperation schema operation).selectionSet) ->
      groundTypeNormalFormSemanticsPreserved schema operation := by
  exact groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet schema
    operation

theorem groundTypeNormalFormSemanticsPreservation_of_selectionSet
    (schema : Schema) (operation : Operation) :
    (SchemaWellFormedness.schemaWellFormed schema ->
      Validation.operationDefinitionValid schema operation ->
        operationDirectiveFree operation ->
          ∀ (ObjectIdentity : Type) (resolvers : Execution.Resolvers ObjectIdentity)
            variableValues depth (source : Execution.Value ObjectIdentity),
            Execution.rootSourceAppliesBool schema operation source = true ->
              Execution.executeSelectionSet schema resolvers variableValues
                depth operation.rootType source operation.selectionSet
                =
              Execution.executeSelectionSet schema resolvers variableValues
                depth operation.rootType source
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
          ∀ (ObjectIdentity : Type) (resolvers : Execution.Resolvers ObjectIdentity)
            variableValues depth (source : Execution.Value ObjectIdentity),
            Execution.rootSourceAppliesBool schema operation source = true ->
              Execution.executeSelectionSet schema resolvers variableValues
                depth operation.rootType source operation.selectionSet
                =
              Execution.executeSelectionSet schema resolvers variableValues
                depth operation.rootType source
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

theorem groundTypeNormalFormSemanticsPreservation
    (schema : Schema) (operation : Operation) :
    NormalForm.groundTypeNormalFormSemanticsPreservation schema operation := by
  intro hschema hvalid hfree
  apply normalizeOperation_executeQuery schema operation
  intro ObjectIdentity resolvers variableValues depth source hroot
  have hrootObject : schema.objectType operation.rootType := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema operation.rootType = true :=
    objectTypeNameBool_eq_true_of_objectType schema hrootObject
  have hsource :
      ∃ runtimeType identity,
        source = Execution.Value.object runtimeType identity
          ∧ schema.typeIncludesObjectBool operation.rootType runtimeType =
            true :=
    rootSourceAppliesBool_true_object schema operation source hroot
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions operation.rootType hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hpreserved :=
    normalizeSelectionSet_executeSelectionSet schema resolvers variableValues
      hschema depth operation.rootType source operation.selectionSet hobject
      hsource hfree hready hmerge
  simpa [normalizeOperation] using hpreserved.symm

theorem groundNormalFormCorrect
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
      Validation.operationDefinitionValid schema operation ->
        operationDirectiveFree operation ->
          NormalForm.groundNormalFormCorrect schema operation := by
  intro hschema hvalid hfree
  exact groundNormalFormCorrect_of_semanticsPreservation schema operation
    (groundTypeNormalFormSemanticsPreservation schema operation)
    hschema hvalid hfree

end GroundTypeNormalization

end NormalForm

end GraphQL
