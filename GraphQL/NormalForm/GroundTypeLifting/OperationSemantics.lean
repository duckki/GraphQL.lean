import GraphQL.NormalForm.GroundTypeLifting.SelectionSemantics

/-!
Operation-level semantic preservation facts for the alternative ground-lift phase.

These proofs are intentionally separate from the existing `normalizeSelectionSet`
correctness proof. The ground-lift phase is a candidate first step for a later
directive-aware normalizer, so it should not depend on the current normalizer as
an implementation shortcut.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeLifting

variable {ObjectRef : Type}

open GroundTypeNormalization

theorem rootSourceAppliesBool_groundLiftOperation
    (schema : Schema) (operation : Operation) (source : Execution.Value ObjectRef) :
    Execution.rootSourceAppliesBool schema
        (groundLiftOperation schema operation) source =
      Execution.rootSourceAppliesBool schema operation source := by
  rfl

theorem executeQueryAtDepth_groundLiftOperation_eq_of_selectionSet
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat)
    (source : Execution.Value ObjectRef) :
    (∀ runtimeType ref,
      source = Execution.Value.object runtimeType ref ->
      schema.typeIncludesObjectBool operation.rootType runtimeType = true ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (groundLiftSelectionSet schema operation.rootType
            operation.selectionSet)
        =
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet) ->
      Execution.executeQueryAtDepth schema resolvers variableValues
        (groundLiftOperation schema operation) depth source
      =
      Execution.executeQueryAtDepth schema resolvers variableValues
        operation depth source := by
  intro hselection
  rw [Execution.executeQueryAtDepth]
  rw [rootSourceAppliesBool_groundLiftOperation]
  rw [Execution.executeQueryAtDepth]
  cases hroot :
      Execution.rootSourceAppliesBool schema operation source
  · simp
  · rcases rootSourceAppliesBool_true_object schema operation source hroot with
      ⟨runtimeType, ref, hsource, hinclude⟩
    simp [groundLiftOperation]
    exact hselection runtimeType ref hsource hinclude

theorem executeOperationAtDepth_groundLiftOperation_eq_of_selectionSet
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat) :
    (∀ runtimeType ref,
      store.rootExecutionValue = .object runtimeType ref ->
      schema.typeIncludesObjectBool operation.rootType runtimeType = true ->
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth operation.rootType store.rootExecutionValue
          (groundLiftSelectionSet schema operation.rootType
            operation.selectionSet)
        =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth operation.rootType store.rootExecutionValue
          operation.selectionSet) ->
      DataModel.executeOperationAtDepth schema store variableValues
        (groundLiftOperation schema operation) depth
      =
      DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  intro hselection
  exact executeQueryAtDepth_groundLiftOperation_eq_of_selectionSet schema
    (store.resolvers schema) variableValues operation depth
    store.rootExecutionValue hselection

theorem executeOperationAtDepth_groundLiftOperation_eq_of_scoped
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    operationDirectiveFree operation ->
    (∀ depth execParent runtimeType scopedSelections,
      objectTypeNameBool schema execParent = true ->
      schema.typeIncludesObjectBool execParent runtimeType = true ->
      scopedSelectionSetDirectiveFree scopedSelections ->
      scopedSelectionSetSemanticsReady schema execParent scopedSelections ->
      scopedSelectionSetLookupValid schema scopedSelections ->
      scopedSelectionSetCanMerge schema execParent scopedSelections ->
        scopedSelectionSetRuntimeApplies schema runtimeType scopedSelections ->
        (ref : Option DataModel.ObjectRef := none) ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues depth execParent
            (Execution.Value.object runtimeType ref)
            (groundLiftScopedSelectionSet schema scopedSelections)
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues depth execParent
            (Execution.Value.object runtimeType ref)
            (eraseScopedSelectionSet scopedSelections)) ->
      DataModel.executeOperationAtDepth schema store variableValues
        (groundLiftOperation schema operation) depth
      =
      DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  intro hschema hvalid hfree hscoped
  apply executeOperationAtDepth_groundLiftOperation_eq_of_selectionSet
  intro runtimeType ref hroot hinclude
  have hrootObject : schema.objectType operation.rootType := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema operation.rootType = true :=
    objectTypeNameBool_eq_true_of_objectType schema hrootObject
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
  have hselection :=
    groundLiftSelectionSet_executeSelectionSet_on_store_of_scoped schema store
      variableValues
      (fun depth execParent runtimeType scopedSelections hobject
          hinclude hfree hready hlookup hmerge happlies ref =>
        hscoped depth execParent runtimeType scopedSelections hobject
          hinclude hfree hready hlookup hmerge happlies (ref := ref))
      depth operation.rootType runtimeType
      operation.selectionSet hobject hinclude hfree hready
      hmerge (ref := ref)
  simpa [hroot] using hselection

theorem executeOperationAtDepth_groundLiftOperation_eq_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat) :
    SchemaWellFormedness.schemaWellFormed schema ->
    store.wellTyped schema ->
    Validation.operationDefinitionValid schema operation ->
    operationDirectiveFree operation ->
      DataModel.executeOperationAtDepth schema store variableValues
        (groundLiftOperation schema operation) depth
      =
      DataModel.executeOperationAtDepth schema store variableValues
        operation depth := by
  intro hschema hstore hvalid hfree
  exact executeOperationAtDepth_groundLiftOperation_eq_of_scoped schema store
    variableValues operation depth hschema hvalid hfree
    (fun depth execParent runtimeType scopedSelections hobject
        hinclude hfree hready hlookup hmerge happlies ref =>
      groundLiftScopedSelectionSet_executeSelectionSet_on_store schema store
        variableValues hschema hstore depth execParent runtimeType
        scopedSelections hobject hinclude hfree hready hlookup hmerge
        happlies (ref := ref))

theorem groundLiftOperation_operationsEquivalentOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    operationDirectiveFree operation ->
      DataModel.operationsEquivalentOnData schema operation
        (groundLiftOperation schema operation) := by
  intro hschema hvalid hfree store variableValues depth hstore
  exact (executeOperationAtDepth_groundLiftOperation_eq_on_store schema store
    variableValues operation depth hschema hstore hvalid hfree).symm

end GroundTypeLifting

end NormalForm

end GraphQL
