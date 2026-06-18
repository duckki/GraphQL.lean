import GraphQL.NormalForm.CompleteNormalization.Validity.Branches

/-! Operation-level validity preservation for complete normalization. -/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem selectionSetImplementationValidInScope_of_rootObjectPossible
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    {rootType objectType : Name} {selectionSet : List Selection} :
    schema.objectType rootType ->
    objectType ∈ schema.getPossibleTypes rootType ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions rootType selectionSet ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions objectType selectionSet := by
  intro hrootObject hpossible himplementation
  have hinclude :
      schema.typeIncludesObjectBool rootType objectType = true :=
    List.contains_iff_mem.mpr hpossible
  have hobjectEq : objectType = rootType :=
    object_typeIncludesObjectBool_eq_self schema hrootObject hinclude
  simpa [hobjectEq] using himplementation

theorem completeNormalizeRootSelectionSet_eq_flatten
    (schema : Schema) (variables : List BoolVar)
    (parentType : Name) (selectionSet : List Selection) :
    completeNormalizeRootSelectionSet schema variables parentType selectionSet =
        List.flatten ((allBoolCases variables).map (fun boolCase =>
          match normalizeSelectionSet schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet) with
          | [] => []
          | selection :: rest =>
              wrapWithBoolCase boolCase (selection :: rest))) := by
  rfl

theorem operation_root_object_of_valid
    {schema : Schema} {operation : Operation} :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      schema.objectType operation.rootType := by
  intro hschema hoperation
  rcases hschema with
    ⟨_hnames, hqueryObject, _htypes, _hpossibleObjects,
      _hpossibleNodup, _himplements⟩
  have hrootEq :=
    Validation.operationDefinitionValid_rootType_eq hoperation
  rw [hrootEq]
  exact hqueryObject

theorem operation_selectionSetSemanticsReady_of_valid
    {schema : Schema} {operation : Operation} :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet := by
  intro hschema hoperation
  exact selectionSetSemanticsReady_of_selectionSetValid_object schema
    operation.variableDefinitions operation.rootType hschema
    (operation_root_object_of_valid hschema hoperation)
    operation.selectionSet
    (Validation.operationDefinitionValid_selectionSetValid hoperation)

theorem completeNormalizeRootSelectionSet_selectionSetValid
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfeasibleAll :
      selectionSetsTypeConditionFeasibleInEveryScope schema)
    (hfilteredCases :
      ∀ boolCase, boolCase ∈ allBoolCases (operationBoolVars operation) ->
        Validation.selectionSetImplementationValidInScope schema
          operation.variableDefinitions operation.rootType
          (filterSelectionSetBoolCase boolCase operation.selectionSet))
    (hoperation : Validation.operationDefinitionValid schema operation) :
    Validation.selectionSetValid schema operation.variableDefinitions
      operation.rootType
      (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
        operation.rootType operation.selectionSet) := by
  have hrootObject : schema.objectType operation.rootType :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have himplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType operation.selectionSet :=
    (Validation.operationDefinitionValid_selectionSetImplementationValid
      hoperation).1
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  rw [completeNormalizeRootSelectionSet_eq_flatten schema
    (operationBoolVars operation) operation.rootType operation.selectionSet]
  exact completeNormalizeBranches_selectionSetValid schema operation hschema
    hfeasibleAll hoperation hrootObject hready himplementation hmerge
    (allBoolCases (operationBoolVars operation))
    (by intro boolCase hcase; exact hcase)
    hfilteredCases

theorem completeNormalizeRootSelectionSet_selectionSetImplementationValid
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfeasibleAll :
      selectionSetsTypeConditionFeasibleInEveryScope schema)
    (hfilteredCases :
      ∀ boolCase, boolCase ∈ allBoolCases (operationBoolVars operation) ->
        Validation.selectionSetImplementationValidInScope schema
          operation.variableDefinitions operation.rootType
          (filterSelectionSetBoolCase boolCase operation.selectionSet))
    (hoperation : Validation.operationDefinitionValid schema operation) :
    Validation.selectionSetImplementationValid schema
      operation.variableDefinitions operation.rootType
      (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
        operation.rootType operation.selectionSet) := by
  have hrootObject : schema.objectType operation.rootType :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have himplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType operation.selectionSet :=
    (Validation.operationDefinitionValid_selectionSetImplementationValid
      hoperation).1
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  have hrootImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
          operation.rootType operation.selectionSet) := by
    rw [completeNormalizeRootSelectionSet_eq_flatten schema
      (operationBoolVars operation) operation.rootType operation.selectionSet]
    exact completeNormalizeBranches_implementationValidInScope schema
      operation hschema hfeasibleAll hrootObject hready himplementation hmerge
      (allBoolCases (operationBoolVars operation))
      hfilteredCases
  exact ⟨hrootImplementation,
    by
      intro objectType hpossible
      exact selectionSetImplementationValidInScope_of_rootObjectPossible
        schema operation.variableDefinitions hrootObject hpossible
        hrootImplementation⟩

theorem completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
    (schema : Schema) (operation : Operation) :
    Validation.operationDefinitionValid schema operation ->
    completeBoolCasesCompositeChildrenSurvive operation ->
      ∀ boolCase, boolCase ∈ allBoolCases (operationBoolVars operation) ->
        Validation.selectionSetImplementationValidInScope schema
          operation.variableDefinitions operation.rootType
          (filterSelectionSetBoolCase boolCase operation.selectionSet) := by
  intro hoperation hboolCases boolCase hcase
  exact
    selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
      schema operation.variableDefinitions boolCase operation.rootType
      operation.selectionSet
      ((Validation.operationDefinitionValid_selectionSetImplementationValid
        hoperation).1)
      (hboolCases boolCase hcase)

theorem completeFilteredBoolCasesFieldsCanMerge
    (schema : Schema) (operation : Operation) :
    Validation.operationDefinitionValid schema operation ->
      ∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
        ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
          FieldMerge.fieldsInSetCanMerge schema operation.rootType
            (filterSelectionSetBoolCase leftCase operation.selectionSet
              ++ filterSelectionSetBoolCase rightCase
                operation.selectionSet) := by
  intro hoperation leftCase _hleftCase rightCase _hrightCase
  have hsourceMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  exact fieldsInSetCanMerge_filterSelectionSetBoolCase_pair schema
    leftCase rightCase
    (GroundTypeNormalization.fieldsInSetCanMerge_self schema
      operation.rootType operation.selectionSet hsourceMerge)

theorem completeNormalizedBoolCaseBranchSelfFieldsCanMerge
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    completeBoolCasesCompositeChildrenSurvive operation ->
      ∀ boolCase, boolCase ∈ allBoolCases (operationBoolVars operation) ->
        FieldMerge.fieldsInSetCanMerge schema operation.rootType
          (normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase boolCase operation.selectionSet)
            ++
            normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase boolCase operation.selectionSet)) := by
  intro hschema hoperation hfeasibleAll hsurvive boolCase hcase
  have hrootObject : schema.objectType operation.rootType :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have hfilteredReady :
      selectionSetSemanticsReady schema operation.rootType
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
      operation.rootType operation.selectionSet hready
  have hfilteredImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
      schema operation hoperation hsurvive boolCase hcase
  have hfilteredMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase schema boolCase
      (Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation)
  have hbranchValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        operation.variableDefinitions operation.rootType
        (normalizeSelectionSet schema operation.rootType
          (filterSelectionSetBoolCase boolCase operation.selectionSet)) :=
    GroundTypeNormalization.normalizeSelectionSet_normalizedValid schema
      operation.variableDefinitions hschema hfeasibleAll operation.rootType
      (filterSelectionSetBoolCase boolCase operation.selectionSet)
      hrootObject hfilteredReady hfilteredImplementation hfilteredMerge
      (filterSelectionSetBoolCase_directiveFree schema boolCase
        operation.selectionSet)
  exact hbranchValid.fieldsCanMergeSelf operation.rootType

theorem completeNormalizedBoolCaseBranchesFieldsCanMerge_of_crossFields
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    completeBoolCasesCompositeChildrenSurvive operation ->
    (∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
      ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
        ∀ leftField,
          leftField ∈ FieldMerge.collectFields schema operation.rootType
            (normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase leftCase operation.selectionSet)) ->
          ∀ rightField,
            rightField ∈ FieldMerge.collectFields schema operation.rootType
              (normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase rightCase operation.selectionSet)) ->
            leftField.responseName = rightField.responseName ->
              FieldMerge.fieldsForNameCanMerge schema leftField rightField) ->
      ∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
        ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
          FieldMerge.fieldsInSetCanMerge schema operation.rootType
            (normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase leftCase operation.selectionSet)
              ++
              normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase rightCase operation.selectionSet)) := by
  intro hschema hoperation hfeasibleAll hsurvive hcross
    leftCase hleftCase rightCase hrightCase
  have hrootObject : schema.objectType operation.rootType :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  have hleftImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
      schema operation hoperation hsurvive leftCase hleftCase
  have hrightImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
      schema operation hoperation hsurvive rightCase hrightCase
  have hleftValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        operation.variableDefinitions operation.rootType
        (normalizeSelectionSet schema operation.rootType
          (filterSelectionSetBoolCase leftCase operation.selectionSet)) :=
    normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
      schema operation.variableDefinitions hschema hfeasibleAll
      operation.rootType operation.selectionSet leftCase hrootObject hready
      hleftImplementation hmerge
  have hrightValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        operation.variableDefinitions operation.rootType
        (normalizeSelectionSet schema operation.rootType
          (filterSelectionSetBoolCase rightCase operation.selectionSet)) :=
    normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
      schema operation.variableDefinitions hschema hfeasibleAll
      operation.rootType operation.selectionSet rightCase hrootObject hready
      hrightImplementation hmerge
  exact GroundTypeNormalization.normalizedSelectionSetsPairFieldsCanMerge
    hleftValid hrightValid
    (fun leftField hleftField rightField hrightField hresponse =>
      hcross leftCase hleftCase rightCase hrightCase
        leftField hleftField rightField hrightField hresponse)

theorem completeNormalizedBoolCaseBranchesFieldsCanMerge
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    completeBoolCasesCompositeChildrenSurvive operation ->
      ∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
        ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
          FieldMerge.fieldsInSetCanMerge schema operation.rootType
            (normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase leftCase operation.selectionSet)
              ++
              normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase rightCase operation.selectionSet)) := by
  intro hschema hoperation hfeasibleAll hsurvive leftCase hleftCase
    rightCase hrightCase
  have hrootObject : schema.objectType operation.rootType :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have hleftReady :
      selectionSetSemanticsReady schema operation.rootType
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema leftCase
      operation.rootType operation.selectionSet hready
  have hrightReady :
      selectionSetSemanticsReady schema operation.rootType
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema rightCase
      operation.rootType operation.selectionSet hready
  have hleftImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
      schema operation hoperation hsurvive leftCase hleftCase
  have hrightImplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
      schema operation hoperation hsurvive rightCase hrightCase
  have hsourceMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  have hleftMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase schema leftCase
      hsourceMerge
  have hrightMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase schema rightCase
      hsourceMerge
  have hpairMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (filterSelectionSetBoolCase leftCase operation.selectionSet
          ++ filterSelectionSetBoolCase rightCase
            operation.selectionSet) :=
    completeFilteredBoolCasesFieldsCanMerge schema operation hoperation
      leftCase hleftCase rightCase hrightCase
  exact
    normalizeSelectionSets_fieldsInSetCanMerge_anyParent schema
      operation.variableDefinitions hschema hfeasibleAll operation.rootType
      (filterSelectionSetBoolCase leftCase operation.selectionSet)
      (filterSelectionSetBoolCase rightCase operation.selectionSet)
      hrootObject hleftReady hrightReady hleftImplementation
      hrightImplementation hleftMerge hrightMerge hpairMerge
      (filterSelectionSetBoolCase_directiveFree schema leftCase
        operation.selectionSet)
      (filterSelectionSetBoolCase_directiveFree schema rightCase
        operation.selectionSet)
      operation.rootType

theorem completeNormalizeOperation_valid_of_filteredCases_and_merge
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    (∀ boolCase, boolCase ∈ allBoolCases (operationBoolVars operation) ->
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (filterSelectionSetBoolCase boolCase operation.selectionSet)) ->
    FieldMerge.fieldsInSetCanMerge schema operation.rootType
      (completeNormalizeRootSelectionSet schema
        (operationBoolVars operation) operation.rootType
        operation.selectionSet) ->
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema operation) := by
  intro hschema hoperation hfeasibleAll hfilteredCases hnormalizedMerge
  exact ⟨
    by simp [completeNormalizeOperation,
      Validation.operationDefinitionValid_rootType_eq hoperation],
    by
      simpa [completeNormalizeOperation] using
        (Validation.operationDefinitionValid_rootTypeComposite
          (operation := operation) hoperation),
    by
      simpa [completeNormalizeOperation] using
        (Validation.operationDefinitionValid_variableDefinitionsValid
          (operation := operation) hoperation),
    by
      simpa [completeNormalizeOperation] using
        completeNormalizeRootSelectionSet_selectionSetValid
          schema operation hschema hfeasibleAll hfilteredCases hoperation,
    by
      simpa [completeNormalizeOperation] using
        completeNormalizeRootSelectionSet_selectionSetImplementationValid
          schema operation hschema hfeasibleAll hfilteredCases hoperation,
    by
      simpa [completeNormalizeOperation] using hnormalizedMerge⟩

theorem completeNormalizeOperation_valid_of_filteredCases_and_branchPairs
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    (∀ boolCase, boolCase ∈ allBoolCases (operationBoolVars operation) ->
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (filterSelectionSetBoolCase boolCase operation.selectionSet)) ->
    (∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
      ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
        FieldMerge.fieldsInSetCanMerge schema operation.rootType
          (normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase leftCase operation.selectionSet)
            ++
            normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase rightCase operation.selectionSet))) ->
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema operation) := by
  intro hschema hoperation hfeasibleAll hfilteredCases hbranchPairs
  apply completeNormalizeOperation_valid_of_filteredCases_and_merge
      schema operation hschema hoperation hfeasibleAll hfilteredCases
  exact completeNormalizeRootSelectionSet_fieldsInSetCanMerge_of_branchPairs
    schema (operationBoolVars operation) operation.rootType
    operation.selectionSet hbranchPairs

theorem completeNormalizeOperation_valid_of_branchPairs
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    completeBoolCasesCompositeChildrenSurvive operation ->
    (∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
      ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
        FieldMerge.fieldsInSetCanMerge schema operation.rootType
          (normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase leftCase operation.selectionSet)
            ++
            normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase rightCase operation.selectionSet))) ->
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema operation) := by
  intro hschema hoperation hfeasibleAll hsurvive hbranchPairs
  exact completeNormalizeOperation_valid_of_filteredCases_and_branchPairs
    schema operation hschema hoperation hfeasibleAll
    (completeFilteredBoolCasesImplementationValid_of_compositeChildrenSurvive
      schema operation hoperation hsurvive)
    hbranchPairs

theorem completeNormalizeOperation_valid_of_crossFields
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    completeBoolCasesCompositeChildrenSurvive operation ->
    (∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
      ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
        ∀ leftField,
          leftField ∈ FieldMerge.collectFields schema operation.rootType
            (normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase leftCase operation.selectionSet)) ->
          ∀ rightField,
            rightField ∈ FieldMerge.collectFields schema operation.rootType
              (normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase rightCase operation.selectionSet)) ->
            leftField.responseName = rightField.responseName ->
              FieldMerge.fieldsForNameCanMerge schema leftField rightField) ->
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema operation) := by
  intro hschema hoperation hfeasibleAll hsurvive hcross
  apply completeNormalizeOperation_valid_of_branchPairs
      schema operation hschema hoperation hfeasibleAll hsurvive
  exact completeNormalizedBoolCaseBranchesFieldsCanMerge_of_crossFields
    schema operation hschema hoperation hfeasibleAll hsurvive hcross

theorem completeNormalizeOperation_valid_of_distinctBranchPairs
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    selectionSetsTypeConditionFeasibleInEveryScope schema ->
    completeBoolCasesCompositeChildrenSurvive operation ->
    (∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
      ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
        leftCase ≠ rightCase ->
          FieldMerge.fieldsInSetCanMerge schema operation.rootType
            (normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase leftCase operation.selectionSet)
              ++
              normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase rightCase operation.selectionSet))) ->
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema operation) := by
  intro hschema hoperation hfeasibleAll hsurvive hdistinctPairs
  apply completeNormalizeOperation_valid_of_branchPairs
      schema operation hschema hoperation hfeasibleAll hsurvive
  intro leftCase hleftCase rightCase hrightCase
  by_cases hsame : leftCase = rightCase
  · subst rightCase
    exact completeNormalizedBoolCaseBranchSelfFieldsCanMerge schema operation
      hschema hoperation hfeasibleAll hsurvive leftCase hleftCase
  · exact hdistinctPairs leftCase hleftCase rightCase hrightCase hsame

theorem completeNormalizeOperation_valid
    (schema : Schema) (operation : Operation) :
    completeNormalizeOperationValid schema operation := by
  intro hschema hoperation hfeasibleAll hsurvive
  apply completeNormalizeOperation_valid_of_branchPairs
      schema operation hschema hoperation hfeasibleAll hsurvive
  exact completeNormalizedBoolCaseBranchesFieldsCanMerge schema operation
    hschema hoperation hfeasibleAll hsurvive

end CompleteNormalization

end NormalForm

end GraphQL
