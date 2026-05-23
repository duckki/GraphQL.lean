import GraphQL.DataModel

/-!
Spec reference: GraphQL September 2025.
- 6.3.2 `CollectFields` and 6.3.3 `ExecuteCollectedFields`: selection-set proof
  cases for multiple response names in the scoped data model.
- Fidelity note: this module stays inside the same query-only, already-coerced,
  data-only execution fragment as `GraphQL.DataModel`.
-/
namespace GraphQL

namespace DataModel

theorem groundNormalFormCorrect_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      groundNormalFormCorrect schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } := by
  intro hdistinct
  rw [groundNormalFormCorrect]
  rw [NormalForm.normalizeSemanticOperation_twoDistinctLeafNoDirectives
    schema name rootType variableDefinitions leftResponseName leftFieldName leftArguments
    rightResponseName rightFieldName rightArguments hdistinct]
  exact semanticOperationsEquivalentOnDataWithFuel_refl schema _ _

set_option linter.unusedSimpArgs false in
theorem normalFormPreservesResponseShapeBool_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      normalFormPreservesResponseShapeBool schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } = true := by
  intro hdistinct
  have hdistinct' : rightResponseName ≠ leftResponseName := Ne.symm hdistinct
  rw [normalFormPreservesResponseShapeBool]
  rw [NormalForm.normalizeSemanticOperation_twoDistinctLeafNoDirectives
    schema name rootType variableDefinitions leftResponseName leftFieldName leftArguments
    rightResponseName rightFieldName rightArguments hdistinct]
  by_cases hempty : schema.getPossibleTypes rootType = []
  · simp [ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields,
      ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
      ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.BooleanLiteral.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
      hempty, ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool]
  · simp [ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields,
      ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
      ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.BooleanLiteral.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool,
      ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
      hempty, hdistinct, hdistinct', ResponseShape.Shape.mergeFields,
      ResponseShape.Shape.merge, ResponseShape.Shape.size,
      ResponseShape.Shape.fieldsSize, ResponseShape.Shape.variantsSize,
      ResponseShape.Shape.mergeWithFuel, ResponseShape.Shape.mergeFieldsWithFuel,
      ResponseShape.Shape.equivalentBool, ResponseShape.Shape.includesBool,
      ResponseShape.Shape.includesFieldsBool, ResponseShape.Shape.includesVariantsBool,
      ResponseShape.Shape.lookupField, ResponseShape.Shape.lookupIncludingVariant,
      ResponseShape.VariantHeader.includedByBool_self,
      ResponseShape.Shape.empty_includesBool]

theorem normalFormPreservesResponseShape_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      normalFormPreservesResponseShape schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } := by
  intro hdistinct
  exact normalFormPreservesResponseShapeBool_sound schema _
    (normalFormPreservesResponseShapeBool_twoDistinctLeafNoDirectives schema name rootType
      variableDefinitions leftResponseName leftFieldName leftArguments rightResponseName
      rightFieldName rightArguments hdistinct)

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_twoDistinctLeafNoDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (leftResponseName leftFieldName : Name) (leftArguments : List Argument)
    (rightResponseName rightFieldName : Name) (rightArguments : List Argument) :
    leftResponseName ≠ rightResponseName ->
      responseShapeCorrectForTypedExecutionAtRoot schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [
            .field leftResponseName leftFieldName leftArguments [] [],
            .field rightResponseName rightFieldName rightArguments [] []
          ] } := by
  intro hdistinct store variableValues root _hstore _hroot hrootType
  have hrootType' : schema.typeIncludesObject rootType root.typeName := hrootType
  have hnonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType'
  simp [TypedExecution.executeSemanticQuery, Execution.executeSemanticQueryFuel,
    Semantic.Operation.size, Semantic.SelectionSet.size, Semantic.Selection.size,
    TypedExecution.executeSelectionSet, Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool, Execution.mergeExecutableGroups,
    Execution.addExecutableGroup, Execution.addExecutableFields,
    Execution.addExecutableField, hdistinct, TypedExecution.executeCollectedFields,
    TypedExecution.executeField, Execution.mergedFieldSelectionSet,
    ResponseShape.Shape.ofSemanticOperation,
    ResponseShape.Shape.semanticOperationShapeFuel,
    ResponseShape.Shape.semanticSelectionSetShape,
    ResponseShape.Shape.collectSelectionSetShapeFields,
    ResponseShape.Shape.collectSelectionShapeFields,
    ResponseShape.Condition.fromDirectives?, ResponseShape.Condition.empty,
    ResponseShape.Shape.empty, ResponseShape.Condition.satisfiableBool,
    ResponseShape.Condition.hasContradictionBool,
    ResponseShape.BooleanLiteral.hasContradictionBool,
    ResponseShape.Condition.possibleTypesEmptyBool,
    ResponseShape.Condition.and, ResponseShape.Shape.semanticOperationInitialCondition,
    hnonempty, ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
    ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
    ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
    ResponseShape.Shape.mergeFieldsWithFuel, typedResponseConformsToShapeBool,
    typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
    ResponseShape.Shape.lookupField]

end DataModel

end GraphQL
