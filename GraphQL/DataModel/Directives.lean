import GraphQL.DataModel

/-!
Spec reference: GraphQL September 2025.
- 3.13.1 `@skip` and 3.13.2 `@include`: directive-sensitive data-model proof
  helpers for the scoped response-shape soundness fragment.
- Fidelity note: this module stays within the project scope from `GraphQL.DataModel`:
  directive arguments are assumed already coerced, and only modeled built-ins are handled.
-/
namespace GraphQL

namespace DataModel

theorem conditionFromDirectives?_satisfiable
    {directives : List DirectiveApplication} {condition : ResponseShape.Condition} :
    ResponseShape.Condition.fromDirectives? directives = some condition ->
      condition.satisfiableBool = true := by
  intro h
  induction directives generalizing condition with
  | nil =>
      simp [ResponseShape.Condition.fromDirectives?] at h
      cases h
      simp [ResponseShape.Condition.empty, ResponseShape.Condition.satisfiableBool,
        ResponseShape.Condition.hasContradictionBool,
        ResponseShape.Condition.possibleTypesEmptyBool,
        ResponseShape.BooleanLiteral.hasContradictionBool]
  | cons directive rest _ih =>
      simp [ResponseShape.Condition.fromDirectives?] at h
      cases hdirective : ResponseShape.Condition.fromDirective? directive with
      | none =>
          simp [hdirective] at h
      | some directiveCondition =>
          cases hrest : ResponseShape.Condition.fromDirectives? rest with
          | none =>
              simp [hdirective, hrest] at h
          | some restCondition =>
              simp [hdirective, hrest] at h
              rcases h with ⟨hsat, heq⟩
              rw [← heq]
              exact hsat

set_option linter.unusedSimpArgs false in
theorem responseShapeCorrectForTypedExecutionAtRoot_singleLeafWithDirectives
    (schema : Schema) (name : Option Name) (rootType : Name)
    (variableDefinitions : List VariableDefinition)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (directiveCondition : ResponseShape.Condition) :
    ResponseShape.Condition.fromDirectives? directives = some directiveCondition ->
      responseShapeCorrectForTypedExecutionAtRoot schema
        { name := name,
          rootType := rootType,
          variableDefinitions := variableDefinitions,
          selectionSet := [.field responseName fieldName arguments directives []] } := by
  intro hdirectives store variableValues root _hstore _hroot hrootType
  let operation : Semantic.Operation :=
    { name := name,
      rootType := rootType,
      variableDefinitions := variableDefinitions,
      selectionSet := [.field responseName fieldName arguments directives []] }
  have hrootType' : schema.typeIncludesObject rootType root.typeName := hrootType
  have hnonempty : ¬ schema.getPossibleTypes rootType = [] :=
    possibleTypes_nonempty_of_typeIncludesObject schema hrootType'
  have hdirectiveNone : directiveCondition.possibleTypes = none :=
    conditionFromDirectives?_possibleTypes_none hdirectives
  have hdirectiveSat : directiveCondition.satisfiableBool = true :=
    conditionFromDirectives?_satisfiable hdirectives
  have hinitialSat :
      (ResponseShape.Shape.semanticOperationInitialCondition schema operation).satisfiableBool
        = true := by
    simp [operation, ResponseShape.Shape.semanticOperationInitialCondition,
      ResponseShape.Condition.satisfiableBool,
      ResponseShape.Condition.hasContradictionBool,
      ResponseShape.Condition.possibleTypesEmptyBool, hnonempty,
      ResponseShape.BooleanLiteral.hasContradictionBool]
  have hfieldSat :
      ((ResponseShape.Shape.semanticOperationInitialCondition schema operation).and
        directiveCondition).satisfiableBool = true := by
    cases directiveCondition with
    | mk possibleTypes booleanLiterals =>
        simp at hdirectiveNone
        subst possibleTypes
        simp [operation, ResponseShape.Shape.semanticOperationInitialCondition,
          ResponseShape.Condition.and, ResponseShape.Condition.satisfiableBool,
          ResponseShape.Condition.hasContradictionBool,
          ResponseShape.Condition.possibleTypesEmptyBool, hnonempty] at hdirectiveSat ⊢
        exact hdirectiveSat
  cases hallows : Execution.selectionDirectivesAllowBool variableValues directives
  · simp [operation, TypedExecution.executeSemanticQuery,
      Execution.executeSemanticQueryFuel, Semantic.Operation.size,
      Semantic.SelectionSet.size, Semantic.Selection.size,
      TypedExecution.executeSelectionSet, Execution.collectFields,
      Execution.collectSelection, hallows, Execution.mergeExecutableGroups,
      Execution.addExecutableGroup, Execution.addExecutableFields,
      TypedExecution.executeCollectedFields, ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields, hdirectives, hinitialSat,
      hfieldSat, typedResponseConformsToShapeBool,
      typedFieldsConformToShapeBool]
  · have hdirectiveHolds :=
      conditionFromDirectives?_holds variableValues root.typeName directives
        directiveCondition hdirectives hallows
    have hinitial :=
      semanticOperationInitialCondition_holds schema variableValues operation hrootType'
    have hfieldCondition :
        conditionHoldsBool variableValues root.typeName
          ((ResponseShape.Shape.semanticOperationInitialCondition schema operation).and
            directiveCondition) = true :=
      conditionHoldsBool_and_right_none variableValues root.typeName
        (ResponseShape.Shape.semanticOperationInitialCondition schema operation)
        directiveCondition hinitial hdirectiveHolds hdirectiveNone
    simp [operation, TypedExecution.executeSemanticQuery,
      Execution.executeSemanticQueryFuel, Semantic.Operation.size,
      Semantic.SelectionSet.size, Semantic.Selection.size,
      TypedExecution.executeSelectionSet, Execution.collectFields,
      Execution.collectSelection, hallows, Execution.mergeExecutableGroups,
      Execution.addExecutableGroup, Execution.addExecutableFields,
      TypedExecution.executeCollectedFields, TypedExecution.executeField,
      Execution.mergedFieldSelectionSet, ResponseShape.Shape.ofSemanticOperation,
      ResponseShape.Shape.semanticOperationShapeFuel,
      ResponseShape.Shape.semanticSelectionSetShape,
      ResponseShape.Shape.collectSelectionSetShapeFields,
      ResponseShape.Shape.collectSelectionShapeFields, hdirectives,
      ResponseShape.Shape.empty, hinitialSat, hfieldSat,
      ResponseShape.Shape.mergeFields, ResponseShape.Shape.merge,
      ResponseShape.Shape.size, ResponseShape.Shape.fieldsSize,
      ResponseShape.Shape.variantsSize, ResponseShape.Shape.mergeWithFuel,
      ResponseShape.Shape.mergeFieldsWithFuel, typedResponseConformsToShapeBool,
      typedFieldsConformToShapeBool, typedVariantConformsToShapeBool,
      variantHeaderActiveBool, hfieldCondition, ResponseShape.Shape.lookupField]

end DataModel

end GraphQL
