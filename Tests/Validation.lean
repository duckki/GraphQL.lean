import Tests.Common
import GraphQL.Validation
import GraphQL.Validation.SelectionValidity

namespace GraphQL
namespace Tests
namespace Validation

def duplicateEpisodeArguments : List Argument :=
  [ { name := "episode", value := .enum "NEWHOPE" }
  , { name := "episode", value := .enum "NEWHOPE" } ]

theorem duplicateArgumentNamesRejected :
    ¬ GraphQL.Validation.argumentsValid sampleSchema
      [testEpisodeArgumentDefinition] [] duplicateEpisodeArguments := by
  simp [GraphQL.Validation.argumentsValid, duplicateEpisodeArguments]

theorem duplicateArgumentOperationSelectionSetRejected :
    ¬ GraphQL.Validation.selectionSetValid sampleSchema []
      sampleDuplicateArgumentQuery.rootType
      sampleDuplicateArgumentQuery.selectionSet := by
  simp [GraphQL.Validation.selectionSetValid,
    GraphQL.Validation.selectionValid,
    GraphQL.Validation.fieldSelectionSetValid,
    GraphQL.Validation.argumentsValid,
    GraphQL.Validation.argumentValid,
    sampleDuplicateArgumentQuery, sampleSchema,
    testObjectFieldDefinition, testEpisodeArgumentDefinition,
    testStringFieldDefinition]

def interfaceDefaultedLimitArgument : InputValueDefinition :=
  { name := "limit"
    inputType := .nonNull (.named "Int")
    defaultValue := some (.int 10) }

def objectRequiredLimitArgument : InputValueDefinition :=
  { name := "limit", inputType := .nonNull (.named "Int") }

def interfaceImplementationArgumentSchema : Schema :=
  { queryType := "Query"
    types :=
      [ .object
          { name := "Query"
            fields := [testObjectFieldDefinition "node" "Node"]
            interfaces := [] }
      , .interface
          { name := "Node"
            fields :=
              [{ name := "value"
                 outputType := .named "String"
                 arguments := [interfaceDefaultedLimitArgument] }]
            interfaces := [] }
      , .object
          { name := "Human"
            fields :=
              [{ name := "value"
                 outputType := .named "String"
                 arguments := [objectRequiredLimitArgument] }]
            interfaces := ["Node"] } ] }

def missingImplementationArgumentQuery : Operation :=
  { name := some "MissingImplementationArgument"
    rootType := "Query"
    selectionSet :=
      [ .field "node" "node" [] [] [
          .field "value" "value" [] [] []
        ] ] }

theorem interfaceImplementationArgumentsRejected :
    ¬ GraphQL.Validation.operationDefinitionValid
      interfaceImplementationArgumentSchema
      missingImplementationArgumentQuery := by
  intro hvalid
  have himplementation :
      GraphQL.Validation.selectionSetImplementationValid
        interfaceImplementationArgumentSchema []
        missingImplementationArgumentQuery.rootType
        missingImplementationArgumentQuery.selectionSet :=
    GraphQL.Validation.operationDefinitionValid_selectionSetImplementationValid
      hvalid
  have hrootScope :
      GraphQL.Validation.selectionSetImplementationValidInScope
        interfaceImplementationArgumentSchema [] "Query"
        [ .field "node" "node" [] [] [
            .field "value" "value" [] [] []
          ] ] := by
    simpa [GraphQL.Validation.selectionSetImplementationValid,
      missingImplementationArgumentQuery] using himplementation.1
  have hnodeImpl :
      GraphQL.Validation.selectionImplementationValid
        interfaceImplementationArgumentSchema [] "Query"
        (.field "node" "node" [] [] [
          .field "value" "value" [] [] []
        ]) := by
    simpa [GraphQL.Validation.selectionSetImplementationValidInScope]
      using hrootScope.1
  have hnodeBranches :
      GraphQL.Validation.selectionSetImplementationValidInScope
        interfaceImplementationArgumentSchema [] "Node"
        [ .field "value" "value" [] [] [] ]
        ∧ ∀ objectType,
          objectType ∈ interfaceImplementationArgumentSchema.getPossibleTypes "Node" ->
            GraphQL.Validation.selectionSetImplementationValidInScope
              interfaceImplementationArgumentSchema [] objectType
              [ .field "value" "value" [] [] [] ] := by
    simpa [GraphQL.Validation.selectionImplementationValid,
      GraphQL.Validation.selectionValid,
      GraphQL.Validation.fieldSelectionSetValid,
      GraphQL.Validation.argumentsValid,
      GraphQL.Validation.argumentValid,
      interfaceImplementationArgumentSchema,
      testObjectFieldDefinition] using hnodeImpl.2
  have hhumanMem :
      "Human" ∈ interfaceImplementationArgumentSchema.getPossibleTypes "Node" := by
    native_decide
  have hhumanValueScope :
      GraphQL.Validation.selectionSetImplementationValidInScope
        interfaceImplementationArgumentSchema [] "Human"
        [ .field "value" "value" [] [] [] ] :=
    hnodeBranches.2 "Human" hhumanMem
  have hhumanValueImpl :
      GraphQL.Validation.selectionImplementationValid
        interfaceImplementationArgumentSchema [] "Human"
        (.field "value" "value" [] [] []) := by
    simpa [GraphQL.Validation.selectionSetImplementationValidInScope]
      using hhumanValueScope.1
  have hhumanValueValid :
      GraphQL.Validation.selectionValid
        interfaceImplementationArgumentSchema [] "Human"
        (.field "value" "value" [] [] []) := by
    simpa [GraphQL.Validation.selectionImplementationValid,
      interfaceImplementationArgumentSchema] using hhumanValueImpl.1
  have hhumanValueData :
      GraphQL.Validation.directivesValid
        interfaceImplementationArgumentSchema [] []
        ∧ ∃ fieldDefinition,
          interfaceImplementationArgumentSchema.lookupField "Human" "value" =
            some fieldDefinition
            ∧ GraphQL.Validation.argumentsValid
              interfaceImplementationArgumentSchema fieldDefinition.arguments [] []
            ∧ GraphQL.Validation.fieldSelectionSetValid
              interfaceImplementationArgumentSchema [] fieldDefinition [] := by
    simpa [GraphQL.Validation.selectionValid] using hhumanValueValid
  rcases hhumanValueData with ⟨_, fieldDefinition, hlookup,
    harguments, _⟩
  have hfield :
      fieldDefinition =
        { name := "value"
          outputType := .named "String"
          arguments := [objectRequiredLimitArgument] } := by
    have hlookupExpected :
        interfaceImplementationArgumentSchema.lookupField "Human" "value" =
          some
            { name := "value"
              outputType := .named "String"
              arguments := [objectRequiredLimitArgument] } := by
      rfl
    rw [hlookupExpected] at hlookup
    simpa using hlookup.symm
  subst fieldDefinition
  have hrequired :
      GraphQL.Validation.isRequiredArgument objectRequiredLimitArgument := by
    simp [GraphQL.Validation.isRequiredArgument,
      GraphQL.Validation.isRequiredInputValueDefinition,
      InputValueDefinition.isRequired,
      objectRequiredLimitArgument]
  have hmissing :=
    harguments.2.2 objectRequiredLimitArgument (by simp)
      hrequired
  rcases hmissing with ⟨argument, hget, _⟩
  simp [GraphQL.Validation.getArgument?] at hget

end Validation
end Tests
end GraphQL
