import Tests.Common

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

end Validation
end Tests
end GraphQL
