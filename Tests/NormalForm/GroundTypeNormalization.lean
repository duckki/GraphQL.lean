import Tests.NormalForm.Common
import GraphQL.NormalForm.GroundTypeNormalization.Normality
import GraphQL.NormalForm.CompleteNormalization.Normality

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm
open GraphQL.NormalForm.GroundTypeNormalization

def stringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .named "String", arguments := [] }

def objectFieldDefinition (name typeName : Name) : FieldDefinition :=
  { name := name, outputType := .named typeName, arguments := [] }

def groundTypingSchema : Schema :=
  { queryType := rootType
    types :=
      [ .object
          { name := rootType
            fields :=
              [ objectFieldDefinition "hero" "Human"
              , objectFieldDefinition "search" "Character" ]
            interfaces := [] }
      , .interface
          { name := "Character"
            fields :=
              [ stringFieldDefinition "id"
              , stringFieldDefinition "name" ]
            interfaces := [] }
      , .object
          { name := "Human"
            fields :=
              [ stringFieldDefinition "id"
              , stringFieldDefinition "name"
              , stringFieldDefinition "homePlanet"
              , objectFieldDefinition "companion" "Character" ]
            interfaces := ["Character"] }
      , .object
          { name := "Droid"
            fields :=
              [ stringFieldDefinition "id"
              , stringFieldDefinition "name"
              , stringFieldDefinition "primaryFunction" ]
            interfaces := ["Character"] } ] }

/-! Ground-typed normalization smoke tests use `*InputQuery` and `*OutputSnapshot` pairs. -/

def objectFieldInputQuery : Operation :=
  query {
    field "hero" {
      field "id",
      field "name"
    }
  }

def objectFieldOutputSnapshot : Operation :=
  query {
    field "hero" {
      field "id",
      field "name"
    }
  }

theorem objectFieldGroundTypingSmoke :
    operationWellFormedBool objectFieldInputQuery = true
      ∧ operationWellFormedBool objectFieldOutputSnapshot = true
      ∧ operationEqBool
        (normalizeOperation groundTypingSchema objectFieldInputQuery)
        objectFieldOutputSnapshot = true := by
  native_decide

theorem groundObjectTypesForObjectSmoke :
    groundObjectTypesForType groundTypingSchema "Human" = ["Human"] := by
  rfl

theorem groundObjectTypesForInterfaceSmoke :
    groundObjectTypesForType groundTypingSchema "Character" =
      ["Human", "Droid"] := by
  rfl

def objectFieldGroundLiftOutputSnapshot : Operation :=
  query {
    field "hero" {
      field "id",
      field "name"
    }
  }

theorem objectFieldGroundLiftSmoke :
    operationWellFormedBool objectFieldGroundLiftOutputSnapshot = true
      ∧ operationEqBool
        (groundLiftOperation groundTypingSchema objectFieldInputQuery)
        objectFieldGroundLiftOutputSnapshot = true := by
  native_decide

def abstractFieldInputQuery : Operation :=
  query {
    field "search" {
      field "id",
      on "Human" {
        field "homePlanet"
      }
    }
  }

def abstractFieldOutputSnapshot : Operation :=
  query {
    field "search" {
      on "Human" {
        field "id",
        field "homePlanet"
      },
      on "Droid" {
        field "id"
      }
    }
  }

theorem abstractFieldGroundTypingSmoke :
    operationWellFormedBool abstractFieldInputQuery = true
      ∧ operationWellFormedBool abstractFieldOutputSnapshot = true
      ∧ operationEqBool
        (normalizeOperation groundTypingSchema abstractFieldInputQuery)
        abstractFieldOutputSnapshot = true := by
  native_decide

def abstractFieldGroundLiftOutputSnapshot : Operation :=
  query {
    field "search" {
      on "Human" {
        field "id",
        on "Human" {
          field "homePlanet"
        }
      },
      on "Droid" {
        field "id",
        on "Human" {
          field "homePlanet"
        }
      }
    }
  }

theorem abstractFieldGroundLiftSmoke :
    operationWellFormedBool abstractFieldGroundLiftOutputSnapshot = true
      ∧ operationEqBool
        (groundLiftOperation groundTypingSchema abstractFieldInputQuery)
        abstractFieldGroundLiftOutputSnapshot = true := by
  native_decide

def duplicateFieldInputQuery : Operation :=
  query {
    field "hero" {
      field "id"
    },
    field "hero" {
      field "name"
    }
  }

def duplicateFieldOutputSnapshot : Operation :=
  query {
    field "hero" {
      field "id",
      field "name"
    }
  }

theorem duplicateFieldGroundTypingSmoke :
    operationWellFormedBool duplicateFieldInputQuery = true
      ∧ operationWellFormedBool duplicateFieldOutputSnapshot = true
      ∧ operationEqBool
        (normalizeOperation groundTypingSchema duplicateFieldInputQuery)
        duplicateFieldOutputSnapshot = true := by
  native_decide

def aliasedDuplicateFieldInputQuery : Operation :=
  operationWith [
    .field "lead" "hero" [] [] [
      Selection.field "id" "id" [] [] []
    ],
    .field "lead" "hero" [] [] [
      Selection.field "name" "name" [] [] []
    ]
  ]

def aliasedDuplicateFieldOutputSnapshot : Operation :=
  operationWith [
    .field "lead" "hero" [] [] [
      Selection.field "id" "id" [] [] [],
      Selection.field "name" "name" [] [] []
    ]
  ]

theorem aliasedDuplicateFieldGroundTypingSmoke :
    operationWellFormedBool aliasedDuplicateFieldInputQuery = true
      ∧ operationWellFormedBool aliasedDuplicateFieldOutputSnapshot = true
      ∧ operationEqBool
        (normalizeOperation groundTypingSchema aliasedDuplicateFieldInputQuery)
        aliasedDuplicateFieldOutputSnapshot = true := by
  native_decide

def untypedInlineFragmentInputQuery : Operation :=
  query {
    spread {
      field "hero" {
        field "id"
      }
    }
  }

def untypedInlineFragmentOutputSnapshot : Operation :=
  query {
    field "hero" {
      field "id"
    }
  }

theorem untypedInlineFragmentGroundTypingSmoke :
    operationWellFormedBool untypedInlineFragmentInputQuery = true
      ∧ operationWellFormedBool untypedInlineFragmentOutputSnapshot = true
      ∧ operationEqBool
        (normalizeOperation groundTypingSchema untypedInlineFragmentInputQuery)
        untypedInlineFragmentOutputSnapshot = true := by
  native_decide

def nonOverlappingInlineFragmentInputQuery : Operation :=
  query {
    field "hero" {
      field "id",
      on "Droid" {
        field "primaryFunction"
      }
    }
  }

def nonOverlappingInlineFragmentOutputSnapshot : Operation :=
  query {
    field "hero" {
      field "id"
    }
  }

theorem nonOverlappingInlineFragmentGroundTypingSmoke :
    operationWellFormedBool nonOverlappingInlineFragmentInputQuery = true
      ∧ operationWellFormedBool nonOverlappingInlineFragmentOutputSnapshot = true
      ∧ operationEqBool
        (normalizeOperation groundTypingSchema nonOverlappingInlineFragmentInputQuery)
        nonOverlappingInlineFragmentOutputSnapshot = true := by
  native_decide

def completeNormalizationDirectiveInputQuery : Operation :=
  operationWith [
    .field "hero" "hero" [] [] [
      .field "id" "id" [] [] [],
      .field "name" "name" [] [.include (.variable "x")] [],
      .inlineFragment none [.skip (.variable "y")] [
        .field "homePlanet" "homePlanet" [] [] []
      ]
    ]
  ]

def completeNormalizationRootBoolCaseBranchesFor
    (variables : List BoolVar)
    (selectionSetForCase : BoolCase -> List Selection) :
    List Selection :=
  List.flatten ((allBoolCases variables).map
    (fun boolCase =>
      wrapWithBoolCase boolCase
        (selectionSetForCase boolCase)))

def completeNormalizationDirectiveOutputSnapshot : Operation :=
  operationWith (completeNormalizationRootBoolCaseBranchesFor ["x", "y"] (fun
    | [("x", false), ("y", false)] =>
        [.field "hero" "hero" [] [] [
          .field "id" "id" [] [] [],
          .field "homePlanet" "homePlanet" [] [] []
        ]]
    | [("x", false), ("y", true)] =>
        [.field "hero" "hero" [] [] [
          .field "id" "id" [] [] []
        ]]
    | [("x", true), ("y", false)] =>
        [.field "hero" "hero" [] [] [
          .field "id" "id" [] [] [],
          .field "name" "name" [] [] [],
          .field "homePlanet" "homePlanet" [] [] []
        ]]
    | [("x", true), ("y", true)] =>
        [.field "hero" "hero" [] [] [
          .field "id" "id" [] [] [],
          .field "name" "name" [] [] []
        ]]
    | _ => []))

theorem completeNormalizationDirectiveSmoke :
    operationWellFormedBool completeNormalizationDirectiveOutputSnapshot = true
      ∧ operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationDirectiveInputQuery)
        completeNormalizationDirectiveOutputSnapshot = true := by
  native_decide

def completeNormalizationGlobalVariablesInputQuery : Operation :=
  operationWith [
    .field "hero" "hero" [] [] [
      .field "id" "id" [] [] [],
      .field "name" "name" [] [.include (.variable "y")] []
    ],
    .field "search" "search" [] [] [
      .field "id" "id" [] [.include (.variable "x")] []
    ]
  ]

def completeNormalizationGlobalVariablesOutputSnapshot : Operation :=
  operationWith (completeNormalizationRootBoolCaseBranchesFor ["y", "x"] (fun
    | [("y", false), ("x", false)] =>
        [
          .field "hero" "hero" [] [] [
            .field "id" "id" [] [] []
          ],
          .field "search" "search" [] [] [
            .inlineFragment (some "Human") [] [],
            .inlineFragment (some "Droid") [] []
          ]
        ]
    | [("y", false), ("x", true)] =>
        [
          .field "hero" "hero" [] [] [
            .field "id" "id" [] [] []
          ],
          .field "search" "search" [] [] [
            .inlineFragment (some "Human") [] [
              .field "id" "id" [] [] []
            ],
            .inlineFragment (some "Droid") [] [
              .field "id" "id" [] [] []
            ]
          ]
        ]
    | [("y", true), ("x", false)] =>
        [
          .field "hero" "hero" [] [] [
            .field "id" "id" [] [] [],
            .field "name" "name" [] [] []
          ],
          .field "search" "search" [] [] [
            .inlineFragment (some "Human") [] [],
            .inlineFragment (some "Droid") [] []
          ]
        ]
    | [("y", true), ("x", true)] =>
        [
          .field "hero" "hero" [] [] [
            .field "id" "id" [] [] [],
            .field "name" "name" [] [] []
          ],
          .field "search" "search" [] [] [
            .inlineFragment (some "Human") [] [
              .field "id" "id" [] [] []
            ],
            .inlineFragment (some "Droid") [] [
              .field "id" "id" [] [] []
            ]
          ]
        ]
    | _ => []))

theorem completeNormalizationGlobalVariablesSmoke :
    operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationGlobalVariablesInputQuery)
        completeNormalizationGlobalVariablesOutputSnapshot = true := by
  native_decide

def completeNormalizationAbstractInputQuery : Operation :=
  operationWith [
    .field "search" "search" [] [] [
      .field "id" "id" [] [] [],
      .inlineFragment (some "Human") [] [
        .field "homePlanet" "homePlanet" [] [] []
      ],
      .inlineFragment (some "Droid") [.include (.variable "x")] [
        .field "primaryFunction" "primaryFunction" [] [] []
      ]
    ]
  ]

def completeNormalizationAbstractOutputSnapshot : Operation :=
  operationWith (completeNormalizationRootBoolCaseBranchesFor ["x"] (fun
    | [("x", false)] =>
        [.field "search" "search" [] [] [
          .inlineFragment (some "Human") [] [
          .field "id" "id" [] [] [],
          .field "homePlanet" "homePlanet" [] [] []
          ],
          .inlineFragment (some "Droid") [] [
            .field "id" "id" [] [] []
          ]
        ]]
    | [("x", true)] =>
        [.field "search" "search" [] [] [
          .inlineFragment (some "Human") [] [
          .field "id" "id" [] [] [],
          .field "homePlanet" "homePlanet" [] [] []
          ],
          .inlineFragment (some "Droid") [] [
          .field "id" "id" [] [] [],
          .field "primaryFunction" "primaryFunction" [] [] []
          ]
        ]]
    | _ => []))

theorem completeNormalizationAbstractSmoke :
    operationWellFormedBool completeNormalizationAbstractOutputSnapshot = true
      ∧ operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationAbstractInputQuery)
        completeNormalizationAbstractOutputSnapshot = true := by
  native_decide

def completeNormalizationNestedDirectiveInputQuery : Operation :=
  operationWith [
    .field "hero" "hero" [] [] [
      .field "companion" "companion" [] [] [
        .field "id" "id" [] [.include (.variable "x")] []
      ]
    ]
  ]

def completeNormalizationNestedDirectiveOutputSnapshot : Operation :=
  operationWith (completeNormalizationRootBoolCaseBranchesFor ["x"] (fun
    | [("x", false)] =>
        [.field "hero" "hero" [] [] [
          .field "companion" "companion" [] [] [
          .inlineFragment (some "Human") [] [
            ],
            .inlineFragment (some "Droid") [] [
            ]
          ]
        ]]
    | [("x", true)] =>
        [.field "hero" "hero" [] [] [
          .field "companion" "companion" [] [] [
            .inlineFragment (some "Human") [] [
              .field "id" "id" [] [] []
            ],
            .inlineFragment (some "Droid") [] [
              .field "id" "id" [] [] []
            ]
          ]
        ]]
    | _ => []))

theorem completeNormalizationNestedDirectiveSmoke :
    operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationNestedDirectiveInputQuery)
        completeNormalizationNestedDirectiveOutputSnapshot = true := by
  native_decide

def completeNormalizationResolvers : Execution.Resolvers String :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => .object "Human" "hero"
      | "Query", "search" => .object "Human" "hero"
      | "Human", "id" => .scalar "human-id"
      | "Human", "name" => .scalar "human-name"
      | "Human", "homePlanet" => .scalar "earth"
      | "Human", "companion" => .object "Droid" "droid"
      | "Droid", "id" => .scalar "droid-id"
      | "Droid", "name" => .scalar "droid-name"
      | "Droid", "primaryFunction" => .scalar "protocol"
      | _, _ => .null }

def completeNormalizationVariableValues : Execution.VariableValues :=
  [("x", .boolean true), ("y", .boolean false)]

theorem completeNormalizationExecutionSmoke :
    responseEqBool
      (Execution.executeQueryAtDepth groundTypingSchema
        completeNormalizationResolvers completeNormalizationVariableValues
        completeNormalizationDirectiveInputQuery 12
        (.object "Query" "root"))
      (Execution.executeQueryAtDepth groundTypingSchema
        completeNormalizationResolvers completeNormalizationVariableValues
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationDirectiveInputQuery) 12
        (.object "Query" "root")) = true := by
  native_decide

theorem completeNormalizationNestedExecutionSmoke :
    responseEqBool
      (Execution.executeQueryAtDepth groundTypingSchema
        completeNormalizationResolvers completeNormalizationVariableValues
        completeNormalizationNestedDirectiveInputQuery 16
        (.object "Query" "root"))
      (Execution.executeQueryAtDepth groundTypingSchema
        completeNormalizationResolvers completeNormalizationVariableValues
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationNestedDirectiveInputQuery) 16
        (.object "Query" "root")) = true := by
  native_decide

theorem completeNormalizationSmokeInputsHaveCompleteShape :
    CompleteNormalization.completeSelectionSetShape
        (operationBoolVars
          completeNormalizationDirectiveInputQuery)
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationDirectiveInputQuery).selectionSet
      ∧ CompleteNormalization.completeSelectionSetShape
        (operationBoolVars
          completeNormalizationGlobalVariablesInputQuery)
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationGlobalVariablesInputQuery).selectionSet
      ∧ CompleteNormalization.completeSelectionSetShape
        (operationBoolVars
          completeNormalizationAbstractInputQuery)
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationAbstractInputQuery).selectionSet
      ∧ CompleteNormalization.completeSelectionSetShape
        (operationBoolVars
          completeNormalizationNestedDirectiveInputQuery)
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationNestedDirectiveInputQuery).selectionSet := by
  exact ⟨
    CompleteNormalization.completeNormalizeOperation_rootSelectionSetShape
      groundTypingSchema completeNormalizationDirectiveInputQuery,
    CompleteNormalization.completeNormalizeOperation_rootSelectionSetShape
      groundTypingSchema completeNormalizationGlobalVariablesInputQuery,
    CompleteNormalization.completeNormalizeOperation_rootSelectionSetShape
      groundTypingSchema completeNormalizationAbstractInputQuery,
    CompleteNormalization.completeNormalizeOperation_rootSelectionSetShape
      groundTypingSchema completeNormalizationNestedDirectiveInputQuery⟩

theorem normalizedSmokeInputsAreNormal
    (hschema : SchemaWellFormedness.schemaWellFormed groundTypingSchema) :
    operationNormal groundTypingSchema
        (normalizeOperation groundTypingSchema objectFieldInputQuery)
      ∧ operationNormal groundTypingSchema
        (normalizeOperation groundTypingSchema abstractFieldInputQuery)
      ∧ operationNormal groundTypingSchema
        (normalizeOperation groundTypingSchema duplicateFieldInputQuery)
      ∧ operationNormal groundTypingSchema
        (normalizeOperation groundTypingSchema aliasedDuplicateFieldInputQuery)
      ∧ operationNormal groundTypingSchema
        (normalizeOperation groundTypingSchema untypedInlineFragmentInputQuery)
      ∧ operationNormal groundTypingSchema
        (normalizeOperation groundTypingSchema nonOverlappingInlineFragmentInputQuery) := by
  exact ⟨
    normalizeOperation_normal groundTypingSchema hschema objectFieldInputQuery,
    normalizeOperation_normal groundTypingSchema hschema abstractFieldInputQuery,
    normalizeOperation_normal groundTypingSchema hschema duplicateFieldInputQuery,
    normalizeOperation_normal groundTypingSchema hschema aliasedDuplicateFieldInputQuery,
    normalizeOperation_normal groundTypingSchema hschema untypedInlineFragmentInputQuery,
    normalizeOperation_normal groundTypingSchema hschema
      nonOverlappingInlineFragmentInputQuery⟩

end NormalForm
end Tests
end GraphQL
