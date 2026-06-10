import Tests.NormalForm.GroundTypeNormalization
import GraphQL.NormalForm.CompleteNormalization.Normality

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm
open GraphQL.NormalForm.GroundTypeNormalization

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

def completeNormalizationDuplicateIncludeInputQuery : Operation :=
  operationWith [
    .field "hero" "hero" [] [.include (.variable "x")] [
      .field "id" "id" [] [] []
    ],
    .field "hero" "hero" [] [.include (.variable "x")] [
      .field "name" "name" [] [] []
    ]
  ]

def completeNormalizationDuplicateIncludeOutputSnapshot : Operation :=
  operationWith [
    .inlineFragment none [.skip (.variable "x")] [],
    .inlineFragment none [.include (.variable "x")] [
      .field "hero" "hero" [] [] [
        .field "id" "id" [] [] []
      ],
      .field "hero" "hero" [] [] [
        .field "name" "name" [] [] []
      ]
    ]
  ]

theorem completeNormalizationDuplicateIncludeSmoke :
    operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationDuplicateIncludeInputQuery)
        completeNormalizationDuplicateIncludeOutputSnapshot = true := by
  native_decide

def completeNormalizationDuplicateSkipInputQuery : Operation :=
  operationWith [
    .field "hero" "hero" [] [.skip (.variable "x")] [
      .field "id" "id" [] [] []
    ],
    .field "hero" "hero" [] [.skip (.variable "x")] [
      .field "name" "name" [] [] []
    ]
  ]

def completeNormalizationDuplicateSkipOutputSnapshot : Operation :=
  operationWith [
    .inlineFragment none [.skip (.variable "x")] [
      .field "hero" "hero" [] [] [
        .field "id" "id" [] [] []
      ],
      .field "hero" "hero" [] [] [
        .field "name" "name" [] [] []
      ]
    ],
    .inlineFragment none [.include (.variable "x")] []
  ]

theorem completeNormalizationDuplicateSkipSmoke :
    operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationDuplicateSkipInputQuery)
        completeNormalizationDuplicateSkipOutputSnapshot = true := by
  native_decide

def completeNormalizationSpineConflictInputQuery : Operation :=
  operationWith [
    .inlineFragment none [.skip (.variable "x")] [
      .field "hero" "hero" [] [] [
        .field "id" "id" [] [] []
      ],
      .field "hero" "hero" [] [.include (.variable "x")] [
        .field "name" "name" [] [] []
      ]
    ]
  ]

def completeNormalizationSpineConflictOutputSnapshot : Operation :=
  operationWith [
    .inlineFragment none [.skip (.variable "x")] [
      .field "hero" "hero" [] [] [
        .field "id" "id" [] [] []
      ]
    ],
    .inlineFragment none [.include (.variable "x")] []
  ]

theorem completeNormalizationSpineConflictSmoke :
    operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationSpineConflictInputQuery)
        completeNormalizationSpineConflictOutputSnapshot = true := by
  native_decide

def completeNormalizationIncludeSkipInputQuery : Operation :=
  operationWith [
    .field "hero" "hero" [] [
      .include (.variable "x"),
      .skip (.variable "y")
    ] [
      .field "id" "id" [] [] []
    ]
  ]

def completeNormalizationIncludeSkipOutputSnapshot : Operation :=
  operationWith (completeNormalizationRootBoolCaseBranchesFor ["x", "y"] (fun
    | [("x", false), ("y", false)] => []
    | [("x", false), ("y", true)] => []
    | [("x", true), ("y", false)] =>
        [.field "hero" "hero" [] [] [
          .field "id" "id" [] [] [],
        ]]
    | [("x", true), ("y", true)] => []
    | _ => []))

theorem completeNormalizationIncludeSkipSmoke :
    operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationIncludeSkipInputQuery)
        completeNormalizationIncludeSkipOutputSnapshot = true := by
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

end NormalForm
end Tests
end GraphQL
