import Tests.NormalForm.Common
import GraphQL.NormalForm.GroundTypeNormalization.Normality

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm
open GraphQL.NormalForm.GroundTypeNormalization

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
