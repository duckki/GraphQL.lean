import Tests.NormalForm.Common

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm

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
              , stringFieldDefinition "homePlanet" ]
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

end NormalForm
end Tests
end GraphQL

