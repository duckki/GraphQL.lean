import Tests.NormalForm.GroundTypeNormalization

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm

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

end NormalForm
end Tests
end GraphQL
