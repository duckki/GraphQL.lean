import GraphQL.Schema

namespace GraphQL

namespace ResponseShape

inductive Shape where
  | scalar
  | object (fields : List (Name × Shape))
deriving Repr

namespace Shape

def lookup (name : Name) : List (Name × Shape) -> Option Shape
  | [] => none
  | (fieldName, shape) :: rest =>
      if fieldName = name then some shape else lookup name rest

mutual
  inductive Includes : Shape -> Shape -> Prop where
    | scalar : Includes .scalar .scalar
    | object {requiredFields availableFields : List (Name × Shape)} :
        IncludesFields requiredFields availableFields ->
          Includes (.object requiredFields) (.object availableFields)

  inductive IncludesFields : List (Name × Shape) -> List (Name × Shape) -> Prop where
    | nil {availableFields : List (Name × Shape)} :
        IncludesFields [] availableFields
    | cons {name : Name} {requiredShape : Shape} {requiredRest availableFields : List (Name × Shape)}
        {availableShape : Shape} :
        lookup name availableFields = some availableShape ->
          Includes requiredShape availableShape ->
            IncludesFields requiredRest availableFields ->
              IncludesFields ((name, requiredShape) :: requiredRest) availableFields
end

def includes (required available : Shape) : Prop :=
  Includes required available

def equivalent (left right : Shape) : Prop :=
  includes left right ∧ includes right left

theorem scalar_equivalent : equivalent scalar scalar := by
  exact And.intro Includes.scalar Includes.scalar

end Shape

end ResponseShape

end GraphQL
