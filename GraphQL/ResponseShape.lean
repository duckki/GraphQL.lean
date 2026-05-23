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
  def size : Shape -> Nat
    | .scalar => 1
    | .object fields => 1 + fieldsSize fields

  def fieldsSize : List (Name × Shape) -> Nat
    | [] => 0
    | (_name, shape) :: rest => shape.size + fieldsSize rest
end

def mergeWithFuel : Nat -> Shape -> Shape -> Shape
  | 0, left, _right => left
  | _fuel + 1, .scalar, .scalar => .scalar
  | fuel + 1, .object leftFields, .object rightFields =>
      .object (rightFields.foldl
        (fun fields (name, shape) =>
          let matching := fields.filter (fun field => field.fst == name)
          let rest := fields.filter (fun field => !(field.fst == name))
          match matching with
          | [] => fields ++ [(name, shape)]
          | (_existingName, existingShape) :: _ =>
              rest ++ [(name, mergeWithFuel fuel existingShape shape)])
        leftFields)
  | _fuel + 1, left, _right => left

def merge (left right : Shape) : Shape :=
  mergeWithFuel (left.size + right.size) left right

def mergeFields (left right : List (Name × Shape)) : List (Name × Shape) :=
  match merge (.object left) (.object right) with
  | .object fields => fields
  | .scalar => []

mutual
  def includesBool : Shape -> Shape -> Bool
    | .scalar, .scalar => true
    | .object requiredFields, .object availableFields =>
        includesFieldsBool requiredFields availableFields
    | _, _ => false

  def includesFieldsBool : List (Name × Shape) -> List (Name × Shape) -> Bool
    | [], _availableFields => true
    | (name, requiredShape) :: requiredRest, availableFields =>
        match lookup name availableFields with
        | none => false
        | some availableShape =>
            includesBool requiredShape availableShape
              && includesFieldsBool requiredRest availableFields
end

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

def equivalentBool (left right : Shape) : Bool :=
  includesBool left right && includesBool right left

mutual
  theorem includesBool_sound {required available : Shape} :
      includesBool required available = true -> Includes required available := by
    cases required <;> cases available <;> intro h <;> simp [includesBool] at h
    · exact Includes.scalar
    · exact Includes.object (includesFieldsBool_sound h)

  theorem includesFieldsBool_sound {required available : List (Name × Shape)} :
      includesFieldsBool required available = true ->
        IncludesFields required available := by
    cases required with
    | nil =>
        intro _h
        exact IncludesFields.nil
    | cons requiredField requiredRest =>
        cases requiredField with
        | mk name requiredShape =>
            intro h
            simp [includesFieldsBool] at h
            cases hlookup : lookup name available with
            | none =>
                simp [hlookup] at h
            | some availableShape =>
                simp [hlookup] at h
                exact IncludesFields.cons hlookup
                  (includesBool_sound h.left)
                  (includesFieldsBool_sound h.right)
end

mutual
  theorem includesBool_complete {required available : Shape} :
      Includes required available -> includesBool required available = true := by
    intro h
    cases h with
    | scalar =>
        simp [includesBool]
    | object hfields =>
        simp [includesBool, includesFieldsBool_complete hfields]

  theorem includesFieldsBool_complete {required available : List (Name × Shape)} :
      IncludesFields required available ->
        includesFieldsBool required available = true := by
    intro h
    cases h with
    | nil =>
        simp [includesFieldsBool]
    | cons hlookup hshape hrest =>
        simp [includesFieldsBool, hlookup, includesBool_complete hshape,
          includesFieldsBool_complete hrest]
end

theorem equivalentBool_sound {left right : Shape} :
    equivalentBool left right = true -> equivalent left right := by
  intro h
  simp [equivalentBool] at h
  exact And.intro (includesBool_sound h.left) (includesBool_sound h.right)

theorem equivalentBool_complete {left right : Shape} :
    equivalent left right -> equivalentBool left right = true := by
  intro h
  simp [equivalentBool, includesBool_complete h.left, includesBool_complete h.right]

theorem scalar_equivalent : equivalent scalar scalar := by
  exact And.intro Includes.scalar Includes.scalar

end Shape

end ResponseShape

end GraphQL
