import GraphQL.Operation

namespace GraphQL

namespace ResponseShape

inductive BooleanLiteral where
  | positive (name : Name)
  | negative (name : Name)
deriving Repr

namespace BooleanLiteral

def eqBool : BooleanLiteral -> BooleanLiteral -> Bool
  | .positive left, .positive right => left == right
  | .negative left, .negative right => left == right
  | _, _ => false

def listEqBool : List BooleanLiteral -> List BooleanLiteral -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      eqBool left right && listEqBool leftRest rightRest
  | _, _ => false

end BooleanLiteral

structure Condition where
  possibleTypes : Option (List Name)
  booleanLiterals : List BooleanLiteral
deriving Repr

namespace Condition

def empty : Condition :=
  { possibleTypes := none, booleanLiterals := [] }

def withPossibleTypes (condition : Condition) (possibleTypes : List Name) : Condition :=
  { condition with possibleTypes := some possibleTypes }

def and (left right : Condition) : Condition :=
  {
    possibleTypes :=
      match left.possibleTypes, right.possibleTypes with
      | none, possibleTypes => possibleTypes
      | possibleTypes, none => possibleTypes
      | some leftTypes, some rightTypes =>
          some (leftTypes.filter (fun name => rightTypes.contains name)),
    booleanLiterals := left.booleanLiterals ++ right.booleanLiterals
  }

def namesEqBool : List Name -> List Name -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      (left == right) && namesEqBool leftRest rightRest
  | _, _ => false

def namesOptionEqBool : Option (List Name) -> Option (List Name) -> Bool
  | none, none => true
  | some left, some right => namesEqBool left right
  | _, _ => false

def eqBool (left right : Condition) : Bool :=
  namesOptionEqBool left.possibleTypes right.possibleTypes
    && BooleanLiteral.listEqBool left.booleanLiterals right.booleanLiterals

def fromDirective? : DirectiveApplication -> Option Condition
  | .include (.boolean Bool.true) => some empty
  | .include (.boolean Bool.false) => none
  | .include (.variable name) =>
      some { possibleTypes := none, booleanLiterals := [.positive name] }
  | .skip (.boolean Bool.false) => some empty
  | .skip (.boolean Bool.true) => none
  | .skip (.variable name) =>
      some { possibleTypes := none, booleanLiterals := [.negative name] }
  | _ => none

def fromDirectives? : List DirectiveApplication -> Option Condition
  | [] => some empty
  | directive :: rest => do
      let directiveCondition <- fromDirective? directive
      let restCondition <- fromDirectives? rest
      some (directiveCondition.and restCondition)

end Condition

structure SelectedField where
  fieldName : Name
  arguments : List Argument
deriving Repr

namespace SelectedField

mutual
  def inputValueEqBool : InputValue -> InputValue -> Bool
    | .null, .null => true
    | .int left, .int right => left == right
    | .float left, .float right => left == right
    | .string left, .string right => left == right
    | .boolean left, .boolean right => left == right
    | .enum left, .enum right => left == right
    | .list left, .list right => inputValuesEqBool left right
    | .object left, .object right => inputFieldsEqBool left right
    | .variable left, .variable right => left == right
    | _, _ => false

  def inputValuesEqBool : List InputValue -> List InputValue -> Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        inputValueEqBool left right && inputValuesEqBool leftRest rightRest
    | _, _ => false

  def inputFieldsEqBool : List (Name × InputValue) -> List (Name × InputValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: leftRest, (rightName, rightValue) :: rightRest =>
        (leftName == rightName)
          && inputValueEqBool leftValue rightValue
          && inputFieldsEqBool leftRest rightRest
    | _, _ => false
end

def argumentEqBool (left right : Argument) : Bool :=
  (left.name == right.name) && inputValueEqBool left.value right.value

def argumentsEqBool : List Argument -> List Argument -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      argumentEqBool left right && argumentsEqBool leftRest rightRest
  | _, _ => false

def eqBool (left right : SelectedField) : Bool :=
  (left.fieldName == right.fieldName)
    && argumentsEqBool left.arguments right.arguments

end SelectedField

def selectedField (fieldName : Name) (arguments : List Argument) :
    SelectedField :=
  { fieldName := fieldName, arguments := arguments }

abbrev VariantHeader := Condition × SelectedField

namespace VariantHeader

def eqBool (left right : VariantHeader) : Bool :=
  Condition.eqBool left.fst right.fst
    && SelectedField.eqBool left.snd right.snd

end VariantHeader

/--
`Shape` summarizes an operation before ground-type normal form. It is not itself
normalized: variants under a response key are interpreted disjunctively, and
their conditions may overlap. For example, one response key may contain both a
variant for `field(arg: 1)` under `{T}` with child `{a}` and a variant for the
same field under `{T, U}` with child `{b}`; both variants may be true.
-/
inductive Shape where
  | scalar
  | object (fields : List (Name × List (VariantHeader × Shape)))
deriving Repr

namespace Shape

def lookupField (responseName : Name) :
    List (Name × List (VariantHeader × Shape)) -> Option (List (VariantHeader × Shape))
  | [] => none
  | (availableName, variants) :: rest =>
      if availableName == responseName then some variants else lookupField responseName rest

def lookupVariant (header : VariantHeader) :
    List (VariantHeader × Shape) -> Option Shape
  | [] => none
  | (availableHeader, shape) :: rest =>
      if VariantHeader.eqBool availableHeader header then
        some shape
      else
        lookupVariant header rest

mutual
  def size : Shape -> Nat
    | .scalar => 1
    | .object fields => 1 + fieldsSize fields

  def fieldsSize : List (Name × List (VariantHeader × Shape)) -> Nat
    | [] => 0
    | (_responseName, variants) :: rest => variantsSize variants + fieldsSize rest

  def variantsSize : List (VariantHeader × Shape) -> Nat
    | [] => 0
    | (_header, shape) :: rest => shape.size + variantsSize rest
end

mutual
  def mergeWithFuel : Nat -> Shape -> Shape -> Shape
    | 0, left, _right => left
    | _fuel + 1, .scalar, .scalar => .scalar
    | fuel + 1, .object leftFields, .object rightFields =>
        .object (mergeFieldsWithFuel fuel leftFields rightFields)
    | _fuel + 1, left, _right => left

  def mergeFieldsWithFuel : Nat ->
      List (Name × List (VariantHeader × Shape)) ->
      List (Name × List (VariantHeader × Shape)) ->
      List (Name × List (VariantHeader × Shape))
    | 0, left, _right => left
    | _fuel + 1, left, [] => left
    | fuel + 1, left, (responseName, variants) :: rightRest =>
        let matching := left.filter (fun field => field.fst == responseName)
        let rest := left.filter (fun field => !(field.fst == responseName))
        let merged :=
          match matching with
          | [] => variants
          | (_existingName, existingVariants) :: _ =>
              mergeVariantsWithFuel fuel existingVariants variants
        mergeFieldsWithFuel fuel (rest ++ [(responseName, merged)]) rightRest

  def mergeVariantsWithFuel : Nat ->
      List (VariantHeader × Shape) ->
      List (VariantHeader × Shape) ->
      List (VariantHeader × Shape)
    | 0, left, _right => left
    | _fuel + 1, left, [] => left
    | fuel + 1, left, (header, shape) :: rightRest =>
        let matching := left.filter (fun variant => VariantHeader.eqBool variant.fst header)
        let rest := left.filter (fun variant => !(VariantHeader.eqBool variant.fst header))
        let merged :=
          match matching with
          | [] => (header, shape)
          | (existingHeader, existingShape) :: _ =>
              (existingHeader, mergeWithFuel fuel existingShape shape)
        mergeVariantsWithFuel fuel (rest ++ [merged]) rightRest
end

def merge (left right : Shape) : Shape :=
  mergeWithFuel (left.size + right.size) left right

def mergeFields (left right : List (Name × List (VariantHeader × Shape))) :
    List (Name × List (VariantHeader × Shape)) :=
  match merge (.object left) (.object right) with
  | .object fields => fields
  | _ => []

mutual
  def includesBool : Shape -> Shape -> Bool
    | .scalar, .scalar => true
    | .object requiredFields, .object availableFields =>
        includesFieldsBool requiredFields availableFields
    | _, _ => false

  def includesFieldsBool :
      List (Name × List (VariantHeader × Shape)) ->
      List (Name × List (VariantHeader × Shape)) ->
      Bool
    | [], _availableFields => true
    | (responseName, requiredVariants) :: requiredRest, availableFields =>
        match lookupField responseName availableFields with
        | none => false
        | some availableVariants =>
            includesVariantsBool requiredVariants availableVariants
              && includesFieldsBool requiredRest availableFields

  def includesVariantsBool :
      List (VariantHeader × Shape) -> List (VariantHeader × Shape) -> Bool
    | [], _availableVariants => true
    | (header, requiredShape) :: requiredRest, availableVariants =>
        match lookupVariant header availableVariants with
        | none => false
        | some availableShape =>
            includesBool requiredShape availableShape
              && includesVariantsBool requiredRest availableVariants
end

mutual
  inductive Includes : Shape -> Shape -> Prop where
    | scalar : Includes .scalar .scalar
    | object {requiredFields availableFields : List (Name × List (VariantHeader × Shape))} :
        IncludesFields requiredFields availableFields ->
          Includes (.object requiredFields) (.object availableFields)

  inductive IncludesFields :
      List (Name × List (VariantHeader × Shape)) ->
      List (Name × List (VariantHeader × Shape)) ->
      Prop where
    | nil {availableFields : List (Name × List (VariantHeader × Shape))} :
        IncludesFields [] availableFields
    | cons {responseName : Name} {requiredVariants requiredRest availableFields}
        {availableVariants : List (VariantHeader × Shape)} :
        lookupField responseName availableFields = some availableVariants ->
          IncludesVariants requiredVariants availableVariants ->
            IncludesFields requiredRest availableFields ->
              IncludesFields ((responseName, requiredVariants) :: requiredRest) availableFields

  inductive IncludesVariants :
      List (VariantHeader × Shape) -> List (VariantHeader × Shape) -> Prop where
    | nil {availableVariants : List (VariantHeader × Shape)} :
        IncludesVariants [] availableVariants
    | cons {header : VariantHeader} {requiredShape : Shape}
        {requiredRest availableVariants : List (VariantHeader × Shape)}
        {availableShape : Shape} :
        lookupVariant header availableVariants = some availableShape ->
          Includes requiredShape availableShape ->
            IncludesVariants requiredRest availableVariants ->
              IncludesVariants ((header, requiredShape) :: requiredRest) availableVariants
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

  theorem includesFieldsBool_sound
      {required available : List (Name × List (VariantHeader × Shape))} :
      includesFieldsBool required available = true ->
        IncludesFields required available := by
    cases required with
    | nil =>
        intro _h
        exact IncludesFields.nil
    | cons requiredField requiredRest =>
        cases requiredField with
        | mk responseName requiredVariants =>
            intro h
            simp [includesFieldsBool] at h
            cases hlookup : lookupField responseName available with
            | none =>
                simp [hlookup] at h
            | some availableVariants =>
                simp [hlookup] at h
                exact IncludesFields.cons hlookup
                  (includesVariantsBool_sound h.left)
                  (includesFieldsBool_sound h.right)

  theorem includesVariantsBool_sound
      {required available : List (VariantHeader × Shape)} :
      includesVariantsBool required available = true ->
        IncludesVariants required available := by
    cases required with
    | nil =>
        intro _h
        exact IncludesVariants.nil
    | cons requiredVariant requiredRest =>
        cases requiredVariant with
        | mk header requiredShape =>
            intro h
            simp [includesVariantsBool] at h
            cases hlookup : lookupVariant header available with
            | none =>
                simp [hlookup] at h
            | some availableShape =>
                simp [hlookup] at h
                exact IncludesVariants.cons hlookup
                  (includesBool_sound h.left)
                  (includesVariantsBool_sound h.right)
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

  theorem includesFieldsBool_complete
      {required available : List (Name × List (VariantHeader × Shape))} :
      IncludesFields required available ->
        includesFieldsBool required available = true := by
    intro h
    cases h with
    | nil =>
        simp [includesFieldsBool]
    | cons hlookup hvariants hrest =>
        simp [includesFieldsBool, hlookup, includesVariantsBool_complete hvariants,
          includesFieldsBool_complete hrest]

  theorem includesVariantsBool_complete
      {required available : List (VariantHeader × Shape)} :
      IncludesVariants required available ->
        includesVariantsBool required available = true := by
    intro h
    cases h with
    | nil =>
        simp [includesVariantsBool]
    | cons hlookup hshape hrest =>
        simp [includesVariantsBool, hlookup, includesBool_complete hshape,
          includesVariantsBool_complete hrest]
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

def restrictConditionToType (schema : Schema) (condition : Condition)
    (typeCondition : Name) : Condition :=
  let allowedTypes := schema.possibleObjectNames typeCondition
  let possibleTypes :=
    match condition.possibleTypes with
    | none => allowedTypes
    | some currentTypes => currentTypes.filter (fun name => allowedTypes.contains name)
  condition.withPossibleTypes possibleTypes

mutual
  def operationSelectionShape (schema : Schema) (fragments : List FragmentDefinition) :
      Nat -> Name -> Condition -> Selection ->
        List (Name × List (VariantHeader × Shape))
    | 0, _parentType, _condition, _selection => []
    | fuel + 1, parentType, condition,
        .field responseName fieldName arguments directives selectionSet =>
        match Condition.fromDirectives? directives with
        | none => []
        | some directiveCondition =>
            let fieldCondition := condition.and directiveCondition
            let childType := (schema.fieldReturnType? parentType fieldName).getD fieldName
            let childShape :=
              match selectionSet with
              | [] => .scalar
              | _ =>
                  .object (operationSelectionSetShape schema fragments fuel
                    childType fieldCondition selectionSet)
            [(responseName, [((fieldCondition, selectedField fieldName arguments), childShape)])]
    | fuel + 1, _parentType, condition, .fragmentSpread fragmentName directives =>
        match Condition.fromDirectives? directives with
        | none => []
        | some directiveCondition =>
            match QueryAux.findFragment? fragments fragmentName with
            | none => []
            | some fragment =>
                let nextCondition :=
                  restrictConditionToType schema (condition.and directiveCondition)
                    fragment.typeCondition
                operationSelectionSetShape schema fragments fuel
                  fragment.typeCondition nextCondition fragment.selectionSet
    | fuel + 1, parentType, condition, .inlineFragment none directives selectionSet =>
        match Condition.fromDirectives? directives with
        | none => []
        | some directiveCondition =>
            operationSelectionSetShape schema fragments fuel parentType
              (condition.and directiveCondition) selectionSet
    | fuel + 1, _parentType, condition,
        .inlineFragment (some typeCondition) directives selectionSet =>
        match Condition.fromDirectives? directives with
        | none => []
        | some directiveCondition =>
            let nextCondition :=
              restrictConditionToType schema (condition.and directiveCondition)
                typeCondition
            operationSelectionSetShape schema fragments fuel
              typeCondition nextCondition selectionSet

  def operationSelectionSetShape (schema : Schema) (fragments : List FragmentDefinition) :
      Nat -> Name -> Condition -> List Selection ->
        List (Name × List (VariantHeader × Shape))
    | 0, _parentType, _condition, _selectionSet => []
    | _fuel + 1, _parentType, _condition, [] => []
    | fuel + 1, parentType, condition, selection :: rest =>
        mergeFields
          (operationSelectionShape schema fragments (fuel + 1) parentType condition selection)
          (operationSelectionSetShape schema fragments (fuel + 1) parentType condition rest)
end

def operationShapeFuel (operation : Operation) : Nat :=
  operation.size + 1

def operationInitialCondition (schema : Schema) (operation : Operation) : Condition :=
  { possibleTypes := some (schema.possibleObjectNames operation.rootType),
    booleanLiterals := [] }

def ofOperation (schema : Schema) (operation : Operation) : Shape :=
  .object (operationSelectionSetShape schema operation.fragments
    (operationShapeFuel operation) operation.rootType
    (operationInitialCondition schema operation) operation.selectionSet)

end Shape

end ResponseShape

end GraphQL
