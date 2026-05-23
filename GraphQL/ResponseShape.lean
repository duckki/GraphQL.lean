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

def negatesBool : BooleanLiteral -> BooleanLiteral -> Bool
  | .positive left, .negative right => left == right
  | .negative left, .positive right => left == right
  | _, _ => false

def variableName : BooleanLiteral -> Name
  | .positive name => name
  | .negative name => name

def listEqBool : List BooleanLiteral -> List BooleanLiteral -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      eqBool left right && listEqBool leftRest rightRest
  | _, _ => false

def containsBool (literal : BooleanLiteral) : List BooleanLiteral -> Bool
  | [] => false
  | candidate :: rest =>
      eqBool literal candidate || containsBool literal rest

def containsNegationBool (literal : BooleanLiteral) : List BooleanLiteral -> Bool
  | [] => false
  | candidate :: rest =>
      negatesBool literal candidate || containsNegationBool literal rest

def hasContradictionBool : List BooleanLiteral -> Bool
  | [] => false
  | literal :: rest =>
      containsNegationBool literal rest || hasContradictionBool rest

def entailsAllBool (stronger weaker : List BooleanLiteral) : Bool :=
  weaker.all (fun literal => containsBool literal stronger)

def compatibleBool (left right : List BooleanLiteral) : Bool :=
  !(hasContradictionBool (left ++ right))

end BooleanLiteral

structure Condition where
  possibleTypes : Option (List Name)
  booleanLiterals : List BooleanLiteral
deriving Repr

namespace Condition

def empty : Condition :=
  { possibleTypes := none, booleanLiterals := [] }

def namesSubsetBool (left right : List Name) : Bool :=
  left.all (fun name => right.contains name)

def namesOverlapBool (left right : List Name) : Bool :=
  left.any (fun name => right.contains name)

def possibleTypesSubsetBool : Option (List Name) -> Option (List Name) -> Bool
  | none, none => true
  | none, some _right => false
  | some _left, none => true
  | some left, some right => namesSubsetBool left right

def possibleTypesOverlapBool : Option (List Name) -> Option (List Name) -> Bool
  | none, none => true
  | none, some right => right != []
  | some left, none => left != []
  | some left, some right => namesOverlapBool left right

def possibleTypesEmptyBool : Option (List Name) -> Bool
  | none => false
  | some names => names == []

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

def hasContradictionBool (condition : Condition) : Bool :=
  possibleTypesEmptyBool condition.possibleTypes
    || BooleanLiteral.hasContradictionBool condition.booleanLiterals

def satisfiableBool (condition : Condition) : Bool :=
  !(condition.hasContradictionBool)

def overlapsBool (left right : Condition) : Bool :=
  possibleTypesOverlapBool left.possibleTypes right.possibleTypes
    && BooleanLiteral.compatibleBool left.booleanLiterals right.booleanLiterals

def subsetBool (left right : Condition) : Bool :=
  possibleTypesSubsetBool left.possibleTypes right.possibleTypes
    && BooleanLiteral.entailsAllBool left.booleanLiterals right.booleanLiterals

def intersect? (left right : Condition) : Option Condition :=
  let combined := left.and right
  if combined.satisfiableBool then some combined else none

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
      let combined := directiveCondition.and restCondition
      if combined.satisfiableBool then some combined else none

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

def conditionsOverlapBool (left right : VariantHeader) : Bool :=
  Condition.overlapsBool left.fst right.fst

def conditionSubsetBool (left right : VariantHeader) : Bool :=
  Condition.subsetBool left.fst right.fst

def selectedFieldEqBool (left right : VariantHeader) : Bool :=
  SelectedField.eqBool left.snd right.snd

def compatibleBool (left right : VariantHeader) : Bool :=
  !(conditionsOverlapBool left right) || selectedFieldEqBool left right

def includedByBool (required available : VariantHeader) : Bool :=
  conditionSubsetBool required available && selectedFieldEqBool required available

def intersect? (left right : VariantHeader) : Option VariantHeader := do
  let condition <- Condition.intersect? left.fst right.fst
  if selectedFieldEqBool left right then
    some (condition, left.snd)
  else
    none

end VariantHeader

/--
`Shape` summarizes a selection set before ground-type normal form. It is not
itself normalized: variants under a response name are interpreted
disjunctively, and their conditions may overlap. For example, one response name
may contain both a variant for `field(arg: 1)` under `{T}` with child `{a}` and
a variant for the same field under `{T, U}` with child `{b}`; both variants may
be true.
-/
structure Shape where
  fields : List (Name × List (VariantHeader × Shape))
deriving Repr

namespace Shape

abbrev Variant := VariantHeader × Shape

def empty : Shape :=
  ⟨[]⟩

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

def lookupIncludingVariant (requiredHeader : VariantHeader) :
    List (VariantHeader × Shape) -> Option Shape
  | [] => none
  | (availableHeader, shape) :: rest =>
      if VariantHeader.includedByBool requiredHeader availableHeader then
        some shape
      else
        lookupIncludingVariant requiredHeader rest

def variantHeadersCompatibleBool (left right : Variant) : Bool :=
  VariantHeader.compatibleBool left.fst right.fst

def variantConditionsOverlapBool (left right : Variant) : Bool :=
  VariantHeader.conditionsOverlapBool left.fst right.fst

def variantsSelectSameFieldBool (left right : Variant) : Bool :=
  VariantHeader.selectedFieldEqBool left.fst right.fst

def variantCompatibleWithAllBool (variant : Variant) : List Variant -> Bool :=
  fun variants => variants.all (fun other => variantHeadersCompatibleBool variant other)

def variantsPairwiseCompatibleBool : List Variant -> Bool
  | [] => true
  | variant :: rest =>
      variantCompatibleWithAllBool variant rest
        && variantsPairwiseCompatibleBool rest

def responseNameVariantsCompatibleBool :
    List (Name × List Variant) -> Bool
  | [] => true
  | (_responseName, variants) :: rest =>
      variantsPairwiseCompatibleBool variants
        && responseNameVariantsCompatibleBool rest

def responseNameNotInFieldsBool (responseName : Name) :
    List (Name × List Variant) -> Bool
  | [] => true
  | (availableName, _variants) :: rest =>
      !(availableName == responseName)
        && responseNameNotInFieldsBool responseName rest

def responseNamesNodupBool :
    List (Name × List Variant) -> Bool
  | [] => true
  | (responseName, _variants) :: rest =>
      responseNameNotInFieldsBool responseName rest
        && responseNamesNodupBool rest

def responseNameNotInFields (responseName : Name)
    (fields : List (Name × List Variant)) : Prop :=
  responseNameNotInFieldsBool responseName fields = true

inductive ResponseNamesNodup :
    List (Name × List Variant) -> Prop where
  | nil : ResponseNamesNodup []
  | cons {responseName : Name} {variants : List Variant}
      {rest : List (Name × List Variant)} :
      responseNameNotInFields responseName rest ->
        ResponseNamesNodup rest ->
          ResponseNamesNodup ((responseName, variants) :: rest)

theorem responseNamesNodupBool_sound
    {fields : List (Name × List Variant)} :
    responseNamesNodupBool fields = true ->
      ResponseNamesNodup fields := by
  induction fields with
  | nil =>
      intro _h
      exact ResponseNamesNodup.nil
  | cons field rest ih =>
      cases field with
      | mk responseName variants =>
          intro h
          simp [responseNamesNodupBool] at h
          exact ResponseNamesNodup.cons h.left (ih h.right)

theorem responseNamesNodupBool_complete
    {fields : List (Name × List Variant)} :
    ResponseNamesNodup fields ->
      responseNamesNodupBool fields = true := by
  intro h
  cases h with
  | nil =>
      simp [responseNamesNodupBool]
  | cons hnotIn hrest =>
      simp [responseNamesNodupBool]
      exact And.intro hnotIn (responseNamesNodupBool_complete hrest)

def variantHeaderCompatible (left right : Variant) : Prop :=
  variantHeadersCompatibleBool left right = true

def variantCompatibleWithAll (variant : Variant) (variants : List Variant) : Prop :=
  ∀ other, other ∈ variants -> variantHeaderCompatible variant other

inductive VariantsPairwiseCompatible : List Variant -> Prop where
  | nil : VariantsPairwiseCompatible []
  | cons {variant : Variant} {rest : List Variant} :
      variantCompatibleWithAll variant rest ->
        VariantsPairwiseCompatible rest ->
          VariantsPairwiseCompatible (variant :: rest)

inductive ResponseNameVariantsCompatible :
    List (Name × List Variant) -> Prop where
  | nil : ResponseNameVariantsCompatible []
  | cons {responseName : Name} {variants : List Variant}
      {rest : List (Name × List Variant)} :
      VariantsPairwiseCompatible variants ->
        ResponseNameVariantsCompatible rest ->
          ResponseNameVariantsCompatible ((responseName, variants) :: rest)

theorem variantCompatibleWithAllBool_sound {variant : Variant}
    {variants : List Variant} :
    variantCompatibleWithAllBool variant variants = true ->
      variantCompatibleWithAll variant variants := by
  induction variants with
  | nil =>
      intro _h other hmem
      cases hmem
  | cons head rest _ih =>
      intro h other hmem
      simp [variantCompatibleWithAllBool] at h
      cases hmem with
      | head =>
          exact h.left
      | tail _ htail =>
          cases other with
          | mk header shape =>
              cases header with
              | mk condition selectedField =>
                  exact h.right condition selectedField shape htail

theorem variantCompatibleWithAllBool_complete {variant : Variant}
    {variants : List Variant} :
    variantCompatibleWithAll variant variants ->
      variantCompatibleWithAllBool variant variants = true := by
  induction variants with
  | nil =>
      intro _h
      simp [variantCompatibleWithAllBool]
  | cons head rest _ih =>
      intro h
      simp [variantCompatibleWithAllBool]
      exact And.intro
        (h head (by simp))
        (by
          intro condition selectedField shape hmem
          exact h ((condition, selectedField), shape) (by simp [hmem]))

theorem variantsPairwiseCompatibleBool_sound {variants : List Variant} :
    variantsPairwiseCompatibleBool variants = true ->
      VariantsPairwiseCompatible variants := by
  induction variants with
  | nil =>
      intro _h
      exact VariantsPairwiseCompatible.nil
  | cons variant rest ih =>
      intro h
      simp [variantsPairwiseCompatibleBool] at h
      exact VariantsPairwiseCompatible.cons
        (variantCompatibleWithAllBool_sound h.left)
        (ih h.right)

theorem variantsPairwiseCompatibleBool_complete {variants : List Variant} :
    VariantsPairwiseCompatible variants ->
      variantsPairwiseCompatibleBool variants = true := by
  intro h
  cases h with
  | nil =>
      simp [variantsPairwiseCompatibleBool]
  | cons hall hrest =>
      simp [variantsPairwiseCompatibleBool,
        variantCompatibleWithAllBool_complete hall,
        variantsPairwiseCompatibleBool_complete hrest]

theorem responseNameVariantsCompatibleBool_sound
    {fields : List (Name × List Variant)} :
    responseNameVariantsCompatibleBool fields = true ->
      ResponseNameVariantsCompatible fields := by
  induction fields with
  | nil =>
      intro _h
      exact ResponseNameVariantsCompatible.nil
  | cons field rest ih =>
      cases field with
      | mk responseName variants =>
          intro h
          simp [responseNameVariantsCompatibleBool] at h
          exact ResponseNameVariantsCompatible.cons
            (variantsPairwiseCompatibleBool_sound h.left)
            (ih h.right)

theorem responseNameVariantsCompatibleBool_complete
    {fields : List (Name × List Variant)} :
    ResponseNameVariantsCompatible fields ->
      responseNameVariantsCompatibleBool fields = true := by
  intro h
  cases h with
  | nil =>
      simp [responseNameVariantsCompatibleBool]
  | cons hvariants hrest =>
      simp [responseNameVariantsCompatibleBool,
        variantsPairwiseCompatibleBool_complete hvariants,
        responseNameVariantsCompatibleBool_complete hrest]

mutual
  def wellFormedBool : Shape -> Bool
    | ⟨fields⟩ =>
        responseNamesNodupBool fields
          && (responseNameVariantsCompatibleBool fields
            && fieldsWellFormedBool fields)

  def fieldsWellFormedBool : List (Name × List Variant) -> Bool
    | [] => true
    | (_responseName, variants) :: rest =>
        variantsWellFormedBool variants && fieldsWellFormedBool rest

  def variantsWellFormedBool : List Variant -> Bool
    | [] => true
    | (_header, shape) :: rest =>
        shape.wellFormedBool && variantsWellFormedBool rest
end

mutual
  inductive WellFormed : Shape -> Prop where
    | shape {fields : List (Name × List Variant)} :
        ResponseNamesNodup fields ->
          ResponseNameVariantsCompatible fields ->
          FieldsWellFormed fields ->
            WellFormed ⟨fields⟩

  inductive FieldsWellFormed :
      List (Name × List Variant) -> Prop where
    | nil : FieldsWellFormed []
    | cons {responseName : Name} {variants : List Variant}
        {rest : List (Name × List Variant)} :
        VariantsWellFormed variants ->
          FieldsWellFormed rest ->
            FieldsWellFormed ((responseName, variants) :: rest)

  inductive VariantsWellFormed : List Variant -> Prop where
    | nil : VariantsWellFormed []
    | cons {header : VariantHeader} {shape : Shape} {rest : List Variant} :
        WellFormed shape ->
          VariantsWellFormed rest ->
            VariantsWellFormed ((header, shape) :: rest)
end

def wellFormed (shape : Shape) : Prop :=
  WellFormed shape

theorem empty_wellFormed : wellFormed empty := by
  exact WellFormed.shape
    ResponseNamesNodup.nil
    ResponseNameVariantsCompatible.nil
    FieldsWellFormed.nil

mutual
  theorem wellFormedBool_sound {shape : Shape} :
      wellFormedBool shape = true -> WellFormed shape := by
    cases shape with
    | mk fields =>
        intro h
        simp [wellFormedBool] at h
        exact WellFormed.shape
          (responseNamesNodupBool_sound h.left)
          (responseNameVariantsCompatibleBool_sound h.right.left)
          (fieldsWellFormedBool_sound h.right.right)

  theorem fieldsWellFormedBool_sound
      {fields : List (Name × List Variant)} :
      fieldsWellFormedBool fields = true -> FieldsWellFormed fields := by
    cases fields with
    | nil =>
        intro _h
        exact FieldsWellFormed.nil
    | cons field rest =>
        cases field with
        | mk responseName variants =>
            intro h
            simp [fieldsWellFormedBool] at h
            exact FieldsWellFormed.cons
              (variantsWellFormedBool_sound h.left)
              (fieldsWellFormedBool_sound h.right)

  theorem variantsWellFormedBool_sound {variants : List Variant} :
      variantsWellFormedBool variants = true ->
        VariantsWellFormed variants := by
    cases variants with
    | nil =>
        intro _h
        exact VariantsWellFormed.nil
    | cons variant rest =>
        cases variant with
        | mk header shape =>
            intro h
            simp [variantsWellFormedBool] at h
            exact VariantsWellFormed.cons
              (wellFormedBool_sound h.left)
              (variantsWellFormedBool_sound h.right)
end

mutual
  theorem wellFormedBool_complete {shape : Shape} :
      WellFormed shape -> wellFormedBool shape = true := by
    intro h
    cases h with
    | shape hnodup hcompatible hfields =>
        simp [wellFormedBool,
          responseNamesNodupBool_complete hnodup,
          responseNameVariantsCompatibleBool_complete hcompatible,
          fieldsWellFormedBool_complete hfields]

  theorem fieldsWellFormedBool_complete
      {fields : List (Name × List Variant)} :
      FieldsWellFormed fields -> fieldsWellFormedBool fields = true := by
    intro h
    cases h with
    | nil =>
        simp [fieldsWellFormedBool]
    | cons hvariants hrest =>
        simp [fieldsWellFormedBool,
          variantsWellFormedBool_complete hvariants,
          fieldsWellFormedBool_complete hrest]

  theorem variantsWellFormedBool_complete {variants : List Variant} :
      VariantsWellFormed variants -> variantsWellFormedBool variants = true := by
    intro h
    cases h with
    | nil =>
        simp [variantsWellFormedBool]
    | cons hshape hrest =>
        simp [variantsWellFormedBool,
          wellFormedBool_complete hshape,
          variantsWellFormedBool_complete hrest]
end

theorem wellFormed_iff_bool {shape : Shape} :
    wellFormed shape <-> wellFormedBool shape = true := by
  exact Iff.intro wellFormedBool_complete wellFormedBool_sound

mutual
  def size : Shape -> Nat
    | ⟨fields⟩ => 1 + fieldsSize fields

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
    | fuel + 1, ⟨leftFields⟩, ⟨rightFields⟩ =>
        ⟨mergeFieldsWithFuel fuel leftFields rightFields⟩

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
  (merge ⟨left⟩ ⟨right⟩).fields

mutual
  def includesBool : Shape -> Shape -> Bool
    | ⟨requiredFields⟩, ⟨availableFields⟩ =>
        includesFieldsBool requiredFields availableFields

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
        match lookupIncludingVariant header availableVariants with
        | none => false
        | some availableShape =>
            includesBool requiredShape availableShape
              && includesVariantsBool requiredRest availableVariants
end

mutual
  inductive Includes : Shape -> Shape -> Prop where
    | shape {requiredFields availableFields : List (Name × List (VariantHeader × Shape))} :
        IncludesFields requiredFields availableFields ->
          Includes ⟨requiredFields⟩ ⟨availableFields⟩

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
        lookupIncludingVariant header availableVariants = some availableShape ->
          Includes requiredShape availableShape ->
            IncludesVariants requiredRest availableVariants ->
              IncludesVariants ((header, requiredShape) :: requiredRest) availableVariants
end

def includes (required available : Shape) : Prop :=
  Includes required available

theorem empty_includes (shape : Shape) : includes empty shape := by
  cases shape with
  | mk fields =>
      exact Includes.shape IncludesFields.nil

theorem empty_includesBool (shape : Shape) : includesBool empty shape = true := by
  cases shape with
  | mk fields =>
      simp [empty, includesBool, includesFieldsBool]

def equivalent (left right : Shape) : Prop :=
  includes left right ∧ includes right left

def equivalentBool (left right : Shape) : Bool :=
  includesBool left right && includesBool right left

theorem empty_equivalent : equivalent empty empty := by
  exact And.intro (empty_includes empty) (empty_includes empty)

theorem empty_equivalentBool : equivalentBool empty empty = true := by
  simp [equivalentBool, empty_includesBool]

mutual
  theorem includesBool_sound {required available : Shape} :
      includesBool required available = true -> Includes required available := by
    cases required with
    | mk requiredFields =>
        cases available with
        | mk availableFields =>
            intro h
            simp [includesBool] at h
            exact Includes.shape (includesFieldsBool_sound h)

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
            cases hlookup : lookupIncludingVariant header available with
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
    | shape hfields =>
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
            if fieldCondition.satisfiableBool then
              let childType := (schema.fieldReturnType? parentType fieldName).getD fieldName
              let childShape : Shape :=
                match selectionSet with
                | [] => empty
                | _ =>
                    ⟨operationSelectionSetShape schema fragments fuel
                      childType fieldCondition selectionSet⟩
              [(responseName, [((fieldCondition, selectedField fieldName arguments), childShape)])]
            else
              []
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
        if condition.satisfiableBool then
          mergeFields
            (operationSelectionShape schema fragments (fuel + 1) parentType condition selection)
            (operationSelectionSetShape schema fragments (fuel + 1) parentType condition rest)
        else
          []
end

def operationShapeFuel (operation : Operation) : Nat :=
  operation.size + 1

def operationInitialCondition (schema : Schema) (operation : Operation) : Condition :=
  { possibleTypes := some (schema.possibleObjectNames operation.rootType),
    booleanLiterals := [] }

def ofOperation (schema : Schema) (operation : Operation) : Shape :=
  ⟨operationSelectionSetShape schema operation.fragments
    (operationShapeFuel operation) operation.rootType
    (operationInitialCondition schema operation) operation.selectionSet⟩

end Shape

end ResponseShape

end GraphQL
