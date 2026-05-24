import GraphQL.Semantic

/-!
Spec reference: GraphQL September 2025.
- 2.8 Field Alias and 6.3.2 Field Collection: response names are the keys used to group
  selected fields.
- 3.13.1 `@skip`, 3.13.2 `@include`, and 5.5.2.3 `GetPossibleTypes`: shape variants record
  Boolean directive conditions and possible runtime object types.
- 5.3.2 Field Selection Merging: selected-field compatibility is tracked structurally for
  same response names.
- Fidelity note: response shapes are not a GraphQL spec definition. They are a
  project-specific abstraction of possible response-name variants; they intentionally omit
  concrete result values, object identity, list/null completion, argument coercion, and
  execution errors.
-/
namespace GraphQL

namespace ResponseShape

-- Spec-inspired Boolean condition atom for 3.13.1 `@skip` and 3.13.2 `@include`; non-spec
-- helper used to summarize variable-dependent directive conditions.
inductive BooleanLiteral where
  | positive (name : Name)
  | negative (name : Name)
deriving Repr

namespace BooleanLiteral

-- Spec-inspired equality over directive-condition literals: non-spec boolean decision
-- helper.
def eqBool : BooleanLiteral -> BooleanLiteral -> Bool
  | .positive left, .positive right => left == right
  | .negative left, .negative right => left == right
  | _, _ => false

-- Spec-inspired contradiction check for modeled directive-condition literals.
def negatesBool : BooleanLiteral -> BooleanLiteral -> Bool
  | .positive left, .negative right => left == right
  | .negative left, .positive right => left == right
  | _, _ => false

-- Non-spec helper exposing the variable referenced by a modeled directive literal.
def variableName : BooleanLiteral -> Name
  | .positive name => name
  | .negative name => name

-- Boolean list equality for the non-spec directive-condition literal representation.
def listEqBool : List BooleanLiteral -> List BooleanLiteral -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      eqBool left right && listEqBool leftRest rightRest
  | _, _ => false

-- Non-spec membership test using `BooleanLiteral.eqBool`.
def containsBool (literal : BooleanLiteral) : List BooleanLiteral -> Bool
  | [] => false
  | candidate :: rest =>
      eqBool literal candidate || containsBool literal rest

-- Non-spec contradiction search for one directive-condition literal.
def containsNegationBool (literal : BooleanLiteral) : List BooleanLiteral -> Bool
  | [] => false
  | candidate :: rest =>
      negatesBool literal candidate || containsNegationBool literal rest

-- Spec-inspired satisfiability helper for conjunctions of modeled directive literals.
def hasContradictionBool : List BooleanLiteral -> Bool
  | [] => false
  | literal :: rest =>
      containsNegationBool literal rest || hasContradictionBool rest

-- Spec-inspired condition implication: the stronger condition must contain all weaker
-- directive literals.
def entailsAllBool (stronger weaker : List BooleanLiteral) : Bool :=
  weaker.all (fun literal => containsBool literal stronger)

-- Spec-inspired condition compatibility: combined directive literals must be satisfiable.
def compatibleBool (left right : List BooleanLiteral) : Bool :=
  !(hasContradictionBool (left ++ right))

theorem eqBool_self (literal : BooleanLiteral) :
    eqBool literal literal = true := by
  cases literal <;> simp [eqBool]

theorem listEqBool_self (literals : List BooleanLiteral) :
    listEqBool literals literals = true := by
  induction literals with
  | nil =>
      simp [listEqBool]
  | cons literal rest ih =>
      simp [listEqBool, eqBool_self literal, ih]

theorem containsBool_of_mem {literal : BooleanLiteral}
    {literals : List BooleanLiteral} :
    literal ∈ literals -> containsBool literal literals = true := by
  intro hmem
  induction literals with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases hmem with
      | head =>
          simp [containsBool, eqBool_self]
      | tail _ htail =>
          simp [containsBool, ih htail]

theorem containsBool_self (literal : BooleanLiteral)
    (literals : List BooleanLiteral) :
    containsBool literal (literal :: literals) = true := by
  exact containsBool_of_mem (by simp)

theorem entailsAllBool_self (literals : List BooleanLiteral) :
    entailsAllBool literals literals = true := by
  simp [entailsAllBool]
  intro literal hmem
  exact containsBool_of_mem hmem

end BooleanLiteral

-- Spec-inspired runtime condition: combines 5.5.2.3 possible object types with 3.13
-- Boolean directive literals; not a GraphQL spec data structure.
structure Condition where
  possibleTypes : Option (List Name)
  booleanLiterals : List BooleanLiteral
deriving Repr

namespace Condition

-- Non-spec empty response-shape condition: no type restriction and no directive literal.
def empty : Condition :=
  { possibleTypes := none, booleanLiterals := [] }

-- Spec-inspired possible-type set inclusion helper.
def namesSubsetBool (left right : List Name) : Bool :=
  left.all (fun name => right.contains name)

-- Spec-inspired possible-type set overlap helper.
def namesOverlapBool (left right : List Name) : Bool :=
  left.any (fun name => right.contains name)

-- Spec-inspired possible-type condition inclusion. `none` represents an unrestricted
-- type condition, not the empty set.
def possibleTypesSubsetBool : Option (List Name) -> Option (List Name) -> Bool
  | none, none => true
  | none, some _right => false
  | some _left, none => true
  | some left, some right => namesSubsetBool left right

-- Spec-inspired possible-type condition overlap. `none` represents an unrestricted
-- type condition, not the empty set.
def possibleTypesOverlapBool : Option (List Name) -> Option (List Name) -> Bool
  | none, none => true
  | none, some right => right != []
  | some left, none => left != []
  | some left, some right => namesOverlapBool left right

-- Non-spec helper detecting an unsatisfiable possible-type restriction.
def possibleTypesEmptyBool : Option (List Name) -> Bool
  | none => false
  | some names => names == []

-- Spec-inspired condition update for a known possible runtime type set.
def withPossibleTypes (condition : Condition) (possibleTypes : List Name) : Condition :=
  { condition with possibleTypes := some possibleTypes }

-- Spec-inspired child-shape condition transfer: child fields are constrained by the
-- field return type's possible runtime types, while directive literals remain in scope.
def forChildType (schema : Schema) (condition : Condition) (childType : Name) : Condition :=
  { possibleTypes := some (schema.getPossibleTypes childType),
    booleanLiterals := condition.booleanLiterals }

@[simp]
theorem forChildType_possibleTypes (schema : Schema)
    (condition : Condition) (childType : Name) :
    (forChildType schema condition childType).possibleTypes
      = some (schema.getPossibleTypes childType) := by
  rfl

@[simp]
theorem forChildType_booleanLiterals (schema : Schema)
    (condition : Condition) (childType : Name) :
    (forChildType schema condition childType).booleanLiterals
      = condition.booleanLiterals := by
  rfl

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

-- Non-spec ordered-name equality for the response-shape condition encoding.
def namesEqBool : List Name -> List Name -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      (left == right) && namesEqBool leftRest rightRest
  | _, _ => false

-- Non-spec equality for optional possible-type lists.
def namesOptionEqBool : Option (List Name) -> Option (List Name) -> Bool
  | none, none => true
  | some left, some right => namesEqBool left right
  | _, _ => false

-- Non-spec equality for the response-shape condition encoding.
def eqBool (left right : Condition) : Bool :=
  namesOptionEqBool left.possibleTypes right.possibleTypes
    && BooleanLiteral.listEqBool left.booleanLiterals right.booleanLiterals

-- Spec-inspired unsatisfiability check for combined possible-type and directive
-- conditions.
def hasContradictionBool (condition : Condition) : Bool :=
  possibleTypesEmptyBool condition.possibleTypes
    || BooleanLiteral.hasContradictionBool condition.booleanLiterals

-- Spec-inspired condition satisfiability check.
def satisfiableBool (condition : Condition) : Bool :=
  !(condition.hasContradictionBool)

-- Spec-inspired condition overlap check.
def overlapsBool (left right : Condition) : Bool :=
  possibleTypesOverlapBool left.possibleTypes right.possibleTypes
    && BooleanLiteral.compatibleBool left.booleanLiterals right.booleanLiterals

-- Spec-inspired condition inclusion check.
def subsetBool (left right : Condition) : Bool :=
  possibleTypesSubsetBool left.possibleTypes right.possibleTypes
    && BooleanLiteral.entailsAllBool left.booleanLiterals right.booleanLiterals

theorem namesSubsetBool_self (names : List Name) :
    namesSubsetBool names names = true := by
  simp [namesSubsetBool]

theorem namesEqBool_self (names : List Name) :
    namesEqBool names names = true := by
  induction names with
  | nil =>
      simp [namesEqBool]
  | cons name rest ih =>
      simp [namesEqBool, ih]

theorem namesOptionEqBool_self (possibleTypes : Option (List Name)) :
    namesOptionEqBool possibleTypes possibleTypes = true := by
  cases possibleTypes with
  | none =>
      rfl
  | some names =>
      simp [namesOptionEqBool, namesEqBool_self]

theorem possibleTypesSubsetBool_self (possibleTypes : Option (List Name)) :
    possibleTypesSubsetBool possibleTypes possibleTypes = true := by
  cases possibleTypes with
  | none =>
      rfl
  | some names =>
      simp [possibleTypesSubsetBool, namesSubsetBool_self]

theorem subsetBool_self (condition : Condition) :
    subsetBool condition condition = true := by
  cases condition with
  | mk possibleTypes booleanLiterals =>
      simp [subsetBool, possibleTypesSubsetBool_self,
        BooleanLiteral.entailsAllBool_self]

theorem eqBool_self (condition : Condition) :
    eqBool condition condition = true := by
  cases condition with
  | mk possibleTypes booleanLiterals =>
      simp [eqBool, namesOptionEqBool_self, BooleanLiteral.listEqBool_self]

-- Spec-inspired condition intersection; returns none when the conjunction is
-- unsatisfiable.
def intersect? (left right : Condition) : Option Condition :=
  let combined := left.and right
  if combined.satisfiableBool then some combined else none

-- Spec 3.13.1 `@skip` and 3.13.2 `@include`: partial; converts modeled built-ins into
-- static/variable Boolean conditions and rejects unsupported argument forms.
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

-- Spec 5.3.2 same-response-name field comparison: partial field identity containing name
-- and raw arguments, without argument coercion or order-insensitive normalization.
structure SelectedField where
  fieldName : Name
  arguments : List Argument
deriving Repr

namespace SelectedField

-- Spec 2.10 input value equality as used by 5.3.2 field argument equality: partial; raw
-- structural equality, so object-field/argument order is significant here.
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

-- Spec 5.3.2 argument equality over the raw ordered argument representation used by
-- response-shape headers.
def argumentsEqBool : List Argument -> List Argument -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      argumentEqBool left right && argumentsEqBool leftRest rightRest
  | _, _ => false

-- Spec 5.3.2 selected-field equality for response-shape variant headers.
def eqBool (left right : SelectedField) : Bool :=
  (left.fieldName == right.fieldName)
    && argumentsEqBool left.arguments right.arguments

mutual
  -- Non-spec structural metric used to prove self-equality for selected-field arguments.
  def inputValueSize : InputValue -> Nat
    | .list values => inputValuesSize values + 1
    | .object fields => inputFieldsSize fields + 1
    | _ => 1

  def inputValuesSize : List InputValue -> Nat
    | [] => 0
    | value :: rest => inputValueSize value + inputValuesSize rest + 1

  def inputFieldsSize : List (Name × InputValue) -> Nat
    | [] => 0
    | (_name, value) :: rest => inputValueSize value + inputFieldsSize rest + 1
end

set_option linter.unusedSimpArgs false in
mutual
  theorem inputValueEqBool_self (value : InputValue) :
      inputValueEqBool value value = true := by
    cases value with
    | null =>
        simp [inputValueEqBool]
    | int value =>
        simp [inputValueEqBool]
    | float value =>
        simp [inputValueEqBool]
    | string value =>
        simp [inputValueEqBool]
    | boolean value =>
        cases value <;> simp [inputValueEqBool]
    | enum value =>
        simp [inputValueEqBool]
    | list values =>
        simp [inputValueEqBool, inputValuesEqBool_self values]
    | object fields =>
        simp [inputValueEqBool, inputFieldsEqBool_self fields]
    | «variable» name =>
        simp [inputValueEqBool]
  termination_by inputValueSize value
  decreasing_by
    simp_wf
    all_goals simp [inputValueSize, inputValuesSize, inputFieldsSize]
    all_goals omega

  theorem inputValuesEqBool_self (values : List InputValue) :
      inputValuesEqBool values values = true := by
    cases values with
    | nil =>
        simp [inputValuesEqBool]
    | cons value rest =>
        simp [inputValuesEqBool, inputValueEqBool_self value,
          inputValuesEqBool_self rest]
  termination_by inputValuesSize values
  decreasing_by
    simp_wf
    all_goals simp [inputValueSize, inputValuesSize, inputFieldsSize]
    all_goals omega

  theorem inputFieldsEqBool_self (fields : List (Name × InputValue)) :
      inputFieldsEqBool fields fields = true := by
    cases fields with
    | nil =>
        simp [inputFieldsEqBool]
    | cons field rest =>
        cases field with
        | mk name value =>
            simp [inputFieldsEqBool, inputValueEqBool_self value,
              inputFieldsEqBool_self rest]
  termination_by inputFieldsSize fields
  decreasing_by
    simp_wf
    all_goals simp [inputValueSize, inputValuesSize, inputFieldsSize]
    all_goals omega
end

theorem argumentEqBool_self (argument : Argument) :
    argumentEqBool argument argument = true := by
  cases argument with
  | mk name value =>
      simp [argumentEqBool, inputValueEqBool_self value]

theorem argumentsEqBool_self (arguments : List Argument) :
    argumentsEqBool arguments arguments = true := by
  induction arguments with
  | nil =>
      simp [argumentsEqBool]
  | cons argument rest ih =>
      simp [argumentsEqBool, argumentEqBool_self argument, ih]

theorem eqBool_self (field : SelectedField) :
    eqBool field field = true := by
  cases field with
  | mk fieldName arguments =>
      simp [eqBool, argumentsEqBool_self]

end SelectedField

-- Spec 5.3.2 selected-field constructor for response-shape variants.
def selectedField (fieldName : Name) (arguments : List Argument) :
    SelectedField :=
  { fieldName := fieldName, arguments := arguments }

-- Spec-inspired variant header: response variant condition plus selected field; not a
-- GraphQL spec structure.
abbrev VariantHeader := Condition × SelectedField

namespace VariantHeader

-- Non-spec equality for response-shape variant headers.
def eqBool (left right : VariantHeader) : Bool :=
  Condition.eqBool left.fst right.fst
    && SelectedField.eqBool left.snd right.snd

theorem eqBool_self (header : VariantHeader) :
    eqBool header header = true := by
  cases header with
  | mk condition field =>
      simp [eqBool, Condition.eqBool_self, SelectedField.eqBool_self]

-- Spec-inspired overlap check for the condition part of two response-shape variants.
def conditionsOverlapBool (left right : VariantHeader) : Bool :=
  Condition.overlapsBool left.fst right.fst

-- Spec-inspired inclusion check for the condition part of two response-shape variants.
def conditionSubsetBool (left right : VariantHeader) : Bool :=
  Condition.subsetBool left.fst right.fst

-- Spec 5.3.2 selected-field equality lifted to response-shape variant headers.
def selectedFieldEqBool (left right : VariantHeader) : Bool :=
  SelectedField.eqBool left.snd right.snd

-- Spec-inspired response-shape compatibility: overlapping conditions must select the
-- same field.
def compatibleBool (left right : VariantHeader) : Bool :=
  !(conditionsOverlapBool left right) || selectedFieldEqBool left right

-- Spec-inspired shape inclusion: non-spec condition-aware inclusion requiring the
-- required condition to be covered by the available condition and the selected field to
-- match.
def includedByBool (required available : VariantHeader) : Bool :=
  conditionSubsetBool required available && selectedFieldEqBool required available

theorem includedByBool_self (header : VariantHeader) :
    includedByBool header header = true := by
  cases header with
  | mk condition selectedField =>
      simp [includedByBool, conditionSubsetBool, selectedFieldEqBool,
        Condition.subsetBool_self, SelectedField.eqBool_self]

-- Spec-inspired variant-header intersection used by shape merging.
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

-- Non-spec recursive response-shape variant type.
abbrev Variant := VariantHeader × Shape

-- Spec 7.1.5 empty `data` object analogue for a leaf/no-field shape: non-spec empty
-- shape.
def empty : Shape :=
  ⟨[]⟩

-- Spec 6.3.2 collected fields map lookup by response name: partial list-backed helper for
-- the response-shape abstraction.
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

-- Spec-inspired variant lookup for inclusion: an available variant may cover a required
-- variant with a stronger condition.
def lookupIncludingVariant (requiredHeader : VariantHeader) :
    List (VariantHeader × Shape) -> Option Shape
  | [] => none
  | (availableHeader, shape) :: rest =>
      if VariantHeader.includedByBool requiredHeader availableHeader then
        some shape
      else
        lookupIncludingVariant requiredHeader rest

-- Spec-inspired same-response-name compatibility for two response-shape variants.
def variantHeadersCompatibleBool (left right : Variant) : Bool :=
  VariantHeader.compatibleBool left.fst right.fst

-- Spec-inspired condition-overlap helper for response-shape variants.
def variantConditionsOverlapBool (left right : Variant) : Bool :=
  VariantHeader.conditionsOverlapBool left.fst right.fst

-- Spec 5.3.2 selected-field equality helper for response-shape variants.
def variantsSelectSameFieldBool (left right : Variant) : Bool :=
  VariantHeader.selectedFieldEqBool left.fst right.fst

-- Spec-inspired compatibility of one variant against a same-response-name variant list.
def variantCompatibleWithAllBool (variant : Variant) : List Variant -> Bool :=
  fun variants => variants.all (fun other => variantHeadersCompatibleBool variant other)

-- Spec-inspired pairwise compatibility for variants under one response name.
def variantsPairwiseCompatibleBool : List Variant -> Bool
  | [] => true
  | variant :: rest =>
      variantCompatibleWithAllBool variant rest
        && variantsPairwiseCompatibleBool rest

-- Spec-inspired compatibility check for all response-name variant groups.
def responseNameVariantsCompatibleBool :
    List (Name × List Variant) -> Bool
  | [] => true
  | (_responseName, variants) :: rest =>
      variantsPairwiseCompatibleBool variants
        && responseNameVariantsCompatibleBool rest

-- Non-spec uniqueness helper over response-shape field entries.
def responseNameNotInFieldsBool (responseName : Name) :
    List (Name × List Variant) -> Bool
  | [] => true
  | (availableName, _variants) :: rest =>
      !(availableName == responseName)
        && responseNameNotInFieldsBool responseName rest

-- Non-spec uniqueness check over response-shape field entries.
def responseNamesNodupBool :
    List (Name × List Variant) -> Bool
  | [] => true
  | (responseName, _variants) :: rest =>
      responseNameNotInFieldsBool responseName rest
        && responseNamesNodupBool rest

-- Spec-inspired well-formedness: non-spec uniqueness and compatibility predicate for this
-- module's response-name variant map.
def responseNameNotInFields (responseName : Name)
    (fields : List (Name × List Variant)) : Prop :=
  responseNameNotInFieldsBool responseName fields = true

-- Non-spec inductive form of response-shape response-name uniqueness.
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

-- Spec-inspired response-shape well-formedness: unique response names, compatible
-- variants under each response name, and recursively well-formed child shapes.
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
  -- Non-spec structural metric used to fuel recursive response-shape merging.
  def size : Shape -> Nat
    | ⟨fields⟩ => 1 + fieldsSize fields

  def fieldsSize : List (Name × List (VariantHeader × Shape)) -> Nat
    | [] => 0
    | (_responseName, variants) :: rest => variantsSize variants + fieldsSize rest

  def variantsSize : List (VariantHeader × Shape) -> Nat
    | [] => 0
    | (_header, shape) :: rest => shape.size + variantsSize rest
end

-- Spec-inspired response-shape merge: non-spec recursive merge by response name and
-- variant header.
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

-- Spec-inspired response-shape merge wrapper with a structural fuel budget.
def merge (left right : Shape) : Shape :=
  mergeWithFuel (left.size + right.size) left right

-- Spec-inspired merge over raw response-shape field lists.
def mergeFields (left right : List (Name × List (VariantHeader × Shape))) :
    List (Name × List (VariantHeader × Shape)) :=
  (merge ⟨left⟩ ⟨right⟩).fields

theorem mergeFields_singleton_empty_self (responseName : Name)
    (header : VariantHeader) :
    mergeFields [(responseName, [(header, empty)])]
      [(responseName, [(header, empty)])]
      = [(responseName, [(header, empty)])] := by
  simp [mergeFields, merge, size, fieldsSize, variantsSize, mergeWithFuel,
    mergeFieldsWithFuel, mergeVariantsWithFuel, VariantHeader.eqBool_self,
    empty]

-- Spec-inspired response-shape inclusion: non-spec recursive inclusion over response
-- names, variant conditions, selected fields, and child shapes.
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

-- Spec-inspired response-shape equivalence: non-spec bidirectional inclusion; weaker than
-- full GraphQL operation equivalence.
def equivalentBool (left right : Shape) : Bool :=
  includesBool left right && includesBool right left

theorem empty_equivalent : equivalent empty empty := by
  exact And.intro (empty_includes empty) (empty_includes empty)

theorem empty_equivalentBool : equivalentBool empty empty = true := by
  simp [equivalentBool, empty_includesBool]

theorem lookupIncludingVariant_self_cons (header : VariantHeader)
    (shape : Shape) (rest : List Variant) :
    lookupIncludingVariant header ((header, shape) :: rest) = some shape := by
  simp [lookupIncludingVariant, VariantHeader.includedByBool_self]

theorem lookupField_self_cons (responseName : Name)
    (variants : List Variant) (rest : List (Name × List Variant)) :
    lookupField responseName ((responseName, variants) :: rest) = some variants := by
  simp [lookupField]

theorem includesVariantsBool_singleton_empty_self (header : VariantHeader) :
    includesVariantsBool [(header, empty)] [(header, empty)] = true := by
  simp [includesVariantsBool, lookupIncludingVariant_self_cons, empty_includesBool]

theorem includesFieldsBool_singleton_empty_self (responseName : Name)
    (header : VariantHeader) :
    includesFieldsBool [(responseName, [(header, empty)])]
      [(responseName, [(header, empty)])] = true := by
  simp [includesFieldsBool, lookupField, includesVariantsBool_singleton_empty_self]

theorem includesBool_singleton_empty_self (responseName : Name)
    (header : VariantHeader) :
    includesBool ⟨[(responseName, [(header, empty)])]⟩
      ⟨[(responseName, [(header, empty)])]⟩ = true := by
  simp [includesBool, includesFieldsBool_singleton_empty_self]

theorem equivalentBool_singleton_empty_self (responseName : Name)
    (header : VariantHeader) :
    equivalentBool ⟨[(responseName, [(header, empty)])]⟩
      ⟨[(responseName, [(header, empty)])]⟩ = true := by
  simp [equivalentBool, includesBool_singleton_empty_self]

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

-- Spec 5.5.2.3 `GetPossibleTypes`: restricts a shape condition to an inline fragment's
-- type condition.
def restrictConditionToType (schema : Schema) (condition : Condition)
    (typeCondition : Name) : Condition :=
  let allowedTypes := schema.getPossibleTypes typeCondition
  let possibleTypes :=
    match condition.possibleTypes with
    | none => allowedTypes
    | some currentTypes => currentTypes.filter (fun name => allowedTypes.contains name)
  condition.withPossibleTypes possibleTypes

-- Spec 6.3.2 `CollectFields`, 5.5.2.3 `GetPossibleTypes`, and 3.13 built-in directive
-- conditions: partial response-shape collection over semantic selections.
mutual
  def collectSelectionShapeFields (schema : Schema) :
      Nat -> Name -> Condition -> Semantic.Selection ->
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
                    ⟨collectSelectionSetShapeFields schema fuel
                      childType
                      (Condition.forChildType schema fieldCondition childType)
                      selectionSet⟩
              [(responseName, [((fieldCondition, selectedField fieldName arguments), childShape)])]
            else
              []
    | fuel + 1, parentType, condition, .inlineFragment none directives selectionSet =>
        match Condition.fromDirectives? directives with
        | none => []
        | some directiveCondition =>
            collectSelectionSetShapeFields schema fuel parentType
              (condition.and directiveCondition) selectionSet
    | fuel + 1, _parentType, condition,
        .inlineFragment (some typeCondition) directives selectionSet =>
        match Condition.fromDirectives? directives with
        | none => []
        | some directiveCondition =>
            let nextCondition :=
              restrictConditionToType schema (condition.and directiveCondition)
                typeCondition
            collectSelectionSetShapeFields schema fuel
              typeCondition nextCondition selectionSet

  def collectSelectionSetShapeFields (schema : Schema) :
      Nat -> Name -> Condition -> List Semantic.Selection ->
        List (Name × List (VariantHeader × Shape))
    | 0, _parentType, _condition, _selectionSet => []
    | _fuel + 1, _parentType, _condition, [] => []
    | fuel + 1, parentType, condition, selection :: rest =>
        if condition.satisfiableBool then
          mergeFields
            (collectSelectionShapeFields schema (fuel + 1) parentType condition selection)
            (collectSelectionSetShapeFields schema (fuel + 1) parentType condition rest)
        else
          []
end

-- Spec-inspired response-shape collection wrapper for a semantic selection set.
def semanticSelectionSetShape (schema : Schema) (fuel : Nat)
    (parentType : Name) (condition : Condition)
    (selectionSet : List Semantic.Selection) :
    List (Name × List (VariantHeader × Shape)) :=
  collectSelectionSetShapeFields schema fuel parentType condition selectionSet

-- Non-spec structural fuel bound for semantic response-shape collection.
def semanticOperationShapeFuel (operation : Semantic.Operation) : Nat :=
  operation.size + 1

-- Spec 5.5.2.3 `GetPossibleTypes`: root shape condition starts at the operation root's
-- possible runtime object types.
def semanticOperationInitialCondition (schema : Schema)
    (operation : Semantic.Operation) : Condition :=
  { possibleTypes := some (schema.getPossibleTypes operation.rootType),
    booleanLiterals := [] }

-- Spec-inspired operation response summary: non-spec abstraction of the semantic
-- operation's possible response-name shape.
def ofSemanticOperation (schema : Schema) (operation : Semantic.Operation) : Shape :=
  ⟨semanticSelectionSetShape schema
    (semanticOperationShapeFuel operation) operation.rootType
    (semanticOperationInitialCondition schema operation) operation.selectionSet⟩

-- Spec-inspired operation response summary after fragment inlining.
def ofOperation (schema : Schema) (operation : GraphQL.Operation) : Shape :=
  ofSemanticOperation schema (Semantic.fromOperation operation)

end Shape

end ResponseShape

end GraphQL
