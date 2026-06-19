import GraphQL.DataModel

/-!
Proof-facing facts about data-model field access equality.
-/
namespace GraphQL

namespace DataModel

namespace FieldAccess

mutual
  theorem structuralInputValueEqBool_symm :
      ∀ left right,
        structuralInputValueEqBool left right = true ->
          structuralInputValueEqBool right left = true
    | left, right, h => by
        cases left <;> cases right <;>
          simp [structuralInputValueEqBool] at h ⊢
        all_goals
          first
          | exact h.symm
          | exact structuralInputValuesEqBool_symm _ _ h
          | exact structuralInputFieldsEqBool_symm _ _ h

  theorem structuralInputValuesEqBool_symm :
      ∀ left right,
        structuralInputValuesEqBool left right = true ->
          structuralInputValuesEqBool right left = true
    | [], [], _h => by
        simp [structuralInputValuesEqBool]
    | left :: leftRest, right :: rightRest, h => by
        simp [structuralInputValuesEqBool] at h ⊢
        exact ⟨structuralInputValueEqBool_symm left right h.1,
          structuralInputValuesEqBool_symm leftRest rightRest h.2⟩
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [structuralInputValuesEqBool] at h

  theorem structuralInputFieldsEqBool_symm :
      ∀ left right,
        structuralInputFieldsEqBool left right = true ->
          structuralInputFieldsEqBool right left = true
    | [], [], _h => by
        simp [structuralInputFieldsEqBool]
    | (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, h => by
        simp [structuralInputFieldsEqBool] at h ⊢
        exact ⟨⟨h.1.1.symm,
          structuralInputValueEqBool_symm leftValue rightValue h.1.2⟩,
          structuralInputFieldsEqBool_symm leftRest rightRest h.2⟩
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [structuralInputFieldsEqBool] at h
end

mutual
  theorem structuralInputValueEqBool_refl :
      ∀ value, structuralInputValueEqBool value value = true
    | .null => by
        simp [structuralInputValueEqBool]
    | .int _value => by
        simp [structuralInputValueEqBool]
    | .float _value => by
        simp [structuralInputValueEqBool]
    | .string _value => by
        simp [structuralInputValueEqBool]
    | .boolean _value => by
        simp [structuralInputValueEqBool]
    | .enum _value => by
        simp [structuralInputValueEqBool]
    | .variable _value => by
        simp [structuralInputValueEqBool]
    | .list values => by
        simp [structuralInputValueEqBool,
          structuralInputValuesEqBool_refl values]
    | .object fields => by
        simp [structuralInputValueEqBool,
          structuralInputFieldsEqBool_refl fields]

  theorem structuralInputValuesEqBool_refl :
      ∀ values, structuralInputValuesEqBool values values = true
    | [] => by
        simp [structuralInputValuesEqBool]
    | value :: rest => by
        simp [structuralInputValuesEqBool,
          structuralInputValueEqBool_refl value,
          structuralInputValuesEqBool_refl rest]

  theorem structuralInputFieldsEqBool_refl :
      ∀ fields, structuralInputFieldsEqBool fields fields = true
    | [] => by
        simp [structuralInputFieldsEqBool]
    | (name, value) :: rest => by
        simp [structuralInputFieldsEqBool,
          structuralInputValueEqBool_refl value,
          structuralInputFieldsEqBool_refl rest]
end

mutual
  theorem structuralInputValueEqBool_eq :
      ∀ left right,
        structuralInputValueEqBool left right = true ->
          left = right
    | left, right, h => by
        cases left <;> cases right <;>
          simp [structuralInputValueEqBool] at h
        all_goals
          first
          | rfl
          | subst_vars; rfl
          | exact congrArg InputValue.list
              (structuralInputValuesEqBool_eq _ _ h)
          | exact congrArg InputValue.object
              (structuralInputFieldsEqBool_eq _ _ h)

  theorem structuralInputValuesEqBool_eq :
      ∀ left right,
        structuralInputValuesEqBool left right = true ->
          left = right
    | [], [], _h => by
        rfl
    | left :: leftRest, right :: rightRest, h => by
        simp [structuralInputValuesEqBool] at h
        have hhead := structuralInputValueEqBool_eq left right h.1
        have htail := structuralInputValuesEqBool_eq leftRest rightRest h.2
        subst right
        subst rightRest
        rfl
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [structuralInputValuesEqBool] at h

  theorem structuralInputFieldsEqBool_eq :
      ∀ left right,
        structuralInputFieldsEqBool left right = true ->
          left = right
    | [], [], _h => by
        rfl
    | (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, h => by
        simp [structuralInputFieldsEqBool] at h
        have hname : leftName = rightName := h.1.1
        have hvalue := structuralInputValueEqBool_eq leftValue rightValue
          h.1.2
        have htail := structuralInputFieldsEqBool_eq leftRest rightRest h.2
        subst rightName
        subst rightValue
        subst rightRest
        rfl
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [structuralInputFieldsEqBool] at h
end

theorem structuralInputValueEqBool_trans
    {left middle right : InputValue} :
    structuralInputValueEqBool left middle = true ->
    structuralInputValueEqBool middle right = true ->
      structuralInputValueEqBool left right = true := by
  intro hleft hright
  have hleftEq := structuralInputValueEqBool_eq left middle hleft
  have hrightEq := structuralInputValueEqBool_eq middle right hright
  subst middle
  subst right
  exact structuralInputValueEqBool_refl left

mutual
  theorem structuralInputValueEqBool_of_structuralEquivalent :
      ∀ {left right : InputValue},
        InputValue.structuralEquivalent left right ->
          structuralInputValueEqBool left right = true
    | .null, .null, _h => by
        simp [structuralInputValueEqBool]
    | .int left, .int right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [structuralInputValueEqBool, h]
    | .float left, .float right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [structuralInputValueEqBool, h]
    | .string left, .string right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [structuralInputValueEqBool, h]
    | .boolean left, .boolean right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [structuralInputValueEqBool, h]
    | .enum left, .enum right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [structuralInputValueEqBool, h]
    | .variable left, .variable right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [structuralInputValueEqBool, h]
    | .list left, .list right, h => by
        exact structuralInputValuesEqBool_of_structuralValuesEquivalent h
    | .object left, .object right, h => by
        exact structuralInputFieldsEqBool_of_structuralObjectFieldsEquivalent h
    | .null, .int _, h
    | .null, .float _, h
    | .null, .string _, h
    | .null, .boolean _, h
    | .null, .enum _, h
    | .null, .variable _, h
    | .null, .list _, h
    | .null, .object _, h
    | .int _, .null, h
    | .int _, .float _, h
    | .int _, .string _, h
    | .int _, .boolean _, h
    | .int _, .enum _, h
    | .int _, .variable _, h
    | .int _, .list _, h
    | .int _, .object _, h
    | .float _, .null, h
    | .float _, .int _, h
    | .float _, .string _, h
    | .float _, .boolean _, h
    | .float _, .enum _, h
    | .float _, .variable _, h
    | .float _, .list _, h
    | .float _, .object _, h
    | .string _, .null, h
    | .string _, .int _, h
    | .string _, .float _, h
    | .string _, .boolean _, h
    | .string _, .enum _, h
    | .string _, .variable _, h
    | .string _, .list _, h
    | .string _, .object _, h
    | .boolean _, .null, h
    | .boolean _, .int _, h
    | .boolean _, .float _, h
    | .boolean _, .string _, h
    | .boolean _, .enum _, h
    | .boolean _, .variable _, h
    | .boolean _, .list _, h
    | .boolean _, .object _, h
    | .enum _, .null, h
    | .enum _, .int _, h
    | .enum _, .float _, h
    | .enum _, .string _, h
    | .enum _, .boolean _, h
    | .enum _, .variable _, h
    | .enum _, .list _, h
    | .enum _, .object _, h
    | .variable _, .null, h
    | .variable _, .int _, h
    | .variable _, .float _, h
    | .variable _, .string _, h
    | .variable _, .boolean _, h
    | .variable _, .enum _, h
    | .variable _, .list _, h
    | .variable _, .object _, h
    | .list _, .null, h
    | .list _, .int _, h
    | .list _, .float _, h
    | .list _, .string _, h
    | .list _, .boolean _, h
    | .list _, .enum _, h
    | .list _, .variable _, h
    | .list _, .object _, h
    | .object _, .null, h
    | .object _, .int _, h
    | .object _, .float _, h
    | .object _, .string _, h
    | .object _, .boolean _, h
    | .object _, .enum _, h
    | .object _, .variable _, h
    | .object _, .list _, h => by
        simp [InputValue.structuralEquivalent] at h

  theorem structuralInputValuesEqBool_of_structuralValuesEquivalent :
      ∀ {left right : List InputValue},
        InputValue.structuralValuesEquivalent left right ->
          structuralInputValuesEqBool left right = true
    | [], [], _h => by
        simp [structuralInputValuesEqBool]
    | left :: leftRest, right :: rightRest, h => by
        simp [InputValue.structuralValuesEquivalent] at h
        simp [structuralInputValuesEqBool,
          structuralInputValueEqBool_of_structuralEquivalent h.1,
          structuralInputValuesEqBool_of_structuralValuesEquivalent h.2]
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [InputValue.structuralValuesEquivalent] at h

  theorem structuralInputFieldsEqBool_of_structuralObjectFieldsEquivalent :
      ∀ {left right : List (Name × InputValue)},
        InputValue.structuralObjectFieldsEquivalent left right ->
          structuralInputFieldsEqBool left right = true
    | [], [], _h => by
        simp [structuralInputFieldsEqBool]
    | (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
        simp [structuralInputFieldsEqBool, h.1,
          structuralInputValueEqBool_of_structuralEquivalent h.2.1,
          structuralInputFieldsEqBool_of_structuralObjectFieldsEquivalent h.2.2]
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
end

theorem structuralInputFieldsEqBool_insertInputFieldSorted
    {leftField rightField : Name × InputValue} :
    leftField.1 = rightField.1 ->
      structuralInputValueEqBool leftField.2 rightField.2 = true ->
        ∀ {left right : List (Name × InputValue)},
          structuralInputFieldsEqBool left right = true ->
            structuralInputFieldsEqBool
              (insertInputFieldSorted leftField left)
              (insertInputFieldSorted rightField right) = true
  | hname, hvalue, [], [], _hordered => by
      cases leftField with
      | mk leftName leftValue =>
          cases rightField with
          | mk rightName rightValue =>
              simp at hname hvalue
              simp [insertInputFieldSorted, InputValue.insertObjectFieldSorted,
                structuralInputFieldsEqBool, hname, hvalue]
  | _hname, _hvalue, [], _ :: _, hordered => by
      simp [structuralInputFieldsEqBool] at hordered
  | _hname, _hvalue, _ :: _, [], hordered => by
      simp [structuralInputFieldsEqBool] at hordered
  | hname, hvalue, (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, hordered => by
      have horderedParts := hordered
      simp [structuralInputFieldsEqBool] at horderedParts
      by_cases hleftLe : leftField.1 <= leftName
      · have hrightLe : rightField.1 <= rightName := by
          simpa [hname, horderedParts.1.1] using hleftLe
        cases leftField with
        | mk insertedLeftName insertedLeftValue =>
            cases rightField with
            | mk insertedRightName insertedRightValue =>
                simp at hname hvalue
                simp [insertInputFieldSorted, InputValue.insertObjectFieldSorted,
                  hleftLe, hrightLe, structuralInputFieldsEqBool]
                exact ⟨⟨hname, hvalue⟩, horderedParts⟩
      · have hrightLe : ¬ rightField.1 <= rightName := by
          intro hrightLe
          exact hleftLe (by
            simpa [hname, horderedParts.1.1] using hrightLe)
        cases leftField with
        | mk insertedLeftName insertedLeftValue =>
            cases rightField with
            | mk insertedRightName insertedRightValue =>
                simp at hname hvalue
                simp [insertInputFieldSorted, InputValue.insertObjectFieldSorted,
                  hleftLe, hrightLe, structuralInputFieldsEqBool]
                exact ⟨horderedParts.1,
                  structuralInputFieldsEqBool_insertInputFieldSorted
                    hname hvalue horderedParts.2⟩

theorem structuralInputFieldsEqBool_sortInputFieldsByName :
    ∀ {left right : List (Name × InputValue)},
      structuralInputFieldsEqBool left right = true ->
        structuralInputFieldsEqBool (sortInputFieldsByName left)
          (sortInputFieldsByName right) = true
  | [], [], _hordered => by
      simp [sortInputFieldsByName, InputValue.sortObjectFieldsByName,
        structuralInputFieldsEqBool]
  | [], _ :: _, hordered => by
      simp [structuralInputFieldsEqBool] at hordered
  | _ :: _, [], hordered => by
      simp [structuralInputFieldsEqBool] at hordered
  | (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, hordered => by
      simp [structuralInputFieldsEqBool] at hordered
      simp [sortInputFieldsByName, InputValue.sortObjectFieldsByName]
      exact structuralInputFieldsEqBool_insertInputFieldSorted hordered.1.1
        hordered.1.2
        (structuralInputFieldsEqBool_sortInputFieldsByName hordered.2)

mutual
  theorem structuralInputValueEqBool_canonical_of_structuralEquivalent :
      ∀ {left right : InputValue},
        InputValue.structuralEquivalent left right ->
          structuralInputValueEqBool
            (canonicalInputValue left) (canonicalInputValue right) = true
    | .null, .null, _h => by
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool]
    | .int left, .int right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool, h]
    | .float left, .float right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool, h]
    | .string left, .string right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool, h]
    | .boolean left, .boolean right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool, h]
    | .enum left, .enum right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool, h]
    | .variable left, .variable right, h => by
        simp [InputValue.structuralEquivalent] at h
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool, h]
    | .list left, .list right, h => by
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool]
        exact structuralInputValuesEqBool_canonical_of_structuralValuesEquivalent h
    | .object left, .object right, h => by
        simp [canonicalInputValue, InputValue.canonical,
          structuralInputValueEqBool]
        exact structuralInputFieldsEqBool_sortInputFieldsByName
          (structuralInputFieldsEqBool_canonicalFields_of_structuralObjectFieldsEquivalent h)
    | .null, .int _, h
    | .null, .float _, h
    | .null, .string _, h
    | .null, .boolean _, h
    | .null, .enum _, h
    | .null, .variable _, h
    | .null, .list _, h
    | .null, .object _, h
    | .int _, .null, h
    | .int _, .float _, h
    | .int _, .string _, h
    | .int _, .boolean _, h
    | .int _, .enum _, h
    | .int _, .variable _, h
    | .int _, .list _, h
    | .int _, .object _, h
    | .float _, .null, h
    | .float _, .int _, h
    | .float _, .string _, h
    | .float _, .boolean _, h
    | .float _, .enum _, h
    | .float _, .variable _, h
    | .float _, .list _, h
    | .float _, .object _, h
    | .string _, .null, h
    | .string _, .int _, h
    | .string _, .float _, h
    | .string _, .boolean _, h
    | .string _, .enum _, h
    | .string _, .variable _, h
    | .string _, .list _, h
    | .string _, .object _, h
    | .boolean _, .null, h
    | .boolean _, .int _, h
    | .boolean _, .float _, h
    | .boolean _, .string _, h
    | .boolean _, .enum _, h
    | .boolean _, .variable _, h
    | .boolean _, .list _, h
    | .boolean _, .object _, h
    | .enum _, .null, h
    | .enum _, .int _, h
    | .enum _, .float _, h
    | .enum _, .string _, h
    | .enum _, .boolean _, h
    | .enum _, .variable _, h
    | .enum _, .list _, h
    | .enum _, .object _, h
    | .variable _, .null, h
    | .variable _, .int _, h
    | .variable _, .float _, h
    | .variable _, .string _, h
    | .variable _, .boolean _, h
    | .variable _, .enum _, h
    | .variable _, .list _, h
    | .variable _, .object _, h
    | .list _, .null, h
    | .list _, .int _, h
    | .list _, .float _, h
    | .list _, .string _, h
    | .list _, .boolean _, h
    | .list _, .enum _, h
    | .list _, .variable _, h
    | .list _, .object _, h
    | .object _, .null, h
    | .object _, .int _, h
    | .object _, .float _, h
    | .object _, .string _, h
    | .object _, .boolean _, h
    | .object _, .enum _, h
    | .object _, .variable _, h
    | .object _, .list _, h => by
        simp [InputValue.structuralEquivalent] at h

  theorem structuralInputValuesEqBool_canonical_of_structuralValuesEquivalent :
      ∀ {left right : List InputValue},
        InputValue.structuralValuesEquivalent left right ->
          structuralInputValuesEqBool
            (canonicalInputValues left) (canonicalInputValues right) = true
    | [], [], _h => by
        simp [canonicalInputValues, InputValue.canonicalValues,
          structuralInputValuesEqBool]
    | left :: leftRest, right :: rightRest, h => by
        simp [InputValue.structuralValuesEquivalent] at h
        simp [canonicalInputValues, InputValue.canonicalValues,
          structuralInputValuesEqBool]
        exact ⟨structuralInputValueEqBool_canonical_of_structuralEquivalent h.1,
          structuralInputValuesEqBool_canonical_of_structuralValuesEquivalent h.2⟩
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [InputValue.structuralValuesEquivalent] at h

  theorem structuralInputFieldsEqBool_canonicalFields_of_structuralObjectFieldsEquivalent :
      ∀ {left right : List (Name × InputValue)},
        InputValue.structuralObjectFieldsEquivalent left right ->
          structuralInputFieldsEqBool
            (canonicalInputFields left) (canonicalInputFields right) = true
    | [], [], _h => by
        simp [canonicalInputFields, InputValue.canonicalObjectFields,
          structuralInputFieldsEqBool]
    | (leftName, leftValue) :: leftRest,
      (rightName, rightValue) :: rightRest, h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
        simp [canonicalInputFields, InputValue.canonicalObjectFields,
          structuralInputFieldsEqBool, h.1]
        exact ⟨structuralInputValueEqBool_canonical_of_structuralEquivalent h.2.1,
          structuralInputFieldsEqBool_canonicalFields_of_structuralObjectFieldsEquivalent h.2.2⟩
    | [], _ :: _, h
    | _ :: _, [], h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
end

theorem argumentEqBool_refl (argument : Argument) :
    argumentEqBool argument argument = true := by
  simp [argumentEqBool, canonicalInputValue,
    structuralInputValueEqBool_refl]

theorem argumentEqBool_of_equivalent
    {left right : Argument} :
    left.equivalent right ->
      argumentEqBool left right = true := by
  intro h
  simp [Argument.equivalent, argumentEqBool, canonicalInputValue,
    InputValue.equivalent] at h ⊢
  exact ⟨h.1,
    structuralInputValueEqBool_of_structuralEquivalent h.2⟩

theorem argumentEqBool_canonicalArgument_of_equivalent
    {left right : Argument} :
    left.equivalent right ->
      argumentEqBool (canonicalArgument left) (canonicalArgument right) = true := by
  intro h
  simp [Argument.equivalent, argumentEqBool, canonicalArgument,
    canonicalInputValue, InputValue.equivalent] at h ⊢
  exact ⟨h.1,
    structuralInputValueEqBool_canonical_of_structuralEquivalent h.2⟩

theorem argumentEqBool_trans
    {left middle right : Argument} :
    argumentEqBool left middle = true ->
    argumentEqBool middle right = true ->
      argumentEqBool left right = true := by
  intro hleft hright
  simp [argumentEqBool, canonicalInputValue] at hleft hright ⊢
  exact ⟨hleft.1.trans hright.1,
    structuralInputValueEqBool_trans hleft.2 hright.2⟩

theorem argumentEqBool_symm
    {left right : Argument} :
    argumentEqBool left right = true ->
      argumentEqBool right left = true := by
  intro h
  simp [argumentEqBool, canonicalInputValue] at h ⊢
  exact ⟨h.1.symm, structuralInputValueEqBool_symm _ _ h.2⟩

theorem argumentsEqBoolOrdered_refl :
    ∀ arguments, argumentsEqBoolOrdered arguments arguments = true
  | [] => by
      simp [argumentsEqBoolOrdered]
  | argument :: rest => by
      simp [argumentsEqBoolOrdered, argumentEqBool_refl argument,
        argumentsEqBoolOrdered_refl rest]

theorem canonicalArguments_append :
    ∀ left right : List Argument,
      canonicalArguments (left ++ right) =
        canonicalArguments left ++ canonicalArguments right
  | [], right => by
      simp [canonicalArguments]
  | argument :: rest, right => by
      simp [canonicalArguments, canonicalArguments_append rest right]

theorem canonicalArguments_names :
    ∀ arguments : List Argument,
      (canonicalArguments arguments).map Argument.name =
        arguments.map Argument.name
  | [] => by
      simp [canonicalArguments]
  | argument :: rest => by
      simp [canonicalArguments, canonicalArgument, canonicalArguments_names rest]

theorem insertArgumentSorted_comm_of_name_ne
    (left right : Argument) :
    left.name ≠ right.name ->
      ∀ rest,
        insertArgumentSorted left (insertArgumentSorted right rest) =
          insertArgumentSorted right (insertArgumentSorted left rest)
  | hne, [] => by
      by_cases hleft : left.name <= right.name
      · have hrightFalse : ¬ right.name <= left.name := by
          intro hright
          exact hne (String.le_antisymm hleft hright)
        simp [insertArgumentSorted, hleft, hrightFalse]
      · have hright : right.name <= left.name := by
          exact Or.resolve_left (String.le_total left.name right.name) hleft
        simp [insertArgumentSorted, hleft, hright]
  | hne, head :: rest => by
      by_cases hrightHead : right.name <= head.name
      · by_cases hleftRight : left.name <= right.name
        · have hleftHead : left.name <= head.name :=
            String.le_trans hleftRight hrightHead
          have hrightLeftFalse : ¬ right.name <= left.name := by
            intro hrightLeft
            exact hne (String.le_antisymm hleftRight hrightLeft)
          simp [insertArgumentSorted, hrightHead, hleftRight, hleftHead,
            hrightLeftFalse]
        · have hrightLeft : right.name <= left.name := by
            exact Or.resolve_left (String.le_total left.name right.name)
              hleftRight
          by_cases hleftHead : left.name <= head.name
          · simp [insertArgumentSorted, hrightHead, hrightLeft, hleftHead]
            intro hle
            exact False.elim (hleftRight hle)
          · simp [insertArgumentSorted, hrightHead, hleftHead]
            intro hle
            exact False.elim (hleftRight hle)
      · by_cases hleftHead : left.name <= head.name
        · by_cases hrightLeft : right.name <= left.name
          · have hrightHead' : right.name <= head.name :=
              String.le_trans hrightLeft hleftHead
            exact False.elim (hrightHead hrightHead')
          · have hleftRight : left.name <= right.name := by
              exact Or.resolve_left (String.le_total right.name left.name)
                hrightLeft
            simp [insertArgumentSorted, hrightHead, hleftHead]
            intro hle
            exact False.elim (hrightLeft hle)
        · simp [insertArgumentSorted, hrightHead, hleftHead,
            insertArgumentSorted_comm_of_name_ne left right hne rest]

theorem sortArgumentsByName_middle_eq_insert_of_name_not_mem :
    ∀ (before suffix : List Argument) (argument : Argument),
      argument.name ∉ (before ++ suffix).map Argument.name ->
        sortArgumentsByName (before ++ argument :: suffix) =
          insertArgumentSorted argument (sortArgumentsByName (before ++ suffix))
  | [], suffix, argument, _hnot => by
      rfl
  | head :: before, suffix, argument, hnot => by
      have hnotParts : argument.name ≠ head.name
          ∧ argument.name ∉ (before ++ suffix).map Argument.name := by
        simpa [List.map_append] using hnot
      have hne : head.name ≠ argument.name := by
        intro h
        exact hnotParts.1 h.symm
      simp [sortArgumentsByName]
      rw [sortArgumentsByName_middle_eq_insert_of_name_not_mem
        before suffix argument hnotParts.2]
      exact insertArgumentSorted_comm_of_name_ne head argument hne
        (sortArgumentsByName (before ++ suffix))

theorem argumentsEqBoolOrdered_insertArgumentSorted
    {leftArgument rightArgument : Argument} :
    argumentEqBool leftArgument rightArgument = true ->
      ∀ {left right : List Argument},
        argumentsEqBoolOrdered left right = true ->
          argumentsEqBoolOrdered
            (insertArgumentSorted leftArgument left)
            (insertArgumentSorted rightArgument right) = true
  | hargument, [], [], _hordered => by
      simp [insertArgumentSorted, argumentsEqBoolOrdered, hargument]
  | _hargument, [], _ :: _, hordered => by
      simp [argumentsEqBoolOrdered] at hordered
  | _hargument, _ :: _, [], hordered => by
      simp [argumentsEqBoolOrdered] at hordered
  | hargument, leftHead :: leftRest, rightHead :: rightRest, hordered => by
      have hargumentParts := hargument
      have horderedParts := hordered
      simp [argumentEqBool] at hargumentParts
      simp [argumentsEqBoolOrdered] at horderedParts
      have hheadParts := horderedParts.1
      simp [argumentEqBool] at hheadParts
      by_cases hleftLe : leftArgument.name <= leftHead.name
      · have hrightLe : rightArgument.name <= rightHead.name := by
          simpa [hargumentParts.1, hheadParts.1] using hleftLe
        simpa [insertArgumentSorted, hleftLe, hrightLe,
          argumentsEqBoolOrdered, hargument] using horderedParts
      · have hrightLe : ¬ rightArgument.name <= rightHead.name := by
          intro hrightLe
          exact hleftLe (by
            simpa [hargumentParts.1, hheadParts.1] using hrightLe)
        simp [insertArgumentSorted, hleftLe, hrightLe,
          argumentsEqBoolOrdered, horderedParts.1,
          argumentsEqBoolOrdered_insertArgumentSorted hargument
            horderedParts.2]

theorem argumentsEqBoolOrdered_sortArgumentsByName :
    ∀ {left right : List Argument},
      argumentsEqBoolOrdered left right = true ->
        argumentsEqBoolOrdered (sortArgumentsByName left)
          (sortArgumentsByName right) = true
  | [], [], _hordered => by
      simp [sortArgumentsByName, argumentsEqBoolOrdered]
  | [], _ :: _, hordered => by
      simp [argumentsEqBoolOrdered] at hordered
  | _ :: _, [], hordered => by
      simp [argumentsEqBoolOrdered] at hordered
  | leftHead :: leftRest, rightHead :: rightRest, hordered => by
      simp [argumentsEqBoolOrdered] at hordered
      simp [sortArgumentsByName]
      exact argumentsEqBoolOrdered_insertArgumentSorted hordered.1
        (argumentsEqBoolOrdered_sortArgumentsByName hordered.2)

theorem argumentsEqBoolOrdered_trans :
    ∀ left middle right,
      argumentsEqBoolOrdered left middle = true ->
      argumentsEqBoolOrdered middle right = true ->
        argumentsEqBoolOrdered left right = true
  | [], [], [], _hleft, _hright => by
      simp [argumentsEqBoolOrdered]
  | leftHead :: leftRest, middleHead :: middleRest,
    rightHead :: rightRest, hleft, hright => by
      simp [argumentsEqBoolOrdered] at hleft hright ⊢
      exact ⟨argumentEqBool_trans hleft.1 hright.1,
        argumentsEqBoolOrdered_trans leftRest middleRest rightRest
          hleft.2 hright.2⟩
  | [], [], _ :: _, _hleft, hright => by
      simp [argumentsEqBoolOrdered] at hright
  | [], _ :: _, _, hleft, _hright => by
      simp [argumentsEqBoolOrdered] at hleft
  | _ :: _, [], _, hleft, _hright => by
      simp [argumentsEqBoolOrdered] at hleft
  | _ :: _, _ :: _, [], _hleft, hright => by
      simp [argumentsEqBoolOrdered] at hright

theorem argumentsEqBoolOrdered_symm :
    ∀ {left right},
      argumentsEqBoolOrdered left right = true ->
        argumentsEqBoolOrdered right left = true
  | [], [], _h => by
      simp [argumentsEqBoolOrdered]
  | leftHead :: leftRest, rightHead :: rightRest, h => by
      simp [argumentsEqBoolOrdered] at h ⊢
      exact ⟨argumentEqBool_symm h.1,
        argumentsEqBoolOrdered_symm h.2⟩
  | [], _ :: _, h
  | _ :: _, [], h => by
      simp [argumentsEqBoolOrdered] at h

theorem argumentsEqBool_refl (arguments : List Argument) :
    argumentsEqBool arguments arguments = true := by
  unfold argumentsEqBool
  exact argumentsEqBoolOrdered_refl _

theorem argumentsEqBool_trans
    {left middle right : List Argument} :
    argumentsEqBool left middle = true ->
    argumentsEqBool middle right = true ->
      argumentsEqBool left right = true := by
  intro hleft hright
  unfold argumentsEqBool at hleft hright ⊢
  exact argumentsEqBoolOrdered_trans _ _ _ hleft hright

theorem argumentsEqBool_symm
    {left right : List Argument} :
    argumentsEqBool left right = true ->
      argumentsEqBool right left = true := by
  intro h
  unfold argumentsEqBool at h ⊢
  exact argumentsEqBoolOrdered_symm h

theorem eqBool_refl (field : FieldAccess) :
    eqBool field field = true := by
  simp [eqBool, argumentsEqBool_refl]

theorem eqBool_trans
    {left middle right : FieldAccess} :
    eqBool left middle = true ->
    eqBool middle right = true ->
      eqBool left right = true := by
  intro hleft hright
  simp [eqBool] at hleft hright ⊢
  exact ⟨hleft.1.trans hright.1,
    argumentsEqBool_trans hleft.2 hright.2⟩

theorem eqBool_symm
    {left right : FieldAccess} :
    eqBool left right = true ->
      eqBool right left = true := by
  intro h
  simp [eqBool] at h ⊢
  exact ⟨h.1.symm, argumentsEqBool_symm h.2⟩

theorem eqBool_congr_right
    {candidate left right : FieldAccess} :
    eqBool left right = true ->
      eqBool candidate left = eqBool candidate right := by
  intro h
  cases hleft : eqBool candidate left <;>
    cases hright : eqBool candidate right <;> try rfl
  · have hcandidateLeft : eqBool candidate left = true :=
      eqBool_trans hright (eqBool_symm h)
    simp [hleft] at hcandidateLeft
  · have hcandidateRight : eqBool candidate right = true :=
      eqBool_trans hleft h
    simp [hright] at hcandidateRight

end FieldAccess

end DataModel

end GraphQL
