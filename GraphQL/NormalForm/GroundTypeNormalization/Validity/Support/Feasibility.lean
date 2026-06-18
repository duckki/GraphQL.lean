import GraphQL.NormalForm.GroundTypeNormalization.Validity.Support.FieldHeads

/-!
Type-condition feasibility facts for ground-type normalization validity.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectionsTypeConditionFeasible_tail
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {selection : Selection} {selectionSet : List Selection} :
    selectionsTypeConditionFeasible schema parentType typeConditions
      (selection :: selectionSet) ->
      selectionsTypeConditionFeasible schema parentType typeConditions
        selectionSet := by
  intro hfeasible
  simpa [selectionsTypeConditionFeasible] using hfeasible.2

theorem selectionsTypeConditionFeasible_append
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {left right : List Selection} :
    selectionsTypeConditionFeasible schema parentType typeConditions left ->
    selectionsTypeConditionFeasible schema parentType typeConditions right ->
      selectionsTypeConditionFeasible schema parentType typeConditions
        (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      have hhead :
          selectionTypeConditionFeasible schema parentType typeConditions
            selection := by
        simpa [selectionsTypeConditionFeasible] using hleft.1
      have htail :
          selectionsTypeConditionFeasible schema parentType typeConditions
            rest := by
        simpa [selectionsTypeConditionFeasible] using hleft.2
      simp [selectionsTypeConditionFeasible]
      exact ⟨hhead, ih htail⟩

mutual
  theorem selectionTypeConditionFeasible_of_subset
      (schema : Schema) {parentType : Name} {source target : List Name} :
      (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source) ->
      ∀ selection,
        selectionTypeConditionFeasible schema parentType source selection ->
          selectionTypeConditionFeasible schema parentType target selection
    | hsubset,
      .field _responseName fieldName _arguments _directives selectionSet,
      hfeasible => by
        cases selectionSet with
        | nil =>
            simp [selectionTypeConditionFeasible]
        | cons selection rest =>
            simp [selectionTypeConditionFeasible] at hfeasible ⊢
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [hlookup] at hfeasible
            | some fieldDefinition =>
                simp [hlookup] at hfeasible ⊢
                exact hfeasible
    | hsubset, .inlineFragment none _directives selectionSet,
      hfeasible => by
        simpa [selectionTypeConditionFeasible] using
          selectionsTypeConditionFeasible_of_subset schema hsubset
            selectionSet hfeasible
    | hsubset, .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible => by
        simpa [selectionTypeConditionFeasible] using
          selectionsTypeConditionFeasible_of_subset schema
            (fun candidate hcandidate =>
              List.mem_cons.mp hcandidate |>.elim
                (fun heq => by subst candidate; simp)
                (fun hmem => List.mem_cons_of_mem typeCondition
                  (hsubset candidate hmem)))
            selectionSet hfeasible

  theorem selectionsTypeConditionFeasible_of_subset
      (schema : Schema) {parentType : Name} {source target : List Name} :
      (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source) ->
      ∀ selectionSet,
        selectionsTypeConditionFeasible schema parentType source selectionSet ->
          selectionsTypeConditionFeasible schema parentType target
            selectionSet
    | _hsubset, [], _hfeasible => by
        simp [selectionsTypeConditionFeasible]
    | hsubset, selection :: rest, hfeasible => by
        have hhead :
            selectionTypeConditionFeasible schema parentType source
              selection := by
          simpa [selectionsTypeConditionFeasible] using hfeasible.1
        have htail :
            selectionsTypeConditionFeasible schema parentType source rest := by
          simpa [selectionsTypeConditionFeasible] using hfeasible.2
        simp [selectionsTypeConditionFeasible]
        exact ⟨
          selectionTypeConditionFeasible_of_subset schema hsubset selection
            hhead,
          selectionsTypeConditionFeasible_of_subset schema hsubset rest
            htail⟩
end

theorem selectionsTypeConditionFeasible_withoutFieldsWithResponseName
    (schema : Schema) (responseName parentType : Name)
    (typeConditions : List Name) :
    ∀ selectionSet,
      selectionsTypeConditionFeasible schema parentType typeConditions
        selectionSet ->
      selectionsTypeConditionFeasible schema parentType typeConditions
        (withoutFieldsWithResponseName schema responseName selectionSet)
  | [], _hfeasible => by
      simp [withoutFieldsWithResponseName, selectionsTypeConditionFeasible]
  | selection :: rest, hfeasible => by
      have hhead :
          selectionTypeConditionFeasible schema parentType typeConditions
            selection := by
        simpa [selectionsTypeConditionFeasible] using hfeasible.1
      have htail :
          selectionsTypeConditionFeasible schema parentType typeConditions
            rest := by
        simpa [selectionsTypeConditionFeasible] using hfeasible.2
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hresponse : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, hresponse]
            exact selectionsTypeConditionFeasible_withoutFieldsWithResponseName
              schema responseName parentType typeConditions rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse,
              selectionsTypeConditionFeasible]
            exact ⟨hhead,
              selectionsTypeConditionFeasible_withoutFieldsWithResponseName
                schema responseName parentType typeConditions rest htail⟩
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              rw [withoutFieldsWithResponseName]
              simp [selectionsTypeConditionFeasible,
                selectionTypeConditionFeasible]
              exact ⟨
                selectionsTypeConditionFeasible_withoutFieldsWithResponseName
                  schema responseName parentType typeConditions selectionSet
                  hhead,
                selectionsTypeConditionFeasible_withoutFieldsWithResponseName
                  schema responseName parentType typeConditions rest htail⟩
          | some typeCondition =>
              rw [withoutFieldsWithResponseName]
              simp [selectionsTypeConditionFeasible,
                selectionTypeConditionFeasible]
              exact ⟨
                selectionsTypeConditionFeasible_withoutFieldsWithResponseName
                  schema responseName parentType
                  (typeCondition :: typeConditions) selectionSet hhead,
                selectionsTypeConditionFeasible_withoutFieldsWithResponseName
              schema responseName parentType typeConditions rest htail⟩

theorem possibleTypeNormalizations_ne_nil_of_branch_forValidity
    (schema : Schema) {possibleTypes : List Name}
    {selectionSet : List Selection} {objectType : Name} :
    objectType ∈ possibleTypes ->
      normalizeSelectionSet schema objectType selectionSet ≠ [] ->
        possibleTypeNormalizations schema possibleTypes selectionSet ≠ [] := by
  intro hmem hnonempty
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst head
        cases hnormalized :
            normalizeSelectionSet schema objectType selectionSet with
        | nil =>
            exact False.elim (hnonempty hnormalized)
        | cons selection selections =>
            simp [possibleTypeNormalizations, hnormalized]
      · have hrestNonempty :
            possibleTypeNormalizations schema rest selectionSet ≠ [] :=
          ih hrest
        cases hnormalized :
            normalizeSelectionSet schema head selectionSet with
        | nil =>
            simpa [possibleTypeNormalizations, hnormalized] using
              hrestNonempty
        | cons selection selections =>
            simp [possibleTypeNormalizations, hnormalized]

theorem typeConditionStackFeasible_of_subset_forValidity
    {schema : Schema} {source target : List Name} :
    typeConditionStackFeasible schema source ->
    (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source) ->
      typeConditionStackFeasible schema target := by
  intro hfeasible hsubset
  rcases hfeasible with ⟨objectType, hobjectType⟩
  exact ⟨objectType, fun typeCondition hmem =>
    hobjectType typeCondition (hsubset typeCondition hmem)⟩

mutual
  theorem selectionContainsTypeConditionFeasibleField_of_subset_forValidity
      (schema : Schema) {source target : List Name} :
      (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source) ->
      ∀ selection,
        selectionContainsTypeConditionFeasibleField schema source selection ->
          selectionContainsTypeConditionFeasibleField schema target selection
    | hsubset,
      .field _responseName _fieldName _arguments _directives _selectionSet,
      hfeasible => by
        exact typeConditionStackFeasible_of_subset_forValidity hfeasible
          hsubset
    | hsubset,
      .inlineFragment none _directives selectionSet, hfeasible => by
        exact selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
          schema hsubset selectionSet hfeasible
    | hsubset,
      .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible => by
        exact selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
          schema
          (fun candidate hcandidate =>
            List.mem_cons.mp hcandidate |>.elim
              (fun heq => by subst candidate; simp)
              (fun hmem => List.mem_cons_of_mem typeCondition
                (hsubset candidate hmem)))
          selectionSet hfeasible

  theorem selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
      (schema : Schema) {source target : List Name} :
      (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source) ->
      ∀ selectionSet,
        selectionSetContainsTypeConditionFeasibleField schema source
          selectionSet ->
          selectionSetContainsTypeConditionFeasibleField schema target
            selectionSet
    | _hsubset, [], hfeasible => by
        cases hfeasible
    | hsubset, selection :: rest, hfeasible => by
        rcases hfeasible with hhead | htail
        · exact Or.inl
            (selectionContainsTypeConditionFeasibleField_of_subset_forValidity
              schema hsubset selection hhead)
        · exact Or.inr
            (selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
              schema hsubset rest htail)
end

theorem selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
    (schema : Schema) (typeConditions : List Name)
    {left right : List Selection} :
    selectionSetContainsTypeConditionFeasibleField schema typeConditions left ->
      selectionSetContainsTypeConditionFeasibleField schema typeConditions
        (left ++ right) := by
  intro hleft
  induction left with
  | nil =>
      cases hleft
  | cons selection rest ih =>
      rcases hleft with hhead | htail
      · simp [selectionSetContainsTypeConditionFeasibleField, hhead]
      · simp [selectionSetContainsTypeConditionFeasibleField, ih htail]

theorem selectionSetContainsTypeConditionFeasibleField_append_right_forValidity
    (schema : Schema) (typeConditions : List Name)
    (left : List Selection) {right : List Selection} :
    selectionSetContainsTypeConditionFeasibleField schema typeConditions right ->
      selectionSetContainsTypeConditionFeasibleField schema typeConditions
        (left ++ right) := by
  intro hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      exact Or.inr ih

mutual
  theorem typeConditionStackFeasible_of_selectionContains_forValidity
      (schema : Schema) (typeConditions : List Name) :
      ∀ selection,
        selectionContainsTypeConditionFeasibleField schema typeConditions
          selection ->
          typeConditionStackFeasible schema typeConditions
    | .field _responseName _fieldName _arguments _directives _selectionSet,
      hfeasible => hfeasible
    | .inlineFragment none _directives selectionSet, hfeasible =>
        typeConditionStackFeasible_of_selectionSetContains_forValidity schema
          typeConditions selectionSet hfeasible
    | .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible =>
        typeConditionStackFeasible_of_subset_forValidity
          (typeConditionStackFeasible_of_selectionSetContains_forValidity
            schema (typeCondition :: typeConditions) selectionSet
            hfeasible)
          (fun _candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)

  theorem typeConditionStackFeasible_of_selectionSetContains_forValidity
      (schema : Schema) (typeConditions : List Name) :
      ∀ selectionSet,
        selectionSetContainsTypeConditionFeasibleField schema typeConditions
          selectionSet ->
          typeConditionStackFeasible schema typeConditions
    | [], hfeasible => by
        cases hfeasible
    | selection :: rest, hfeasible => by
        rcases hfeasible with hhead | htail
        · exact typeConditionStackFeasible_of_selectionContains_forValidity
            schema typeConditions selection hhead
        · exact typeConditionStackFeasible_of_selectionSetContains_forValidity
            schema typeConditions rest htail
end

theorem typesOverlapBool_eq_true_of_object_stack_feasible_forValidity
    (schema : Schema) {parentType typeCondition : Name}
    {typeConditions : List Name} :
    schema.objectType parentType ->
    typeConditionStackFeasible schema
      (typeCondition :: parentType :: typeConditions) ->
      schema.typesOverlapBool parentType typeCondition = true := by
  intro hobject hfeasible
  rcases hfeasible with ⟨objectType, hobjectType⟩
  have hparentMem :
      objectType ∈ schema.getPossibleTypes parentType :=
    hobjectType parentType (by simp)
  have hobjectEq : objectType = parentType :=
    object_typeIncludesObjectBool_eq_self schema hobject
      (List.contains_iff_mem.mpr hparentMem)
  subst objectType
  exact typesOverlapBool_eq_true_of_typesOverlap schema
    ⟨parentType, object_typeIncludesObject_self schema hobject,
      hobjectType typeCondition (by simp)⟩

theorem normalizeSelectionSet_ne_nil_of_feasible_forValidity
    (schema : Schema) :
    ∀ parentType selectionSet,
      schema.objectType parentType ->
      selectionSetSemanticsReady schema parentType selectionSet ->
      selectionSetContainsTypeConditionFeasibleField schema [parentType]
        selectionSet ->
        normalizeSelectionSet schema parentType selectionSet ≠ [] := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _hobject _hready hfeasible
      cases hfeasible
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro _hobject hready _hfeasible
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hheadReady' :
          ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
              ∧ ∀ runtimeType,
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType runtimeType = true ->
                  selectionSetSemanticsReady schema runtimeType
                    subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      rcases hheadReady' with ⟨fieldDefinition, hlookupSome, _hchild⟩
      rw [hlookup] at hlookupSome
      cases hlookupSome
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro _hobject _hready _hfeasible
      intro hnil
      simp [normalizeSelectionSet, hlookup, normalizedField] at hnil
  | case4 parentType rest directives subselections happend =>
      intro hobject hready hfeasible
      rcases hfeasible with hbody | hrestFeasible
      · have hbodyFeasible :
            selectionSetContainsTypeConditionFeasibleField schema [parentType]
              (subselections ++ rest) :=
          selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
            schema [parentType]
            (selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
              schema (fun typeCondition hmem => hmem) subselections hbody)
        have hbodyReady :
            selectionSemanticsReady schema parentType
              (Selection.inlineFragment none directives subselections) := by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
        have htailReady := selectionSetSemanticsReady_tail hready
        have happReady :
            selectionSetSemanticsReady schema parentType
              (subselections ++ rest) :=
          selectionSetSemanticsReady_append
            (by simpa [selectionSemanticsReady] using hbodyReady)
            htailReady
        simpa [normalizeSelectionSet] using
          happend hobject happReady hbodyFeasible
      · have hrestFeasible' :
            selectionSetContainsTypeConditionFeasibleField schema [parentType]
              (subselections ++ rest) :=
          selectionSetContainsTypeConditionFeasibleField_append_right_forValidity
            schema [parentType] subselections hrestFeasible
        have hbodyReady :
            selectionSemanticsReady schema parentType
              (Selection.inlineFragment none directives subselections) := by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
        have htailReady := selectionSetSemanticsReady_tail hready
        have happReady :
            selectionSetSemanticsReady schema parentType
              (subselections ++ rest) :=
          selectionSetSemanticsReady_append
            (by simpa [selectionSemanticsReady] using hbodyReady)
            htailReady
        simpa [normalizeSelectionSet] using
          happend hobject happReady hrestFeasible'
  | case5 parentType rest typeCondition directives subselections hoverlap
      hrest happend =>
      intro hobject hready hfeasible
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have htailReady := selectionSetSemanticsReady_tail hready
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have happReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      rcases hfeasible with hbody | hrestFeasible
      · have hbodyFeasible :
            selectionSetContainsTypeConditionFeasibleField schema [parentType]
              subselections :=
          selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
            schema
            (fun candidate hcandidate =>
              List.mem_cons_of_mem typeCondition hcandidate)
            subselections hbody
        have happFeasible :
            selectionSetContainsTypeConditionFeasibleField schema [parentType]
              (subselections ++ rest) :=
          selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
            schema [parentType] hbodyFeasible
        simpa [normalizeSelectionSet, hoverlap] using
          happend hobject happReady happFeasible
      · have happFeasible :
            selectionSetContainsTypeConditionFeasibleField schema [parentType]
              (subselections ++ rest) :=
          selectionSetContainsTypeConditionFeasibleField_append_right_forValidity
            schema [parentType] subselections hrestFeasible
        simpa [normalizeSelectionSet, hoverlap] using
          happend hobject happReady happFeasible
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro hobject hready hfeasible
      rcases hfeasible with hbody | hrestFeasible
      · have hbodyOverlap :
            schema.typesOverlapBool parentType typeCondition = true :=
          typesOverlapBool_eq_true_of_object_stack_feasible_forValidity
            schema hobject
            (typeConditionStackFeasible_of_selectionSetContains_forValidity
              schema (typeCondition :: [parentType]) subselections hbody)
        cases hoverlap hbodyOverlap
      · have htailReady := selectionSetSemanticsReady_tail hready
        have hfalse :
            schema.typesOverlapBool parentType typeCondition = false := by
          cases hmatch : schema.typesOverlapBool parentType typeCondition
          · rfl
          · contradiction
        simpa [normalizeSelectionSet, hfalse] using
          hrest hobject htailReady hrestFeasible



end GroundTypeNormalization

end NormalForm

end GraphQL
