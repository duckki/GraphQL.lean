import GraphQL.NormalForm

/-!
Proof-facing lemmas for directive-free ground-type normalization.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectionSetDirectiveFree_nil :
    selectionSetDirectiveFree ([] : List Selection) := by
  simp [selectionSetDirectiveFree]

theorem selectionSetDirectiveFree_head
    {selection : Selection}
    {selectionSet : List Selection} :
    selectionSetDirectiveFree (selection :: selectionSet) ->
      selectionDirectiveFree selection := by
  intro hfree
  exact hfree.1

theorem selectionSetDirectiveFree_tail
    {selection : Selection}
    {selectionSet : List Selection} :
    selectionSetDirectiveFree (selection :: selectionSet) ->
      selectionSetDirectiveFree selectionSet := by
  intro hfree
  exact hfree.2

theorem selectionSetDirectiveFree_append
    {left right : List Selection} :
    selectionSetDirectiveFree left ->
      selectionSetDirectiveFree right ->
        selectionSetDirectiveFree (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      exact ⟨hleft.1, ih hleft.2⟩

theorem selectionDirectiveFree_subselections
    {selection : Selection} :
    selectionDirectiveFree selection ->
      selectionSetDirectiveFree selection.subselections := by
  intro hfree
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simpa [Selection.subselections, selectionDirectiveFree] using hfree.2
  | inlineFragment typeCondition directives selectionSet =>
      simpa [Selection.subselections, selectionDirectiveFree] using hfree.2

theorem selectionSetDirectiveFree_mergeSelectionSets
    {selections : List Selection} :
    selectionSetDirectiveFree selections ->
      selectionSetDirectiveFree (mergeSelectionSets selections) := by
  intro hselections
  induction selections with
  | nil =>
      exact selectionSetDirectiveFree_nil
  | cons selection rest ih =>
      simp [mergeSelectionSets]
      exact selectionSetDirectiveFree_append
        (selectionDirectiveFree_subselections
          (selectionSetDirectiveFree_head hselections))
        (ih (selectionSetDirectiveFree_tail hselections))

theorem withoutFieldsWithResponseName_directiveFree (schema : Schema)
    (responseName : Name) :
    ∀ selectionSet,
      selectionSetDirectiveFree selectionSet ->
        selectionSetDirectiveFree
          (withoutFieldsWithResponseName schema responseName selectionSet)
  | [], _hfree => by
      simpa [withoutFieldsWithResponseName] using selectionSetDirectiveFree_nil
  | selection :: rest, hfree => by
      have hselection := selectionSetDirectiveFree_head hfree
      have hrest := selectionSetDirectiveFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            exact withoutFieldsWithResponseName_directiveFree schema responseName
              rest hrest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse]
            exact ⟨hselection,
              withoutFieldsWithResponseName_directiveFree schema responseName
                rest hrest⟩
      | inlineFragment typeCondition directives selectionSet =>
          have hdirectives : directives = [] := hselection.1
          subst directives
          simp [withoutFieldsWithResponseName]
          exact ⟨
            ⟨rfl,
              withoutFieldsWithResponseName_directiveFree schema responseName
                selectionSet hselection.2⟩,
            withoutFieldsWithResponseName_directiveFree schema responseName
              rest hrest⟩

theorem validFieldsWithResponseName_directiveFree (schema : Schema)
    (parentType responseName : Name) :
    ∀ selectionSet,
      selectionSetDirectiveFree selectionSet ->
        selectionSetDirectiveFree
          (validFieldsWithResponseName schema parentType responseName selectionSet)
  | [], _hfree => by
      simpa [validFieldsWithResponseName] using selectionSetDirectiveFree_nil
  | selection :: rest, hfree => by
      have hselection := selectionSetDirectiveFree_head hfree
      have hrest := selectionSetDirectiveFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [validFieldsWithResponseName, hname]
            exact ⟨hselection,
              validFieldsWithResponseName_directiveFree schema parentType
                responseName rest hrest⟩
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [validFieldsWithResponseName, hfalse]
            exact validFieldsWithResponseName_directiveFree schema parentType
              responseName rest hrest
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [validFieldsWithResponseName]
              exact selectionSetDirectiveFree_append
                (validFieldsWithResponseName_directiveFree schema parentType
                  responseName selectionSet hselection.2)
                (validFieldsWithResponseName_directiveFree schema parentType
                  responseName rest hrest)
          | some typeCondition =>
              by_cases hoverlap :
                  (schema.typesOverlapBool parentType typeCondition) = true
              · simp [validFieldsWithResponseName, hoverlap]
                exact selectionSetDirectiveFree_append
                  (validFieldsWithResponseName_directiveFree schema parentType
                    responseName selectionSet hselection.2)
                  (validFieldsWithResponseName_directiveFree schema parentType
                    responseName rest hrest)
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [validFieldsWithResponseName, hfalse]
                exact validFieldsWithResponseName_directiveFree schema parentType
                  responseName rest hrest

theorem selectionSetDirectiveFree_possibleTypeNormalizations
    (schema : Schema)
    (possibleTypes : List Name) {selectionSet : List Selection} :
    (∀ objectType, objectType ∈ possibleTypes ->
      selectionSetDirectiveFree
        (normalizeSelectionSet schema objectType selectionSet)) ->
      selectionSetDirectiveFree
        (possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (normalizeSelectionSet schema objectType selectionSet))) := by
  intro hnormalize
  induction possibleTypes with
  | nil =>
      exact selectionSetDirectiveFree_nil
  | cons objectType rest ih =>
      exact ⟨
        ⟨rfl, hnormalize objectType (by simp)⟩,
        ih (fun candidate hcandidate =>
          hnormalize candidate (List.mem_cons_of_mem objectType hcandidate))⟩

theorem normalizeMergedSelectionSetForType_directiveFree
    (schema : Schema)
    (hnormalize :
      ∀ parentType selectionSet,
        selectionSetDirectiveFree selectionSet ->
          selectionSetDirectiveFree
            (normalizeSelectionSet schema parentType selectionSet))
    (returnType : Name) {selectionSet : List Selection} :
    selectionSetDirectiveFree selectionSet ->
      selectionSetDirectiveFree
        (normalizeMergedSelectionSetForType schema returnType selectionSet) := by
  intro hfree
  unfold normalizeMergedSelectionSetForType
  by_cases hobject : objectTypeNameBool schema returnType = true
  · simp [hobject]
    exact hnormalize returnType selectionSet hfree
  · have hfalse : objectTypeNameBool schema returnType = false := by
      cases hmatch : objectTypeNameBool schema returnType
      · rfl
      · contradiction
    simp [hfalse]
    exact selectionSetDirectiveFree_possibleTypeNormalizations schema
      (schema.getPossibleTypes returnType)
      (fun objectType _hobjectType =>
        hnormalize objectType selectionSet hfree)

theorem normalizeSelectionSet_directiveFree (schema : Schema) :
    ∀ parentType selectionSet,
      selectionSetDirectiveFree selectionSet ->
        selectionSetDirectiveFree
          (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
    intro hfree
    simpa [normalizeSelectionSet] using selectionSetDirectiveFree_nil
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
    intro hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have hfilteredRestFree :
        selectionSetDirectiveFree
          (withoutFieldsWithResponseName schema responseName rest) :=
      withoutFieldsWithResponseName_directiveFree schema responseName rest hrestFree
    simpa [normalizeSelectionSet, hlookup] using hrest hfilteredRestFree
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
    intro hfree
    have hselectionFree :=
      selectionSetDirectiveFree_head hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have hdirectives : directives = [] := hselectionFree.1
    subst directives
    have hsubselectionsFree : selectionSetDirectiveFree selectionSet :=
      hselectionFree.2
    have hfilteredRestFree :
        selectionSetDirectiveFree
          (withoutFieldsWithResponseName schema responseName rest) :=
      withoutFieldsWithResponseName_directiveFree schema responseName rest hrestFree
    have hnormalizedRest :
        selectionSetDirectiveFree
          (normalizeSelectionSet schema parentType
            (withoutFieldsWithResponseName schema responseName rest)) :=
      hrest hfilteredRestFree
    have hmatchingFree : selectionSetDirectiveFree matching := by
      subst matching
      exact validFieldsWithResponseName_directiveFree schema parentType
        responseName rest hrestFree
    have hmergedSubselectionsFree :
        selectionSetDirectiveFree mergedSubselections := by
      subst mergedSubselections
      exact selectionSetDirectiveFree_append hsubselectionsFree
        (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
    have hnormalizedSubselections :
        selectionSetDirectiveFree
          (if objectTypeNameBool schema returnType then
            normalizeSelectionSet schema returnType mergedSubselections
          else
            (schema.getPossibleTypes returnType).map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (normalizeSelectionSet schema objectType mergedSubselections))) := by
      by_cases hobject : objectTypeNameBool schema returnType = true
      · simp [hobject]
        exact hmerged hmergedSubselectionsFree
      · have hfalse : objectTypeNameBool schema returnType = false := by
          cases hmatch : objectTypeNameBool schema returnType
          · rfl
          · contradiction
        simp [hfalse]
        exact selectionSetDirectiveFree_possibleTypeNormalizations schema
          (schema.getPossibleTypes returnType)
          (fun objectType _hobjectType =>
            hpossible objectType hmergedSubselectionsFree)
    simpa [normalizeSelectionSet, hlookup, matching, mergedSubselections,
      returnType] using
      (show selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments []
          (if objectTypeNameBool schema returnType then
            normalizeSelectionSet schema returnType mergedSubselections
          else
            (schema.getPossibleTypes returnType).map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (normalizeSelectionSet schema objectType mergedSubselections)))
          :: normalizeSelectionSet schema parentType
            (withoutFieldsWithResponseName schema responseName rest)) from
        ⟨⟨rfl, hnormalizedSubselections⟩, hnormalizedRest⟩)
  | case4 parentType rest directives selectionSet happend =>
    intro hfree
    have hselectionFree :=
      selectionSetDirectiveFree_head hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have happendFree :
        selectionSetDirectiveFree (selectionSet ++ rest) :=
      selectionSetDirectiveFree_append hselectionFree.2 hrestFree
    simpa [normalizeSelectionSet] using happend happendFree
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
    intro hfree
    have hselectionFree :=
      selectionSetDirectiveFree_head hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have happendFree :
        selectionSetDirectiveFree (selectionSet ++ rest) :=
      selectionSetDirectiveFree_append hselectionFree.2 hrestFree
    simpa [normalizeSelectionSet, hoverlap] using happend happendFree
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
    intro hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
      cases hmatch : schema.typesOverlapBool parentType typeCondition
      · rfl
      · contradiction
    simpa [normalizeSelectionSet, hfalse] using hrest hrestFree

theorem normalizeMergedSelectionSetForType_directiveFree_self
    (schema : Schema) (returnType : Name) {selectionSet : List Selection} :
    selectionSetDirectiveFree selectionSet ->
      selectionSetDirectiveFree
        (normalizeMergedSelectionSetForType schema returnType selectionSet) := by
  exact normalizeMergedSelectionSetForType_directiveFree schema
    (normalizeSelectionSet_directiveFree schema) returnType

theorem normalizeOperation_directiveFree (schema : Schema)
    (operation : Operation) :
    operationDirectiveFree operation ->
      operationDirectiveFree (normalizeOperation schema operation) := by
  intro hfree
  exact normalizeSelectionSet_directiveFree schema operation.rootType
    operation.selectionSet hfree

theorem normalizeSelectionSet_allFields (schema : Schema) :
    ∀ parentType selectionSet,
      selectionsAllFields
        (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro selection hmem
      simp [normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro selection hmem
      simp [normalizeSelectionSet, hlookup] at hmem
      cases hmem with
      | inl hhead =>
          subst selection
          simp [Selection.isField]
      | inr htail =>
          exact hrest selection htail
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest

theorem possibleTypeNormalizations_allInlineFragments
    (schema : Schema)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    selectionsAllInlineFragments
      (possibleTypes.map
        (fun objectType =>
          Selection.inlineFragment (some objectType) []
            (normalizeSelectionSet schema objectType selectionSet))) := by
  intro selection hmem
  rcases List.mem_map.mp hmem with ⟨objectType, _hobjectType, hselection⟩
  subst selection
  simp [Selection.isInlineFragment]

theorem possibleTypeNormalizations_groundTyped
    (schema : Schema)
    (possibleTypes : List Name) (selectionSet : List Selection)
    (hpossible :
      ∀ objectType, objectType ∈ possibleTypes -> schema.objectType objectType)
    (hnormalize :
      ∀ objectType, objectType ∈ possibleTypes ->
        selectionSetGroundTyped schema
          (normalizeSelectionSet schema objectType selectionSet)) :
    selectionSetGroundTyped schema
      (possibleTypes.map
        (fun objectType =>
          Selection.inlineFragment (some objectType) []
            (normalizeSelectionSet schema objectType selectionSet))) := by
  unfold selectionSetGroundTyped
  constructor
  · exact Or.inr
      (possibleTypeNormalizations_allInlineFragments schema possibleTypes
        selectionSet)
  · intro selection hmem
    rcases List.mem_map.mp hmem with ⟨objectType, hobjectType, hselection⟩
    subst selection
    unfold selectionGroundTyped
    exact ⟨
      hpossible objectType hobjectType,
      normalizeSelectionSet_allFields schema objectType selectionSet,
      hnormalize objectType hobjectType⟩

theorem normalizeSelectionSet_groundTyped (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ parentType selectionSet,
      selectionSetGroundTyped schema
        (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      unfold selectionSetGroundTyped
      constructor
      · exact Or.inl (normalizeSelectionSet_allFields schema parentType [])
      · intro selection hmem
        simp [normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          (schema.getPossibleTypes returnType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType mergedSubselections))
      have hsubselectionsGround :
          selectionSetGroundTyped schema normalizedSubselections := by
        unfold normalizedSubselections
        by_cases hobject : objectTypeNameBool schema returnType = true
        · simp [hobject]
          exact hmerged
        · have hfalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hfalse]
          exact possibleTypeNormalizations_groundTyped schema
            (schema.getPossibleTypes returnType) mergedSubselections
            (fun objectType hobjectType =>
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType)
            (fun objectType hobjectType => hpossible objectType)
      have hsubselectionsShape :
          selectionsAllFields normalizedSubselections
            ∨ selectionsAllInlineFragments normalizedSubselections := by
        unfold normalizedSubselections
        by_cases hobject : objectTypeNameBool schema returnType = true
        · simp [hobject]
          exact Or.inl
            (normalizeSelectionSet_allFields schema returnType
              mergedSubselections)
        · have hfalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hfalse]
          exact Or.inr
            (possibleTypeNormalizations_allInlineFragments schema
              (schema.getPossibleTypes returnType) mergedSubselections)
      unfold selectionSetGroundTyped
      constructor
      · exact Or.inl (normalizeSelectionSet_allFields schema parentType
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      · intro selection hmem
        simp [normalizeSelectionSet, hlookup] at hmem
        cases hmem with
        | inl hhead =>
            subst selection
            unfold selectionGroundTyped
            change
              (selectionsAllFields normalizedSubselections
                  ∨ selectionsAllInlineFragments normalizedSubselections)
                ∧ selectionSetGroundTyped schema normalizedSubselections
            exact ⟨hsubselectionsShape, hsubselectionsGround⟩
        | inr htail =>
            have hrestGround := hrest
            unfold selectionSetGroundTyped at hrestGround
            exact hrestGround.2 selection htail
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest

theorem selectionSetResponseNameFree_nil (schema : Schema)
    (parentType responseName : Name) :
    selectionSetResponseNameFree schema parentType responseName [] := by
  unfold selectionSetResponseNameFree
  intro selection hselection
  simp at hselection

theorem selectionSetResponseNameFree_cons {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection} :
    selectionResponseNameFree schema parentType responseName selection ->
      selectionSetResponseNameFree schema parentType responseName selectionSet ->
        selectionSetResponseNameFree schema parentType responseName
          (selection :: selectionSet) := by
  unfold selectionSetResponseNameFree
  intro hselection hselectionSet candidate hcandidate
  cases hcandidate with
  | head =>
      exact hselection
  | tail _ htail =>
      exact hselectionSet candidate htail

theorem selectionSetResponseNameFree_head {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection} :
    selectionSetResponseNameFree schema parentType responseName
      (selection :: selectionSet) ->
        selectionResponseNameFree schema parentType responseName selection := by
  unfold selectionSetResponseNameFree
  intro hfree
  exact hfree selection (by simp)

theorem selectionSetResponseNameFree_tail {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection} :
    selectionSetResponseNameFree schema parentType responseName
      (selection :: selectionSet) ->
        selectionSetResponseNameFree schema parentType responseName selectionSet := by
  unfold selectionSetResponseNameFree
  intro hfree candidate hcandidate
  exact hfree candidate (List.mem_cons_of_mem selection hcandidate)

theorem selectionSetResponseNameFree_append {schema : Schema}
    {parentType responseName : Name} {left right : List Selection} :
    selectionSetResponseNameFree schema parentType responseName left ->
      selectionSetResponseNameFree schema parentType responseName right ->
        selectionSetResponseNameFree schema parentType responseName
          (left ++ right) := by
  unfold selectionSetResponseNameFree
  intro hleft hright selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem withoutFieldsWithResponseName_responseNameFree (schema : Schema)
    (parentType responseName : Name) :
    ∀ selectionSet,
      selectionSetResponseNameFree schema parentType responseName
        (withoutFieldsWithResponseName schema responseName selectionSet)
  | [] => by
      simpa [withoutFieldsWithResponseName] using
        selectionSetResponseNameFree_nil schema parentType responseName
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            exact withoutFieldsWithResponseName_responseNameFree schema
              parentType responseName rest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse]
            apply selectionSetResponseNameFree_cons
            · simp [selectionResponseNameFree]
              intro heq
              subst fieldResponseName
              simp at hfalse
            · exact withoutFieldsWithResponseName_responseNameFree schema
                parentType responseName rest
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldsWithResponseName]
          apply selectionSetResponseNameFree_cons
          · cases typeCondition with
            | none =>
                simpa [selectionResponseNameFree] using
                  withoutFieldsWithResponseName_responseNameFree schema
                    parentType responseName selectionSet
            | some typeCondition =>
                simp [selectionResponseNameFree]
                intro _hoverlap
                exact withoutFieldsWithResponseName_responseNameFree schema
                  parentType responseName selectionSet
          · exact withoutFieldsWithResponseName_responseNameFree schema
              parentType responseName rest

theorem withoutFieldsWithResponseName_preserves_responseNameFree
    (schema : Schema) (removedResponseName : Name)
    (parentType responseName : Name) :
    ∀ selectionSet,
      selectionSetResponseNameFree schema parentType responseName selectionSet ->
        selectionSetResponseNameFree schema parentType responseName
          (withoutFieldsWithResponseName schema removedResponseName selectionSet)
  | [], hfree => by
      simpa [withoutFieldsWithResponseName] using hfree
  | selection :: rest, hfree => by
      have hselection := selectionSetResponseNameFree_head hfree
      have hrest := selectionSetResponseNameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == removedResponseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            exact withoutFieldsWithResponseName_preserves_responseNameFree
              schema removedResponseName parentType responseName rest hrest
          · have hfalse : (fieldResponseName == removedResponseName) = false := by
              cases hmatch : fieldResponseName == removedResponseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse]
            exact selectionSetResponseNameFree_cons hselection
              (withoutFieldsWithResponseName_preserves_responseNameFree
                schema removedResponseName parentType responseName rest hrest)
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldsWithResponseName]
          apply selectionSetResponseNameFree_cons
          · cases typeCondition with
            | none =>
                have hselectionSet :
                    selectionSetResponseNameFree schema parentType responseName
                      selectionSet := by
                  simpa [selectionResponseNameFree] using hselection
                simpa [selectionResponseNameFree] using
                  withoutFieldsWithResponseName_preserves_responseNameFree
                    schema removedResponseName parentType responseName
                    selectionSet hselectionSet
            | some typeCondition =>
                have hselectionSet :
                    schema.typesOverlapBool parentType typeCondition = true ->
                      selectionSetResponseNameFree schema parentType responseName
                        selectionSet := by
                  simpa [selectionResponseNameFree] using hselection
                simp [selectionResponseNameFree]
                intro hoverlap
                exact withoutFieldsWithResponseName_preserves_responseNameFree
                  schema removedResponseName parentType responseName
                  selectionSet (hselectionSet hoverlap)
          · exact withoutFieldsWithResponseName_preserves_responseNameFree
              schema removedResponseName parentType responseName rest hrest

theorem normalizeSelectionSet_responseNameFree (schema : Schema) :
    ∀ parentType responseName selectionSet,
      selectionSetResponseNameFree schema parentType responseName selectionSet ->
        selectionSetResponseNameFree schema parentType responseName
          (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType responseName selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _hfree
      simpa [normalizeSelectionSet] using
        selectionSetResponseNameFree_nil schema parentType responseName
  | case2 parentType rest fieldResponseName fieldName arguments directives
      selectionSet hlookup hrest =>
      intro hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hfiltered :=
        withoutFieldsWithResponseName_preserves_responseNameFree schema
          fieldResponseName parentType responseName rest htail
      simpa [normalizeSelectionSet, hlookup] using hrest hfiltered
  | case3 parentType rest fieldResponseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro hfree
      have hhead := selectionSetResponseNameFree_head hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hfiltered :=
        withoutFieldsWithResponseName_preserves_responseNameFree schema
          fieldResponseName parentType responseName rest htail
      have hnormalizedRest := hrest hfiltered
      simp [normalizeSelectionSet, hlookup]
      have hnormalizedHead :
          selectionResponseNameFree schema parentType responseName
            (Selection.field fieldResponseName fieldName arguments directives
              (if objectTypeNameBool schema returnType then
                normalizeSelectionSet schema returnType mergedSubselections
              else
                (schema.getPossibleTypes returnType).map
                  (fun objectType =>
                    Selection.inlineFragment (some objectType) []
                      (normalizeSelectionSet schema objectType
                        mergedSubselections)))) := by
        simpa [selectionResponseNameFree] using hhead
      exact selectionSetResponseNameFree_cons hnormalizedHead hnormalizedRest
  | case4 parentType rest directives selectionSet happend =>
      intro hfree
      have hhead := selectionSetResponseNameFree_head hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hsubselections :
          selectionSetResponseNameFree schema parentType responseName
            selectionSet := by
        simpa [selectionResponseNameFree] using hhead
      have happendFree :
          selectionSetResponseNameFree schema parentType responseName
            (selectionSet ++ rest) := by
        exact selectionSetResponseNameFree_append hsubselections htail
      simpa [normalizeSelectionSet] using happend happendFree
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
      intro hfree
      have hhead := selectionSetResponseNameFree_head hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hheadApplies :
          schema.typesOverlapBool parentType typeCondition = true ->
            selectionSetResponseNameFree schema parentType responseName
              selectionSet := by
        simpa [selectionResponseNameFree] using hhead
      have hsubselections :
          selectionSetResponseNameFree schema parentType responseName
            selectionSet := by
        exact hheadApplies hoverlap
      have happendFree :
          selectionSetResponseNameFree schema parentType responseName
            (selectionSet ++ rest) :=
        selectionSetResponseNameFree_append hsubselections htail
      simpa [normalizeSelectionSet, hoverlap] using happend happendFree
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      intro hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest htail

theorem responseName_not_mem_filterMap_of_responseNameFree
    {schema : Schema} {parentType responseName : Name} :
    ∀ selectionSet,
      selectionSetResponseNameFree schema parentType responseName selectionSet ->
        responseName ∉ selectionSet.filterMap Selection.responseName? := by
  intro selectionSet
  induction selectionSet with
  | nil =>
      intro _hfree
      simp
  | cons selection rest ih =>
      intro hfree
      have hhead := selectionSetResponseNameFree_head hfree
      have hrest := selectionSetResponseNameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hheadNe : fieldResponseName ≠ responseName := by
            simpa [selectionResponseNameFree] using hhead
          simp [Selection.responseName?, ih hrest]
          intro heq
          exact hheadNe heq.symm
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.responseName?, ih hrest]

theorem normalizeSelectionSet_without_responseName_not_mem
    (schema : Schema) (parentType responseName : Name)
    (selectionSet : List Selection) :
    responseName ∉
      (normalizeSelectionSet schema parentType
        (withoutFieldsWithResponseName schema responseName selectionSet)).filterMap
        Selection.responseName? := by
  apply responseName_not_mem_filterMap_of_responseNameFree
  exact normalizeSelectionSet_responseNameFree schema parentType responseName
    (withoutFieldsWithResponseName schema responseName selectionSet)
    (withoutFieldsWithResponseName_responseNameFree schema parentType
      responseName selectionSet)

theorem normalizeSelectionSet_responseNamesNodup (schema : Schema) :
    ∀ parentType selectionSet,
      responseNamesNodup (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      simp [normalizeSelectionSet, responseNamesNodup]
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      have htailNoResponseName :=
        normalizeSelectionSet_without_responseName_not_mem schema parentType
          responseName rest
      have htailNodup := hrest
      simp [normalizeSelectionSet, hlookup]
      unfold responseNamesNodup at htailNodup ⊢
      simp [Selection.responseName?]
      constructor
      · intro name hname hresponse
        exact htailNoResponseName
          (List.mem_filterMap.mpr ⟨name, hname, hresponse⟩)
      · exact htailNodup
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest

theorem inlineFragmentTypeConditionsNodup_of_selectionsAllFields
    {selectionSet : List Selection} :
    selectionsAllFields selectionSet ->
      inlineFragmentTypeConditionsNodup selectionSet := by
  intro hfields
  induction selectionSet with
  | nil =>
      simp [inlineFragmentTypeConditionsNodup]
  | cons selection rest ih =>
      have hhead : Selection.isField selection := hfields selection (by simp)
      have hrest : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hfields candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          simpa [inlineFragmentTypeConditionsNodup] using ih hrest
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hhead

theorem selectionSetNonRedundant_selection {selectionSet : List Selection}
    {selection : Selection} :
    selectionSetNonRedundant selectionSet ->
      selection ∈ selectionSet ->
        selectionNonRedundant selection := by
  intro hnonRedundant hselection
  unfold selectionSetNonRedundant at hnonRedundant
  exact hnonRedundant.2.2 selection hselection

theorem possibleTypeNormalizations_responseNamesNodup
    (schema : Schema) (possibleTypes : List Name)
    (selectionSet : List Selection) :
    responseNamesNodup
      (possibleTypes.map
        (fun objectType =>
          Selection.inlineFragment (some objectType) []
            (normalizeSelectionSet schema objectType selectionSet))) := by
  have hfilterNone :
      ∀ names : List Name,
        (names.filterMap (fun _ => (none : Option Name))).Nodup := by
    intro names
    induction names with
    | nil => simp
    | cons name rest ih => simp [ih]
  simpa [responseNamesNodup, Selection.responseName?] using
    hfilterNone possibleTypes

theorem possibleTypeNormalizations_inlineFragmentTypeConditionsNodup
    (schema : Schema) (possibleTypes : List Name)
    (selectionSet : List Selection) :
    possibleTypes.Nodup ->
      inlineFragmentTypeConditionsNodup
        (possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (normalizeSelectionSet schema objectType selectionSet))) := by
  intro hnodup
  simpa [inlineFragmentTypeConditionsNodup, Function.comp_def] using hnodup

theorem possibleTypeNormalizations_nonRedundant
    (schema : Schema) (possibleTypes : List Name)
    (selectionSet : List Selection) :
    possibleTypes.Nodup ->
      (∀ objectType, objectType ∈ possibleTypes ->
        selectionSetNonRedundant
          (normalizeSelectionSet schema objectType selectionSet)) ->
        selectionSetNonRedundant
          (possibleTypes.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType selectionSet))) := by
  intro hnodup hnormalize
  unfold selectionSetNonRedundant
  constructor
  · exact possibleTypeNormalizations_responseNamesNodup schema possibleTypes
      selectionSet
  · constructor
    · exact possibleTypeNormalizations_inlineFragmentTypeConditionsNodup
        schema possibleTypes selectionSet hnodup
    · intro selection hselection
      rcases List.mem_map.mp hselection with
        ⟨objectType, hobjectType, hselectionEq⟩
      subst selection
      unfold selectionNonRedundant
      exact hnormalize objectType hobjectType

theorem normalizeSelectionSet_nonRedundant (schema : Schema)
    (hpossibleTypesNodup :
      ∀ typeName, (schema.getPossibleTypes typeName).Nodup) :
    ∀ parentType selectionSet,
      selectionSetNonRedundant
        (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      simp [normalizeSelectionSet, selectionSetNonRedundant,
        responseNamesNodup, inlineFragmentTypeConditionsNodup]
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          (schema.getPossibleTypes returnType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType mergedSubselections))
      have hsubselectionsNonRedundant :
          selectionSetNonRedundant normalizedSubselections := by
        unfold normalizedSubselections
        by_cases hobject : objectTypeNameBool schema returnType = true
        · simp [hobject]
          exact hmerged
        · have hfalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hfalse]
          exact possibleTypeNormalizations_nonRedundant schema
            (schema.getPossibleTypes returnType) mergedSubselections
            (hpossibleTypesNodup returnType)
            (fun objectType hobjectType => hpossible objectType)
      unfold selectionSetNonRedundant
      constructor
      · exact normalizeSelectionSet_responseNamesNodup schema parentType
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest)
      · constructor
        · exact inlineFragmentTypeConditionsNodup_of_selectionsAllFields
            (normalizeSelectionSet_allFields schema parentType
              (Selection.field responseName fieldName arguments directives
                selectionSet :: rest))
        · intro selection hselection
          simp [normalizeSelectionSet, hlookup] at hselection
          cases hselection with
          | inl hhead =>
              subst selection
              unfold selectionNonRedundant
              change selectionSetNonRedundant normalizedSubselections
              exact hsubselectionsNonRedundant
          | inr htail =>
              exact selectionSetNonRedundant_selection hrest htail
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest

theorem normalizeSelectionSet_normal (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name) (selectionSet : List Selection) :
    selectionSetNormal schema
      (normalizeSelectionSet schema parentType selectionSet) := by
  exact ⟨
    normalizeSelectionSet_groundTyped schema hschema parentType selectionSet,
    normalizeSelectionSet_nonRedundant schema
      (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema)
      parentType selectionSet⟩

theorem normalizeOperation_normal (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (operation : Operation) :
    operationNormal schema (normalizeOperation schema operation) := by
  exact normalizeSelectionSet_normal schema hschema operation.rootType
    operation.selectionSet

theorem groundNormalFormCorrect_of_semanticsPreserved
    (schema : Schema) (operation : Operation) :
    groundTypeNormalFormSemanticsPreserved schema operation ->
      groundNormalFormCorrect schema operation := by
  intro hpreserved
  unfold groundNormalFormCorrect DataModel.operationsEquivalentOnData
    DataModel.executeOperation
  intro store variableValues root _hstore _hroot
  exact hpreserved store.resolvers variableValues root.toExecutionValue

theorem groundNormalFormCorrect_of_semanticsPreservation
    (schema : Schema) (operation : Operation) :
    groundTypeNormalFormSemanticsPreservation schema operation ->
      SchemaWellFormedness.schemaWellFormed schema ->
        Validation.operationDefinitionValid schema operation ->
          operationDirectiveFree operation ->
            groundNormalFormCorrect schema operation := by
  intro hpreservation hschema hvalid hfree
  exact groundNormalFormCorrect_of_semanticsPreserved schema operation
    (hpreservation hschema hvalid hfree)

theorem selectionDirectivesAllowBool_nil
    (variableValues : Execution.VariableValues) :
    Execution.selectionDirectivesAllowBool variableValues [] = true := by
  rfl

theorem selectionDirectiveFree_directivesAllowBool
    (variableValues : Execution.VariableValues) {selection : Selection} :
    selectionDirectiveFree selection ->
      match selection with
      | .field _responseName _fieldName _arguments directives _selectionSet =>
          Execution.selectionDirectivesAllowBool variableValues directives = true
      | .inlineFragment _typeCondition directives _selectionSet =>
          Execution.selectionDirectivesAllowBool variableValues directives = true := by
  intro hfree
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      have hdirectives : directives = [] := hfree.1
      subst directives
      rfl
  | inlineFragment typeCondition directives selectionSet =>
      have hdirectives : directives = [] := hfree.1
      subst directives
      rfl

theorem collectSelection_field_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] selectionSet)
      =
      [(responseName, [{
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      }])] := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem collectSelection_inlineFragment_none_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.inlineFragment none [] selectionSet)
      =
      Execution.collectFields schema variableValues parentType source
        selectionSet := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem collectSelection_inlineFragment_some_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name) (source : Execution.Value)
    (selectionSet : List Selection) :
    Execution.collectSelection schema variableValues parentType source
      (Selection.inlineFragment (some typeCondition) [] selectionSet)
      =
      if Execution.doesFragmentTypeApplyBool schema parentType source
          typeCondition then
        Execution.collectFields schema variableValues typeCondition source
          selectionSet
      else
        [] := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem normalizeOperation_name (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).name = operation.name := by
  rfl

theorem normalizeOperation_rootType (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).rootType = operation.rootType := by
  rfl

theorem normalizeOperation_variableDefinitions (schema : Schema)
    (operation : Operation) :
    (normalizeOperation schema operation).variableDefinitions
      = operation.variableDefinitions := by
  rfl

end GroundTypeNormalization

end NormalForm

end GraphQL
