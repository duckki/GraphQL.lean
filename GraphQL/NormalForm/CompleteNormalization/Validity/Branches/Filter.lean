import GraphQL.NormalForm.CompleteNormalization.Validity.Branches.Sources

/-!
Boolean filtering and final complete-normalization branch validity facts.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem collectFields_filterSelectionSetBoolCase_mem_source
    (schema : Schema) (boolCase : BoolCase) :
    ∀ parentType selectionSet filteredField,
      filteredField ∈ FieldMerge.collectFields schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet) ->
        ∃ sourceField,
          sourceField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ BoolFilteredScopedFieldSource schema boolCase sourceField
              filteredField
  | _parentType, [], _filteredField, hfield => by
      simp [filterSelectionSetBoolCase, FieldMerge.collectFields] at hfield
  | parentType,
    Selection.field responseName fieldName arguments directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow,
              FieldMerge.collectFields] at hfield
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [hlookup] at hfield
                rcases
                  collectFields_filterSelectionSetBoolCase_mem_source schema
                    boolCase parentType rest filteredField hfield with
                  ⟨sourceField, hsourceMem, hsource⟩
                exact ⟨sourceField, by
                  simp [FieldMerge.collectFields, hlookup, hsourceMem],
                  hsource⟩
            | some fieldDefinition =>
                simp [hlookup] at hfield
                rcases hfield with hhead | htail
                · subst filteredField
                  refine ⟨{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    outputType := fieldDefinition.outputType,
                    selectionSet := []
                  }, ?_, ?_⟩
                  · simp [FieldMerge.collectFields, hlookup]
                  · exact ⟨rfl, rfl, rfl, rfl, rfl, by
                      simp [filterSelectionSetBoolCase]⟩
                · rcases
                    collectFields_filterSelectionSetBoolCase_mem_source schema
                      boolCase parentType rest filteredField htail with
                    ⟨sourceField, hsourceMem, hsource⟩
                  exact ⟨sourceField, by
                    simp [FieldMerge.collectFields, hlookup, hsourceMem],
                    hsource⟩
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase
                  (child :: children) with
            | nil =>
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source schema
                        boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
            | cons filteredChild filteredChildren =>
                simp [filterSelectionSetBoolCase, hallow, hchild,
                  FieldMerge.collectFields] at hfield
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source
                        schema boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          cases hlookup : schema.lookupField parentType fieldName
          <;> simp [FieldMerge.collectFields, hlookup, hsourceMem],
          hsource⟩
  | parentType,
    Selection.inlineFragment none directives selectionSet :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source schema
                boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase parentType selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩
  | parentType,
    Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source schema
                boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase typeCondition selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩

theorem collectFields_normalize_filterSelectionSetBoolCase_mem_source
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (boolCase : BoolCase) :
    ∀ parentType selectionSet normalizedField,
      schema.objectType parentType ->
      selectionSetSemanticsReady schema parentType selectionSet ->
      normalizedField ∈ FieldMerge.collectFields schema parentType
        (normalizeSelectionSet schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet)) ->
        ∃ sourceField,
          sourceField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ GroundTypeNormalization.NormalizedFieldSource schema sourceField
              normalizedField := by
  intro parentType selectionSet normalizedField hobject hready hmem
  have hfilteredReady :
      selectionSetSemanticsReady schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) :=
    selectionSetSemanticsReady_filterSelectionSetBoolCase schema boolCase
      parentType selectionSet hready
  rcases
    GroundTypeNormalization.collectFields_normalizeSelectionSet_mem_source
      schema hschema parentType
      (filterSelectionSetBoolCase boolCase selectionSet) normalizedField
      hobject hfilteredReady hmem with
  ⟨filteredField, hfilteredMem, hnormalized⟩
  rcases
    collectFields_filterSelectionSetBoolCase_mem_source schema boolCase
      parentType selectionSet filteredField hfilteredMem with
  ⟨sourceField, hsourceMem, hfilteredSource⟩
  exact ⟨sourceField, hsourceMem,
    normalizedFieldSource_of_boolFiltered hfilteredSource hnormalized⟩

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase
    (schema : Schema) (boolCase : BoolCase)
    {parentType : Name} {selectionSet : List Selection} :
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      FieldMerge.fieldsInSetCanMerge schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) := by
  intro hmerge
  refine
    FieldMerge.FieldsInSetCanMerge.rec
      (motive_1 := fun parentType selectionSet _hmerge =>
        FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet))
      (motive_2 := fun sourceLeft sourceRight _hmerge =>
        ∀ left right,
          BoolFilteredScopedFieldSource schema boolCase sourceLeft left ->
          BoolFilteredScopedFieldSource schema boolCase sourceRight right ->
          left.responseName = right.responseName ->
            FieldMerge.fieldsForNameCanMerge schema left right)
      ?setCase ?fieldCase hmerge
  · intro parentType selectionSet hfields ihfields
    unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      (filterSelectionSetBoolCase boolCase selectionSet) ?_
    dsimp
    intro left hleft right hright hresponse
    rcases
      collectFields_filterSelectionSetBoolCase_mem_source schema
        boolCase parentType selectionSet left hleft with
      ⟨sourceLeft, hsourceLeft, hleftSource⟩
    rcases
      collectFields_filterSelectionSetBoolCase_mem_source schema
        boolCase parentType selectionSet right hright with
      ⟨sourceRight, hsourceRight, hrightSource⟩
    have hsourceResponse :
        sourceLeft.responseName = sourceRight.responseName :=
      hleftSource.responseName.symm.trans
        (hresponse.trans hrightSource.responseName)
    exact ihfields sourceLeft hsourceLeft sourceRight hsourceRight
      hsourceResponse left right hleftSource hrightSource hresponse
  · intro sourceLeft sourceRight hshape hidentity hsubfields ihsubfields
      left right hleftSource hrightSource _hresponse
    refine FieldMerge.FieldsForNameCanMerge.intro left right ?_ ?_ ?_
    · simpa [hleftSource.outputType, hrightSource.outputType] using
        hshape
    · intro hparents
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      rcases hidentity hsourceParents with ⟨hfieldName, harguments⟩
      exact ⟨hleftSource.fieldName.trans
          (hfieldName.trans hrightSource.fieldName.symm),
        by
          simpa [hleftSource.arguments, hrightSource.arguments]
            using harguments⟩
    · intro hparents objectType
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      have hfilteredSubfields :
          FieldMerge.fieldsInSetCanMerge schema objectType
            (filterSelectionSetBoolCase boolCase
              (sourceLeft.selectionSet ++ sourceRight.selectionSet)) :=
        ihsubfields hsourceParents objectType
      rw [filterSelectionSetBoolCase_append] at hfilteredSubfields
      simpa [hleftSource.selectionSet, hrightSource.selectionSet]
        using hfilteredSubfields

theorem filterSelectionSetBoolCase_ne_nil_of_contributes
    (boolCase : BoolCase) :
    ∀ selectionSet,
      selectionSetContributesInBoolCase boolCase selectionSet ->
        filterSelectionSetBoolCase boolCase selectionSet ≠ []
  | [], hcontributes => by
      cases hcontributes
  | selection :: rest, hcontributes => by
      rcases hcontributes with hhead | htail
      · cases selection with
        | field responseName fieldName arguments directives selectionSet =>
            simp [selectionContributesInBoolCase] at hhead
            cases selectionSet with
            | nil =>
                simp [filterSelectionSetBoolCase, hhead]
            | cons child children =>
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase (child :: children) with
                | nil =>
                    simp [filterSelectionSetBoolCase, hhead, hfiltered]
                | cons filteredChild filteredChildren =>
                    simp [filterSelectionSetBoolCase, hhead, hfiltered]
        | inlineFragment typeCondition directives selectionSet =>
            rcases hhead with ⟨hallow, hchildContributes⟩
            have hchild :
                filterSelectionSetBoolCase boolCase selectionSet ≠ [] :=
              filterSelectionSetBoolCase_ne_nil_of_contributes boolCase
                selectionSet hchildContributes
            cases hfiltered :
                filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                exact False.elim (hchild hfiltered)
            | cons child children =>
                simp [filterSelectionSetBoolCase, hallow, hfiltered]
      · have hrest :
            filterSelectionSetBoolCase boolCase rest ≠ [] :=
          filterSelectionSetBoolCase_ne_nil_of_contributes boolCase rest
            htail
        cases selection with
        | field responseName fieldName arguments directives selectionSet =>
            cases hallow : directivesAllowIn boolCase directives
            · simpa [filterSelectionSetBoolCase, hallow] using hrest
            · cases selectionSet with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow]
              | cons child children =>
                  cases hfiltered :
                      filterSelectionSetBoolCase boolCase
                        (child :: children) with
                  | nil =>
                      simp [filterSelectionSetBoolCase, hallow, hfiltered]
                  | cons filteredChild filteredChildren =>
                      simp [filterSelectionSetBoolCase, hallow, hfiltered]
        | inlineFragment typeCondition directives selectionSet =>
            cases hallow : directivesAllowIn boolCase directives
            · simpa [filterSelectionSetBoolCase, hallow] using hrest
            · cases hfiltered :
                  filterSelectionSetBoolCase boolCase selectionSet with
              | nil =>
                  simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                    using hrest
              | cons child children =>
                  simp [filterSelectionSetBoolCase, hallow, hfiltered]

theorem selectionSetValid_filterSelectionSetBoolCase_of_survive
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (boolCase : BoolCase) :
    ∀ parentType selectionSet,
      Validation.selectionSetValid schema variableDefinitions parentType
        selectionSet ->
      selectionSetBoolCaseCompositeChildrenSurvive boolCase selectionSet ->
        Validation.selectionSetValid schema variableDefinitions parentType
          (filterSelectionSetBoolCase boolCase selectionSet)
  | _parentType, [], _hvalid, _hsurvive => by
      simp [filterSelectionSetBoolCase, Validation.selectionSetValid]
  | parentType, selection :: rest, hvalid, hsurvive => by
      have hheadValid :
          Validation.selectionValid schema variableDefinitions parentType
            selection :=
        by
          have hvalidFun :
              ∀ candidate, candidate ∈ selection :: rest ->
                Validation.selectionValid schema variableDefinitions
                  parentType candidate := by
            simpa [Validation.selectionSetValid] using hvalid
          exact hvalidFun selection (by simp)
      have hrestValid :
          Validation.selectionSetValid schema variableDefinitions parentType
            rest :=
        Validation.selectionSetValid_tail hvalid
      have hheadSurvive :
          selectionBoolCaseCompositeChildrenSurvive boolCase selection := by
        simpa [selectionSetBoolCaseCompositeChildrenSurvive] using
          hsurvive.1
      have hrestSurvive :
          selectionSetBoolCaseCompositeChildrenSurvive boolCase rest := by
        simpa [selectionSetBoolCaseCompositeChildrenSurvive] using
          hsurvive.2
      have hrestFilteredValid :
          Validation.selectionSetValid schema variableDefinitions parentType
            (filterSelectionSetBoolCase boolCase rest) :=
        selectionSetValid_filterSelectionSetBoolCase_of_survive schema
          variableDefinitions boolCase parentType rest hrestValid
          hrestSurvive
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hallow : directivesAllowIn boolCase directives
          · simpa [filterSelectionSetBoolCase, hallow] using
              hrestFilteredValid
          · rcases Validation.selectionValid_field_lookup hheadValid with
              ⟨fieldDefinition, hlookup, harguments, hchildValid⟩
            have hdirectives :
                Validation.directivesValid schema variableDefinitions [] :=
              directivesValid_nil schema variableDefinitions
            cases hsourceChild : selectionSet with
            | nil =>
                have hfilteredFieldValid :
                    Validation.selectionValid schema variableDefinitions
                      parentType
                      (.field responseName fieldName arguments [] []) := by
                  simp [Validation.selectionValid, hdirectives, hlookup,
                    harguments]
                  simpa [Validation.fieldSelectionSetValid, hsourceChild]
                    using hchildValid
                simp [filterSelectionSetBoolCase, hallow,
                  Validation.selectionSetValid]
                exact ⟨hfilteredFieldValid,
                  by simpa [Validation.selectionSetValid] using
                    hrestFilteredValid⟩
            | cons child children =>
                have hsurviveChild :
                    selectionSetContributesInBoolCase boolCase
                        (child :: children)
                      ∧ selectionSetBoolCaseCompositeChildrenSurvive
                        boolCase (child :: children) := by
                  simpa [selectionBoolCaseCompositeChildrenSurvive, hallow,
                    hsourceChild] using hheadSurvive
                have hchildNonempty :
                    filterSelectionSetBoolCase boolCase
                      (child :: children) ≠ [] :=
                  filterSelectionSetBoolCase_ne_nil_of_contributes boolCase
                    (child :: children) hsurviveChild.1
                have hsourceChildValid :
                    Validation.selectionSetValid schema variableDefinitions
                      fieldDefinition.outputType.namedType
                      (child :: children) := by
                  rw [hsourceChild] at hchildValid
                  simp [Validation.fieldSelectionSetValid] at hchildValid
                  exact hchildValid.2.2
                have hfilteredChildValid :
                    Validation.selectionSetValid schema variableDefinitions
                      fieldDefinition.outputType.namedType
                      (filterSelectionSetBoolCase boolCase
                        (child :: children)) :=
                  selectionSetValid_filterSelectionSetBoolCase_of_survive
                    schema variableDefinitions boolCase
                    fieldDefinition.outputType.namedType (child :: children)
                    hsourceChildValid hsurviveChild.2
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase
                      (child :: children) with
                | nil =>
                    exact False.elim (hchildNonempty hfiltered)
                | cons filteredChild filteredChildren =>
                    have hfilteredFieldValid :
                        Validation.selectionValid schema variableDefinitions
                          parentType
                          (.field responseName fieldName arguments []
                            (filteredChild :: filteredChildren)) := by
                      simp [Validation.selectionValid, hdirectives, hlookup,
                        harguments]
                      simp [Validation.fieldSelectionSetValid]
                      rw [hsourceChild] at hchildValid
                      simp [Validation.fieldSelectionSetValid] at hchildValid
                      exact ⟨hchildValid.1, hchildValid.2.1,
                        by simpa [hfiltered] using hfilteredChildValid⟩
                    simp [filterSelectionSetBoolCase, hallow,
                      hfiltered, Validation.selectionSetValid]
                    exact ⟨hfilteredFieldValid,
                      by simpa [Validation.selectionSetValid] using
                        hrestFilteredValid⟩
      | inlineFragment typeCondition directives selectionSet =>
          cases hallow : directivesAllowIn boolCase directives
          · simpa [filterSelectionSetBoolCase, hallow] using
              hrestFilteredValid
          · have hchildSurvive :
                selectionSetBoolCaseCompositeChildrenSurvive boolCase
                  selectionSet := by
              simpa [selectionBoolCaseCompositeChildrenSurvive, hallow]
                using hheadSurvive
            cases typeCondition with
            | none =>
                simp [Validation.selectionValid] at hheadValid
                rcases hheadValid with
                  ⟨_hdirectives, _hne, hchildValid⟩
                have hfilteredChildValid :
                    Validation.selectionSetValid schema variableDefinitions
                      parentType
                      (filterSelectionSetBoolCase boolCase selectionSet) :=
                  selectionSetValid_filterSelectionSetBoolCase_of_survive
                    schema variableDefinitions boolCase parentType selectionSet
                    hchildValid hchildSurvive
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase selectionSet with
                | nil =>
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using hrestFilteredValid
                | cons filteredChild filteredChildren =>
                    have hinlineValid :
                        Validation.selectionValid schema variableDefinitions
                          parentType
                          (.inlineFragment none []
                            (filteredChild :: filteredChildren)) := by
                      simp [Validation.selectionValid,
                        directivesValid_nil schema variableDefinitions]
                      simpa [hfiltered] using hfilteredChildValid
                    simp [filterSelectionSetBoolCase, hallow, hfiltered,
                      Validation.selectionSetValid]
                    exact ⟨hinlineValid,
                      by simpa [Validation.selectionSetValid] using
                        hrestFilteredValid⟩
            | some typeCondition =>
                simp [Validation.selectionValid] at hheadValid
                rcases hheadValid with
                  ⟨_hdirectives, hcomposite, hoverlap, _hne,
                    hchildValid⟩
                have hfilteredChildValid :
                    Validation.selectionSetValid schema variableDefinitions
                      typeCondition
                      (filterSelectionSetBoolCase boolCase selectionSet) :=
                  selectionSetValid_filterSelectionSetBoolCase_of_survive
                    schema variableDefinitions boolCase typeCondition
                    selectionSet hchildValid hchildSurvive
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase selectionSet with
                | nil =>
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using hrestFilteredValid
                | cons filteredChild filteredChildren =>
                    have hinlineValid :
                        Validation.selectionValid schema variableDefinitions
                          parentType
                          (.inlineFragment (some typeCondition) []
                            (filteredChild :: filteredChildren)) := by
                      simp [Validation.selectionValid,
                        directivesValid_nil schema variableDefinitions,
                        hcomposite, hoverlap]
                      simpa [hfiltered] using hfilteredChildValid
                    simp [filterSelectionSetBoolCase, hallow, hfiltered,
                      Validation.selectionSetValid]
                    exact ⟨hinlineValid,
                      by simpa [Validation.selectionSetValid] using
                        hrestFilteredValid⟩

theorem selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (boolCase : BoolCase) :
    ∀ parentType selectionSet,
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType selectionSet ->
      selectionSetBoolCaseCompositeChildrenSurvive boolCase selectionSet ->
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions parentType
          (filterSelectionSetBoolCase boolCase selectionSet)
  | _parentType, [], _himplementation, _hsurvive => by
      simp [filterSelectionSetBoolCase,
        Validation.selectionSetImplementationValidInScope]
  | parentType, selection :: rest, himplementation, hsurvive => by
      have hheadImplementation :
          Validation.selectionImplementationValid schema variableDefinitions
            parentType selection :=
        GroundTypeNormalization.selectionSetImplementationValidInScope_head
          himplementation
      have hrestImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType rest :=
        GroundTypeNormalization.selectionSetImplementationValidInScope_tail
          himplementation
      have hheadSurvive :
          selectionBoolCaseCompositeChildrenSurvive boolCase selection := by
        simpa [selectionSetBoolCaseCompositeChildrenSurvive] using
          hsurvive.1
      have hrestSurvive :
          selectionSetBoolCaseCompositeChildrenSurvive boolCase rest := by
        simpa [selectionSetBoolCaseCompositeChildrenSurvive] using
          hsurvive.2
      have hrestFilteredImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType
            (filterSelectionSetBoolCase boolCase rest) :=
        selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
          schema variableDefinitions boolCase parentType rest
          hrestImplementation hrestSurvive
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hallow : directivesAllowIn boolCase directives
          · simpa [filterSelectionSetBoolCase, hallow] using
              hrestFilteredImplementation
          · have hsourceFieldValid :
                Validation.selectionValid schema variableDefinitions parentType
                  (.field responseName fieldName arguments directives
                    selectionSet) := by
              simpa [Validation.selectionImplementationValid] using
                hheadImplementation.1
            rcases Validation.selectionValid_field_lookup hsourceFieldValid with
              ⟨fieldDefinition, hlookup, _harguments, _hchildValid⟩
            have hfilteredFieldValidInSingleton :
                Validation.selectionSetValid schema variableDefinitions
                  parentType
                  (filterSelectionSetBoolCase boolCase
                    [.field responseName fieldName arguments directives
                      selectionSet]) :=
              selectionSetValid_filterSelectionSetBoolCase_of_survive schema
                variableDefinitions boolCase parentType
                [.field responseName fieldName arguments directives
                  selectionSet]
                (by
                  simp [Validation.selectionSetValid]
                  exact hsourceFieldValid)
                (by
                  simp [selectionSetBoolCaseCompositeChildrenSurvive]
                  exact hheadSurvive)
            cases hsourceChild : selectionSet with
            | nil =>
                have hfilteredFieldValid :
                    Validation.selectionValid schema variableDefinitions
                      parentType
                      (.field responseName fieldName arguments [] []) := by
                  simpa [filterSelectionSetBoolCase, hallow, hsourceChild,
                    Validation.selectionSetValid]
                    using hfilteredFieldValidInSingleton
                have hfilteredFieldImplementation :
                    Validation.selectionImplementationValid schema
                      variableDefinitions parentType
                      (.field responseName fieldName arguments [] []) := by
                  simp [Validation.selectionImplementationValid, hlookup]
                  exact ⟨hfilteredFieldValid,
                    by simp [Validation.selectionSetImplementationValidInScope],
                    by
                      intro objectType hpossible
                      simp [Validation.selectionSetImplementationValidInScope]⟩
                simp [filterSelectionSetBoolCase, hallow,
                  Validation.selectionSetImplementationValidInScope]
                exact ⟨hfilteredFieldImplementation,
                  hrestFilteredImplementation⟩
            | cons child children =>
                have hsurviveChild :
                    selectionSetContributesInBoolCase boolCase
                        (child :: children)
                      ∧ selectionSetBoolCaseCompositeChildrenSurvive
                        boolCase (child :: children) := by
                  simpa [selectionBoolCaseCompositeChildrenSurvive, hallow,
                    hsourceChild] using hheadSurvive
                have hchildNonempty :
                    filterSelectionSetBoolCase boolCase
                      (child :: children) ≠ [] :=
                  filterSelectionSetBoolCase_ne_nil_of_contributes boolCase
                    (child :: children) hsurviveChild.1
                have hsourceChildImplementation :
                    Validation.selectionSetImplementationValidInScope schema
                      variableDefinitions
                      fieldDefinition.outputType.namedType
                      (child :: children) := by
                  simp [Validation.selectionImplementationValid, hlookup,
                    hsourceChild] at hheadImplementation
                  exact hheadImplementation.2.1
                have hfilteredChildImplementation :
                    Validation.selectionSetImplementationValidInScope schema
                      variableDefinitions
                      fieldDefinition.outputType.namedType
                      (filterSelectionSetBoolCase boolCase
                        (child :: children)) :=
                  selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
                    schema variableDefinitions boolCase
                    fieldDefinition.outputType.namedType (child :: children)
                    hsourceChildImplementation hsurviveChild.2
                have hfilteredObjectImplementation :
                    ∀ objectType,
                      objectType ∈ schema.getPossibleTypes
                          fieldDefinition.outputType.namedType ->
                        Validation.selectionSetImplementationValidInScope
                          schema variableDefinitions objectType
                          (filterSelectionSetBoolCase boolCase
                            (child :: children)) := by
                  intro objectType hpossible
                  have hsourceObjectImplementation :
                      Validation.selectionSetImplementationValidInScope schema
                        variableDefinitions objectType (child :: children) := by
                    simp [Validation.selectionImplementationValid, hlookup,
                      hsourceChild] at hheadImplementation
                    exact hheadImplementation.2.2 objectType hpossible
                  exact
                    selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
                      schema variableDefinitions boolCase objectType
                      (child :: children) hsourceObjectImplementation
                      hsurviveChild.2
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase
                      (child :: children) with
                | nil =>
                    exact False.elim (hchildNonempty hfiltered)
                | cons filteredChild filteredChildren =>
                    have hfilteredFieldValid :
                        Validation.selectionValid schema variableDefinitions
                          parentType
                          (.field responseName fieldName arguments []
                            (filteredChild :: filteredChildren)) := by
                      simpa [filterSelectionSetBoolCase, hallow, hsourceChild,
                        hfiltered, Validation.selectionSetValid]
                        using hfilteredFieldValidInSingleton
                    have hfilteredFieldImplementation :
                        Validation.selectionImplementationValid schema
                          variableDefinitions parentType
                          (.field responseName fieldName arguments []
                            (filteredChild :: filteredChildren)) := by
                      simp [Validation.selectionImplementationValid, hlookup]
                      exact ⟨hfilteredFieldValid,
                        by simpa [hfiltered] using
                          hfilteredChildImplementation,
                        by
                          intro objectType hpossible
                          simpa [hfiltered] using
                            hfilteredObjectImplementation objectType
                              hpossible⟩
                    simp [filterSelectionSetBoolCase, hallow,
                      hfiltered,
                      Validation.selectionSetImplementationValidInScope]
                    exact ⟨hfilteredFieldImplementation,
                      hrestFilteredImplementation⟩
      | inlineFragment typeCondition directives selectionSet =>
          cases hallow : directivesAllowIn boolCase directives
          · simpa [filterSelectionSetBoolCase, hallow] using
              hrestFilteredImplementation
          · have hchildSurvive :
                selectionSetBoolCaseCompositeChildrenSurvive boolCase
                  selectionSet := by
              simpa [selectionBoolCaseCompositeChildrenSurvive, hallow]
                using hheadSurvive
            cases hfiltered :
                filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                simpa [filterSelectionSetBoolCase, hallow, hfiltered] using
                  hrestFilteredImplementation
            | cons filteredChild filteredChildren =>
                have hfilteredInlineImplementation :
                    Validation.selectionImplementationValid schema
                      variableDefinitions parentType
                      (.inlineFragment typeCondition []
                        (filteredChild :: filteredChildren)) := by
                  cases typeCondition with
                  | none =>
                      have hsourceChildImplementation :
                          Validation.selectionSetImplementationValidInScope
                            schema variableDefinitions parentType
                            selectionSet := by
                        simpa [Validation.selectionImplementationValid] using
                          hheadImplementation
                      have hfilteredChildImplementation :
                          Validation.selectionSetImplementationValidInScope
                            schema variableDefinitions parentType
                            (filteredChild :: filteredChildren) := by
                        simpa [hfiltered] using
                          selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
                            schema variableDefinitions boolCase parentType
                            selectionSet hsourceChildImplementation
                            hchildSurvive
                      simpa [Validation.selectionImplementationValid] using
                        hfilteredChildImplementation
                  | some typeCondition =>
                      intro hoverlap
                      have hsourceChildImplementation :
                          Validation.selectionSetImplementationValidInScope
                              schema variableDefinitions typeCondition
                              selectionSet
                            ∧ ∀ objectType,
                              objectType ∈ schema.getPossibleTypes
                                  typeCondition ->
                                Validation.selectionSetImplementationValidInScope
                                  schema variableDefinitions objectType
                                  selectionSet := by
                        simpa [Validation.selectionImplementationValid,
                          hoverlap] using hheadImplementation
                      have hfilteredTypeConditionImplementation :
                          Validation.selectionSetImplementationValidInScope
                            schema variableDefinitions typeCondition
                            (filteredChild :: filteredChildren) := by
                        simpa [hfiltered] using
                          selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
                            schema variableDefinitions boolCase typeCondition
                            selectionSet hsourceChildImplementation.1
                            hchildSurvive
                      refine ⟨hfilteredTypeConditionImplementation, ?_⟩
                      intro objectType hpossible
                      simpa [hfiltered] using
                        selectionSetImplementationValidInScope_filterSelectionSetBoolCase_of_survive
                          schema variableDefinitions boolCase objectType
                          selectionSet
                          (hsourceChildImplementation.2 objectType hpossible)
                          hchildSurvive
                simp [filterSelectionSetBoolCase, hallow, hfiltered,
                  Validation.selectionSetImplementationValidInScope]
                exact ⟨hfilteredInlineImplementation,
                  hrestFilteredImplementation⟩

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase_pair
    (schema : Schema)
    {parentType : Name} {leftSet rightSet : List Selection}
    (leftCase rightCase : BoolCase) :
    FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet) ->
      FieldMerge.fieldsInSetCanMerge schema parentType
        (filterSelectionSetBoolCase leftCase leftSet
          ++ filterSelectionSetBoolCase rightCase rightSet) := by
  intro hmerge
  refine
    FieldMerge.FieldsInSetCanMerge.rec
      (motive_1 := fun parentType selectionSet _hmerge =>
        ∀ leftSet rightSet,
          selectionSet = leftSet ++ rightSet ->
          ∀ leftCase rightCase,
            FieldMerge.fieldsInSetCanMerge schema parentType
              (filterSelectionSetBoolCase leftCase leftSet
                ++ filterSelectionSetBoolCase rightCase rightSet))
      (motive_2 := fun sourceLeft sourceRight _hmerge =>
        ∀ leftCase rightCase left right,
          BoolFilteredScopedFieldSource schema leftCase sourceLeft left ->
          BoolFilteredScopedFieldSource schema rightCase sourceRight right ->
          left.responseName = right.responseName ->
            FieldMerge.fieldsForNameCanMerge schema left right)
      ?setCase ?fieldCase hmerge leftSet rightSet rfl leftCase rightCase
  · intro parentType selectionSet hfields ihfields leftSet rightSet
      hsplit leftCase rightCase
    unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      (filterSelectionSetBoolCase leftCase leftSet
        ++ filterSelectionSetBoolCase rightCase rightSet) ?_
    dsimp
    intro left hleft right hright hresponse
    rw [FieldMerge.collectFields_append] at hleft hright
    rcases List.mem_append.mp hleft with hleftInLeft | hleftInRight
    · rcases
        collectFields_filterSelectionSetBoolCase_mem_source schema
          leftCase parentType leftSet left hleftInLeft with
        ⟨sourceLeft, hsourceLeftMem, hleftSource⟩
      have hsourceLeftAll :
          sourceLeft ∈ FieldMerge.collectFields schema parentType
            selectionSet := by
        rw [hsplit, FieldMerge.collectFields_append]
        exact List.mem_append_left
          (FieldMerge.collectFields schema parentType rightSet)
          hsourceLeftMem
      rcases List.mem_append.mp hright with hrightInLeft | hrightInRight
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            leftCase parentType leftSet right hrightInLeft with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_left
            (FieldMerge.collectFields schema parentType rightSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse leftCase leftCase left right
          hleftSource hrightSource hresponse
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            rightCase parentType rightSet right hrightInRight with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_right
            (FieldMerge.collectFields schema parentType leftSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse leftCase rightCase left right
          hleftSource hrightSource hresponse
    · rcases
        collectFields_filterSelectionSetBoolCase_mem_source schema
          rightCase parentType rightSet left hleftInRight with
        ⟨sourceLeft, hsourceLeftMem, hleftSource⟩
      have hsourceLeftAll :
          sourceLeft ∈ FieldMerge.collectFields schema parentType
            selectionSet := by
        rw [hsplit, FieldMerge.collectFields_append]
        exact List.mem_append_right
          (FieldMerge.collectFields schema parentType leftSet)
          hsourceLeftMem
      rcases List.mem_append.mp hright with hrightInLeft | hrightInRight
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            leftCase parentType leftSet right hrightInLeft with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_left
            (FieldMerge.collectFields schema parentType rightSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse rightCase leftCase left right
          hleftSource hrightSource hresponse
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            rightCase parentType rightSet right hrightInRight with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_right
            (FieldMerge.collectFields schema parentType leftSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse rightCase rightCase left right
          hleftSource hrightSource hresponse
  · intro sourceLeft sourceRight hshape hidentity hsubfields ihsubfields
      leftCase rightCase left right hleftSource hrightSource _hresponse
    refine FieldMerge.FieldsForNameCanMerge.intro left right ?_ ?_ ?_
    · simpa [hleftSource.outputType, hrightSource.outputType] using
        hshape
    · intro hparents
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      rcases hidentity hsourceParents with ⟨hfieldName, harguments⟩
      exact ⟨hleftSource.fieldName.trans
          (hfieldName.trans hrightSource.fieldName.symm),
        by
          simpa [hleftSource.arguments, hrightSource.arguments]
            using harguments⟩
    · intro hparents objectType
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      have hfilteredSubfields :
          FieldMerge.fieldsInSetCanMerge schema objectType
            (filterSelectionSetBoolCase leftCase sourceLeft.selectionSet
              ++ filterSelectionSetBoolCase rightCase
                sourceRight.selectionSet) :=
        ihsubfields hsourceParents objectType sourceLeft.selectionSet
          sourceRight.selectionSet rfl leftCase rightCase
      simpa [hleftSource.selectionSet, hrightSource.selectionSet]
        using hfilteredSubfields

mutual
  theorem filterSelectionSetBoolCase_selectionLookupValid
      (schema : Schema) (boolCase : BoolCase) :
      ∀ parentType sourceSelection filteredSelection,
        filteredSelection ∈
          filterSelectionSetBoolCase boolCase [sourceSelection] ->
        selectionLookupValid schema parentType sourceSelection ->
          selectionLookupValid schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionLookupValid] using hlookupValid
          | cons child children =>
              cases hchildFiltered :
                  filterSelectionSetBoolCase boolCase
                    (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hsourceChildLookup :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChildLookup :
                  selectionSetLookupValid schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetLookupValid schema
                    boolCase parentType selectionSet hsourceChildLookup
              simpa [selectionLookupValid] using hfilteredChildLookup
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hsourceChildLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChildLookup :
                  selectionSetLookupValid schema typeCondition
                    (filteredChild :: filteredChildren) := by
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetLookupValid schema
                    boolCase typeCondition selectionSet hsourceChildLookup
              simpa [selectionLookupValid] using hfilteredChildLookup
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem filterSelectionSetBoolCase_selectionSetLookupValid
      (schema : Schema) (boolCase : BoolCase) :
      ∀ parentType selectionSet,
        selectionSetLookupValid schema parentType selectionSet ->
        selectionSetLookupValid schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hlookupValid => by
        simp [filterSelectionSetBoolCase, selectionSetLookupValid]
    | parentType, selection :: rest, hlookupValid => by
        have hhead :
            selectionLookupValid schema parentType selection :=
          selectionSetLookupValid_head hlookupValid
        have htail :
            selectionSetLookupValid schema parentType rest :=
          selectionSetLookupValid_tail hlookupValid
        have hheadFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetLookupValid
          intro candidate hcandidate
          exact filterSelectionSetBoolCase_selectionLookupValid schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          filterSelectionSetBoolCase_selectionSetLookupValid schema
            boolCase parentType rest htail
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetLookupValid_append hheadFiltered hrestFiltered
end

mutual
  theorem filterSelectionSetBoolCase_selectionSemanticsReady
      (schema : Schema) (boolCase : BoolCase) :
      ∀ parentType sourceSelection filteredSelection,
        filteredSelection ∈
          filterSelectionSetBoolCase boolCase [sourceSelection] ->
        selectionSemanticsReady schema parentType sourceSelection ->
          selectionSemanticsReady schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionSemanticsReady] using hready
          | cons child children =>
              cases hchildFiltered :
                  filterSelectionSetBoolCase boolCase
                    (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, _hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  exact ⟨fieldDefinition, hlookup, by
                    intro runtimeType _hincludes
                    exact selectionSetSemanticsReady_nil schema runtimeType⟩
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  refine ⟨fieldDefinition, hlookup, ?_⟩
                  intro runtimeType hincludes
                  have hsourceChildReady :
                      selectionSetSemanticsReady schema runtimeType
                        (child :: children) :=
                    hchildrenReady runtimeType hincludes
                  simpa [hchildFiltered] using
                    filterSelectionSetBoolCase_selectionSetSemanticsReady
                      schema boolCase runtimeType (child :: children)
                      hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hsourceChildReady :
                  selectionSetSemanticsReady schema parentType selectionSet := by
                simpa [selectionSemanticsReady] using hready
              have hfilteredChildReady :
                  selectionSetSemanticsReady schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetSemanticsReady
                    schema boolCase parentType selectionSet hsourceChildReady
              simpa [selectionSemanticsReady] using hfilteredChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hreadyParts :
                  selectionSetLookupValid schema typeCondition selectionSet
                    ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                      selectionSetSemanticsReady schema parentType
                        selectionSet) := by
                simpa [selectionSemanticsReady] using hready
              simp [selectionSemanticsReady]
              constructor
              · simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetLookupValid schema
                    boolCase typeCondition selectionSet hreadyParts.1
              · intro hoverlap
                have hsourceChildReady :
                    selectionSetSemanticsReady schema parentType selectionSet :=
                  hreadyParts.2 hoverlap
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetSemanticsReady
                    schema boolCase parentType selectionSet hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem filterSelectionSetBoolCase_selectionSetSemanticsReady
      (schema : Schema) (boolCase : BoolCase) :
      ∀ parentType selectionSet,
        selectionSetSemanticsReady schema parentType selectionSet ->
        selectionSetSemanticsReady schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hready => by
        simpa [filterSelectionSetBoolCase] using
          selectionSetSemanticsReady_nil schema parentType
    | parentType, selection :: rest, hready => by
        have hhead :
            selectionSemanticsReady schema parentType selection := by
          unfold selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            selectionSetSemanticsReady schema parentType rest :=
          selectionSetSemanticsReady_tail hready
        have hheadFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetSemanticsReady
          intro candidate hcandidate
          exact filterSelectionSetBoolCase_selectionSemanticsReady schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          filterSelectionSetBoolCase_selectionSetSemanticsReady schema
            boolCase parentType rest htailReady
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetSemanticsReady_append hheadFiltered hrestFiltered
end

theorem filterSelectionSetBoolCase_singleton_nil_or_singleton
    (boolCase : BoolCase) (selection : Selection) :
    filterSelectionSetBoolCase boolCase [selection] = []
      ∨ ∃ filteredSelection,
        filterSelectionSetBoolCase boolCase [selection] =
          [filteredSelection] := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            exact Or.inr ⟨.field responseName fieldName arguments [] [],
              by simp [filterSelectionSetBoolCase, hallow]⟩
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase
                  (child :: children) with
            | nil =>
                exact Or.inr
                  ⟨.field responseName fieldName arguments [] [], by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨.field responseName fieldName arguments []
                    (filteredChild :: filteredChildren), by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        exact Or.inl (by simp [filterSelectionSetBoolCase, hfalse])
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                exact Or.inl (by
                  simp [filterSelectionSetBoolCase, hallow, hchild])
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨.inlineFragment none []
                    (filteredChild :: filteredChildren), by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
          · have hfalse :
                directivesAllowIn boolCase directives = false := by
              cases hmatch : directivesAllowIn boolCase directives
              · rfl
              · contradiction
            exact Or.inl (by simp [filterSelectionSetBoolCase, hfalse])
      | some typeCondition =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                exact Or.inl (by
                  simp [filterSelectionSetBoolCase, hallow, hchild])
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨.inlineFragment (some typeCondition) []
                    (filteredChild :: filteredChildren), by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
          · have hfalse :
                directivesAllowIn boolCase directives = false := by
              cases hmatch : directivesAllowIn boolCase directives
              · rfl
              · contradiction
            exact Or.inl (by simp [filterSelectionSetBoolCase, hfalse])

theorem normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfeasibleAll :
      selectionSetsTypeConditionFeasibleInEveryScope schema)
    (parentType : Name) (selectionSet : List Selection)
    (boolCase : BoolCase) :
    schema.objectType parentType ->
    selectionSetSemanticsReady schema parentType selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      parentType (filterSelectionSetBoolCase boolCase selectionSet) ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions parentType
        (normalizeSelectionSet schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet)) := by
  intro hobject hready hfilteredImplementation hmerge
  exact GroundTypeNormalization.normalizeSelectionSet_normalizedValid schema
    variableDefinitions hschema hfeasibleAll parentType
    (filterSelectionSetBoolCase boolCase selectionSet)
    hobject
    (filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
      parentType selectionSet hready)
    hfilteredImplementation
    (fieldsInSetCanMerge_filterSelectionSetBoolCase schema boolCase hmerge)
    (filterSelectionSetBoolCase_directiveFree schema boolCase selectionSet)

theorem completeNormalizeBranches_selectionSetValid
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfeasibleAll :
      selectionSetsTypeConditionFeasibleInEveryScope schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hrootObject : schema.objectType operation.rootType)
    (hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet)
    (himplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType operation.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet) :
    ∀ cases : List BoolCase,
      (∀ boolCase, boolCase ∈ cases ->
        boolCase ∈ allBoolCases (operationBoolVars operation)) ->
      (∀ boolCase, boolCase ∈ cases ->
        Validation.selectionSetImplementationValidInScope schema
          operation.variableDefinitions operation.rootType
          (filterSelectionSetBoolCase boolCase operation.selectionSet)) ->
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType
        (List.flatten (cases.map (fun boolCase =>
          match normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase boolCase
                operation.selectionSet) with
          | [] => []
          | selection :: rest =>
              wrapWithBoolCase boolCase (selection :: rest))))
  | [], _hcases, _hfilteredCases => by
      simp [Validation.selectionSetValid]
  | boolCase :: restCases, hcases, hfilteredCases => by
      have hcase :
          boolCase ∈ allBoolCases (operationBoolVars operation) :=
        hcases boolCase (by simp)
      have hrest :
          Validation.selectionSetValid schema operation.variableDefinitions
            operation.rootType
            (List.flatten (restCases.map (fun boolCase =>
              match normalizeSelectionSet schema operation.rootType
                  (filterSelectionSetBoolCase boolCase
                    operation.selectionSet) with
              | [] => []
              | selection :: rest =>
                  wrapWithBoolCase boolCase (selection :: rest)))) :=
        completeNormalizeBranches_selectionSetValid schema operation hschema
          hfeasibleAll hoperation hrootObject hready himplementation hmerge restCases
          (by
            intro candidate hcandidate
            exact hcases candidate (by simp [hcandidate]))
          (by
            intro candidate hcandidate
            exact hfilteredCases candidate (by simp [hcandidate]))
      cases hnormalized :
          normalizeSelectionSet schema operation.rootType
            (filterSelectionSetBoolCase boolCase
              operation.selectionSet) with
      | nil =>
          simpa [hnormalized] using hrest
      | cons selection normalizedRest =>
          have hbranchValid :
              GroundTypeNormalization.NormalizedSelectionSetValid schema
                operation.variableDefinitions operation.rootType
                (selection :: normalizedRest) := by
            simpa [hnormalized] using
              normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
                schema operation.variableDefinitions hschema
                hfeasibleAll operation.rootType operation.selectionSet boolCase
                hrootObject hready
                (hfilteredCases boolCase (by simp)) hmerge
          have hvars :
              ∀ varName, varName ∈ boolCase.map Prod.fst ->
                varName ∈ operationBoolVars operation := by
            have hfst := boolCase_map_fst_of_mem_allBoolCases hcase
            intro varName hvar
            simpa [hfst] using hvar
          have hwrapped :
              Validation.selectionSetValid schema operation.variableDefinitions
                operation.rootType
                (wrapWithBoolCase boolCase
                  (selection :: normalizedRest)) :=
            wrapWithBoolCase_selectionSetValid schema operation
              operation.rootType boolCase (selection :: normalizedRest)
              hoperation hvars (by simp) hbranchValid.selectionSetValid
          simpa [hnormalized] using
            Validation.selectionSetValid_append hwrapped hrest

theorem completeNormalizeBranches_implementationValidInScope
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfeasibleAll :
      selectionSetsTypeConditionFeasibleInEveryScope schema)
    (hrootObject : schema.objectType operation.rootType)
    (hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet)
    (himplementation :
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType operation.selectionSet)
    (hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet) :
    ∀ cases : List BoolCase,
      (∀ boolCase, boolCase ∈ cases ->
        Validation.selectionSetImplementationValidInScope schema
          operation.variableDefinitions operation.rootType
          (filterSelectionSetBoolCase boolCase operation.selectionSet)) ->
      Validation.selectionSetImplementationValidInScope schema
        operation.variableDefinitions operation.rootType
        (List.flatten (cases.map (fun boolCase =>
          match normalizeSelectionSet schema operation.rootType
              (filterSelectionSetBoolCase boolCase
                operation.selectionSet) with
          | [] => []
          | selection :: rest =>
              wrapWithBoolCase boolCase (selection :: rest))))
  | [], _hfilteredCases => by
      simp [Validation.selectionSetImplementationValidInScope]
  | boolCase :: restCases, hfilteredCases => by
      have hrest :
          Validation.selectionSetImplementationValidInScope schema
            operation.variableDefinitions operation.rootType
            (List.flatten (restCases.map (fun boolCase =>
              match normalizeSelectionSet schema operation.rootType
                  (filterSelectionSetBoolCase boolCase
                    operation.selectionSet) with
              | [] => []
              | selection :: rest =>
                  wrapWithBoolCase boolCase (selection :: rest)))) :=
        completeNormalizeBranches_implementationValidInScope schema operation
          hschema hfeasibleAll hrootObject hready himplementation hmerge restCases
          (by
            intro candidate hcandidate
            exact hfilteredCases candidate (by simp [hcandidate]))
      cases hnormalized :
          normalizeSelectionSet schema operation.rootType
            (filterSelectionSetBoolCase boolCase
              operation.selectionSet) with
      | nil =>
          simpa [hnormalized] using hrest
      | cons selection normalizedRest =>
          have hbranchValid :
              GroundTypeNormalization.NormalizedSelectionSetValid schema
                operation.variableDefinitions operation.rootType
                (selection :: normalizedRest) := by
            simpa [hnormalized] using
              normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
                schema operation.variableDefinitions hschema
                hfeasibleAll operation.rootType operation.selectionSet boolCase
                hrootObject hready
                (hfilteredCases boolCase (by simp)) hmerge
          have hwrapped :
              Validation.selectionSetImplementationValidInScope schema
                operation.variableDefinitions operation.rootType
                (wrapWithBoolCase boolCase
                  (selection :: normalizedRest)) :=
            wrapWithBoolCase_selectionSetImplementationValidInScope schema
              operation.variableDefinitions operation.rootType boolCase
              (selection :: normalizedRest) hbranchValid.implementationValid
          simpa [hnormalized] using
            GroundTypeNormalization.selectionSetImplementationValidInScope_append
              hwrapped hrest



end CompleteNormalization

end NormalForm

end GraphQL
