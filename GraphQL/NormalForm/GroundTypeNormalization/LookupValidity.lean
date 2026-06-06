import GraphQL.NormalForm.GroundTypeNormalization.ValidationTransport

/-!
Lookup-validity facts for ground-type normalization proofs.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

mutual
  def selectionLookupValid (schema : Schema)
      (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives _selectionSet =>
        ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
    | .inlineFragment none _directives selectionSet =>
        selectionSetLookupValid schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetLookupValid schema typeCondition selectionSet

  def selectionSetLookupValid (schema : Schema)
      (parentType : Name) (selectionSet : List Selection) : Prop :=
    ∀ selection, selection ∈ selectionSet ->
      selectionLookupValid schema parentType selection
end

theorem selectionSetLookupValid_nil (schema : Schema)
    (parentType : Name) :
    selectionSetLookupValid schema parentType [] := by
  simp [selectionSetLookupValid]

theorem selectionSetLookupValid_append
    {schema : Schema} {parentType : Name}
    {left right : List Selection} :
    selectionSetLookupValid schema parentType left ->
      selectionSetLookupValid schema parentType right ->
        selectionSetLookupValid schema parentType (left ++ right) := by
  intro hleft hright
  unfold selectionSetLookupValid at hleft hright ⊢
  intro selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem selectionSetLookupValid_append_left
    {schema : Schema} {parentType : Name}
    {left right : List Selection} :
    selectionSetLookupValid schema parentType (left ++ right) ->
      selectionSetLookupValid schema parentType left := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid ⊢
  intro selection hselection
  exact hvalid selection (List.mem_append.mpr (Or.inl hselection))

theorem selectionSetLookupValid_append_right
    {schema : Schema} {parentType : Name}
    {left right : List Selection} :
    selectionSetLookupValid schema parentType (left ++ right) ->
      selectionSetLookupValid schema parentType right := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid ⊢
  intro selection hselection
  exact hvalid selection (List.mem_append.mpr (Or.inr hselection))

theorem selectionSetLookupValid_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection} :
    selectionSetLookupValid schema parentType (selection :: selectionSet) ->
      selectionSetLookupValid schema parentType selectionSet := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid ⊢
  intro candidate hcandidate
  exact hvalid candidate (List.mem_cons_of_mem selection hcandidate)

theorem selectionSetLookupValid_head
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection} :
    selectionSetLookupValid schema parentType (selection :: selectionSet) ->
      selectionLookupValid schema parentType selection := by
  intro hvalid
  unfold selectionSetLookupValid at hvalid
  exact hvalid selection (by simp)

theorem fieldMerge_collectFields_mem_outputType
    (schema : Schema) :
    ∀ parentType selectionSet scopedField,
      SchemaWellFormedness.schemaWellFormed schema ->
        selectionSetLookupValid schema parentType selectionSet ->
          scopedField ∈ FieldMerge.collectFields schema parentType
            selectionSet ->
            scopedField.outputType.isOutputType schema
  | _parentType, [], _scopedField, _hschema, _hvalid, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | parentType, selection :: rest, scopedField, hschema, hvalid, hfield => by
      have htailValid :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hvalid
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              exact fieldMerge_collectFields_mem_outputType schema parentType
                rest scopedField hschema htailValid hfield
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases hfield with hhead | htail
              · subst scopedField
                exact
                  SchemaWellFormedness.schemaWellFormed_lookupField_outputType
                    hschema hlookup
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType rest scopedField hschema htailValid htail
      | inlineFragment typeCondition directives selectionSet =>
          have hheadValid :
              selectionLookupValid schema parentType
                (Selection.inlineFragment typeCondition directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalid
          cases typeCondition with
          | none =>
              have hselectionValid :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hheadValid
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType selectionSet scopedField hschema
                  hselectionValid hselection
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType rest scopedField hschema htailValid hrest
          | some typeCondition =>
              have hselectionValid :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadValid
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · exact fieldMerge_collectFields_mem_outputType schema
                  typeCondition selectionSet scopedField hschema
                  hselectionValid hselection
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType rest scopedField hschema htailValid hrest

def scopedFieldSameSelection
    (left right : FieldMerge.ScopedField) : Prop :=
  left.responseName = right.responseName
    ∧ left.fieldName = right.fieldName
    ∧ left.arguments = right.arguments
    ∧ left.selectionSet = right.selectionSet

theorem scopedFieldSameSelection_refl
    (field : FieldMerge.ScopedField) :
    scopedFieldSameSelection field field := by
  simp [scopedFieldSameSelection]

theorem possibleObjectParent_eq_or_abstract_not_object
    (schema : Schema) {objectParent abstractParent : Name} :
    objectParent ∈ schema.getPossibleTypes abstractParent ->
      abstractParent = objectParent ∨ ¬ schema.objectType abstractParent := by
  intro hpossible
  by_cases habstractObject : schema.objectType abstractParent
  · have hinclude :
        schema.typeIncludesObjectBool abstractParent objectParent = true :=
      List.contains_iff_mem.mpr hpossible
    have heq :
        objectParent = abstractParent :=
      object_typeIncludesObjectBool_eq_self schema habstractObject hinclude
    exact Or.inl heq.symm
  · exact Or.inr habstractObject

theorem fieldsForNameCanMerge_of_sameSelection_bridge
    (schema : Schema)
    (objectLeft objectRight abstractLeft abstractRight :
      FieldMerge.ScopedField) :
    scopedFieldSameSelection objectLeft abstractLeft ->
    scopedFieldSameSelection objectRight abstractRight ->
    FieldMerge.sameResponseShape schema objectLeft.outputType
      abstractLeft.outputType ->
    FieldMerge.sameResponseShape schema objectRight.outputType
      abstractRight.outputType ->
    (abstractLeft.parentType = objectLeft.parentType
      ∨ ¬ schema.objectType abstractLeft.parentType) ->
    (abstractRight.parentType = objectRight.parentType
      ∨ ¬ schema.objectType abstractRight.parentType) ->
    objectLeft.responseName = objectRight.responseName ->
    FieldMerge.fieldsForNameCanMerge schema abstractLeft abstractRight ->
      FieldMerge.fieldsForNameCanMerge schema objectLeft objectRight := by
  intro hleftSame hrightSame hleftShape hrightShape hleftParent
    hrightParent hresponse habstractMerge
  rcases hleftSame with
    ⟨hleftResponse, hleftField, hleftArguments, hleftSelectionSet⟩
  rcases hrightSame with
    ⟨hrightResponse, hrightField, hrightArguments, hrightSelectionSet⟩
  refine FieldMerge.FieldsForNameCanMerge.intro objectLeft objectRight ?_ ?_ ?_
  · have habstractShape :=
      FieldMerge.fieldsForNameCanMerge_sameResponseShape habstractMerge
    exact
      FieldMerge.sameResponseShape_trans schema objectLeft.outputType
        abstractLeft.outputType objectRight.outputType hleftShape
        (FieldMerge.sameResponseShape_trans schema abstractLeft.outputType
          abstractRight.outputType objectRight.outputType habstractShape
          (FieldMerge.sameResponseShape_symm schema objectRight.outputType
            abstractRight.outputType hrightShape))
  · intro hobjectParentCondition
    have habstractParentCondition :
        abstractLeft.parentType = abstractRight.parentType
          ∨ ¬ schema.objectType abstractLeft.parentType
          ∨ ¬ schema.objectType abstractRight.parentType := by
      rcases hleftParent with hleftParentEq | hleftNotObject
      · rcases hrightParent with hrightParentEq | hrightNotObject
        · rcases hobjectParentCondition with hobjectParentEq
            | hobjectNotObject
          · exact Or.inl
              (hleftParentEq.trans
                (hobjectParentEq.trans hrightParentEq.symm))
          · rcases hobjectNotObject with hobjectLeftNotObject
              | hobjectRightNotObject
            · exact Or.inr (Or.inl
                (by
                  intro habstractObject
                  exact hobjectLeftNotObject
                    (by simpa [hleftParentEq] using habstractObject)))
            · exact Or.inr (Or.inr
                (by
                  intro habstractObject
                  exact hobjectRightNotObject
                    (by simpa [hrightParentEq] using habstractObject)))
        · exact Or.inr (Or.inr hrightNotObject)
      · exact Or.inr (Or.inl hleftNotObject)
    rcases
      FieldMerge.fieldsForNameCanMerge_identity habstractMerge
        habstractParentCondition with
      ⟨habstractField, habstractArguments⟩
    have hfield :
        objectLeft.fieldName = objectRight.fieldName :=
      hleftField.trans (habstractField.trans hrightField.symm)
    have harguments :
        Argument.argumentsEquivalent objectLeft.arguments
          objectRight.arguments := by
      simpa [hleftArguments, hrightArguments] using habstractArguments
    exact ⟨hfield, harguments⟩
  · intro objectType
    have hsubfields :=
      FieldMerge.fieldsForNameCanMerge_subfields habstractMerge objectType
    simpa [hleftSelectionSet, hrightSelectionSet] using hsubfields

theorem fieldMerge_collectFields_objectParent_possibleParent
    (schema : Schema) :
    ∀ objectParent abstractParent selectionSet objectField,
      SchemaWellFormedness.schemaWellFormed schema ->
        schema.objectType objectParent ->
          objectParent ∈ schema.getPossibleTypes abstractParent ->
            selectionSetLookupValid schema objectParent selectionSet ->
              selectionSetLookupValid schema abstractParent selectionSet ->
                objectField ∈ FieldMerge.collectFields schema objectParent
                  selectionSet ->
                  ∃ abstractField,
                    abstractField ∈ FieldMerge.collectFields schema
                      abstractParent selectionSet
                      ∧ scopedFieldSameSelection objectField abstractField
                      ∧ FieldMerge.sameResponseShape schema
                        objectField.outputType abstractField.outputType
                      ∧ (abstractField.parentType = objectField.parentType
                        ∨ ¬ schema.objectType abstractField.parentType)
  | _objectParent, _abstractParent, [], _objectField, _hschema, _hobject,
      _hpossible, _hvalidObject, _hvalidAbstract, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | objectParent, abstractParent, selection :: rest, objectField, hschema,
      hobject, hpossible, hvalidObject, hvalidAbstract, hfield => by
      have htailObject :
          selectionSetLookupValid schema objectParent rest :=
        selectionSetLookupValid_tail hvalidObject
      have htailAbstract :
          selectionSetLookupValid schema abstractParent rest :=
        selectionSetLookupValid_tail hvalidAbstract
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hheadObject :
              selectionLookupValid schema objectParent
                (Selection.field responseName fieldName arguments directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidObject
          have hheadAbstract :
              selectionLookupValid schema abstractParent
                (Selection.field responseName fieldName arguments directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidAbstract
          rcases (by
            simpa [selectionLookupValid] using hheadAbstract) with
            ⟨abstractDefinition, habstractLookup⟩
          cases hlookup : schema.lookupField objectParent fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases
                fieldMerge_collectFields_objectParent_possibleParent schema
                  objectParent abstractParent rest objectField hschema hobject
                  hpossible htailObject htailAbstract hfield with
                ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
              exact ⟨abstractField,
                fieldMerge_collectFields_tail_mem schema abstractParent
                  (Selection.field responseName fieldName arguments directives
                    selectionSet)
                  rest abstractField habstractMem,
                hsame, hshape, hparent⟩
          | some objectDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases hfield with hhead | htail
              · subst objectField
                let abstractField : FieldMerge.ScopedField :=
                  {
                    parentType := abstractParent,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    outputType := abstractDefinition.outputType,
                    selectionSet := selectionSet
                  }
                refine ⟨abstractField, ?_, ?_, ?_, ?_⟩
                · simp [abstractField, FieldMerge.collectFields,
                    habstractLookup]
                · simp [scopedFieldSameSelection, abstractField]
                · exact
                    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_sameResponseShape
                      hschema hpossible habstractLookup hlookup
                · rcases
                    possibleObjectParent_eq_or_abstract_not_object schema
                      hpossible with
                    heq | hnotObject
                  · exact Or.inl (by simp [abstractField, heq])
                  · exact Or.inr (by simpa [abstractField] using hnotObject)
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent rest objectField hschema
                    hobject hpossible htailObject htailAbstract htail with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField,
                  fieldMerge_collectFields_tail_mem schema abstractParent
                    (Selection.field responseName fieldName arguments
                      directives selectionSet)
                    rest abstractField habstractMem,
                  hsame, hshape, hparent⟩
      | inlineFragment typeCondition directives selectionSet =>
          have hheadObject :
              selectionLookupValid schema objectParent
                (Selection.inlineFragment typeCondition directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidObject
          have hheadAbstract :
              selectionLookupValid schema abstractParent
                (Selection.inlineFragment typeCondition directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidAbstract
          cases typeCondition with
          | none =>
              have hselectionObject :
                  selectionSetLookupValid schema objectParent selectionSet := by
                simpa [selectionLookupValid] using hheadObject
              have hselectionAbstract :
                  selectionSetLookupValid schema abstractParent selectionSet := by
                simpa [selectionLookupValid] using hheadAbstract
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent selectionSet objectField
                    hschema hobject hpossible hselectionObject
                    hselectionAbstract hselection with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField, by
                  simp [FieldMerge.collectFields, habstractMem],
                  hsame, hshape, hparent⟩
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent rest objectField hschema
                    hobject hpossible htailObject htailAbstract hrest with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField,
                  fieldMerge_collectFields_tail_mem schema abstractParent
                    (Selection.inlineFragment none directives selectionSet)
                    rest abstractField habstractMem,
                  hsame, hshape, hparent⟩
          | some typeCondition =>
              have hselectionLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadObject
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · refine ⟨objectField, ?_, ?_, ?_, ?_⟩
                · simp [FieldMerge.collectFields, hselection]
                · exact scopedFieldSameSelection_refl objectField
                · exact
                    FieldMerge.sameResponseShape_refl schema
                      objectField.outputType
                      (fieldMerge_collectFields_mem_outputType schema
                        typeCondition selectionSet objectField hschema
                        hselectionLookup hselection)
                · exact Or.inl rfl
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent rest objectField hschema
                    hobject hpossible htailObject htailAbstract hrest with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField,
                  fieldMerge_collectFields_tail_mem schema abstractParent
                    (Selection.inlineFragment (some typeCondition) directives
                      selectionSet)
                    rest abstractField habstractMem,
                  hsame, hshape, hparent⟩

theorem fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
    (schema : Schema) (parentType typeCondition : Name)
    (selectionSet rest : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.objectType parentType ->
    schema.typesOverlapBool parentType typeCondition = true ->
    selectionSetLookupValid schema parentType selectionSet ->
    selectionSetLookupValid schema typeCondition selectionSet ->
    selectionSetLookupValid schema parentType rest ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.inlineFragment (some typeCondition) [] selectionSet
        :: rest) ->
      FieldMerge.fieldsInSetCanMerge schema parentType
        (selectionSet ++ rest) := by
  intro hschema hobject hoverlap hselectionParentLookup
    hselectionTypeLookup hrestLookup hmerge
  have hpossible :
      parentType ∈ schema.getPossibleTypes typeCondition :=
    List.contains_iff_mem.mp
      (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
        hoverlap)
  have horiginalOf :
      ∀ objectField,
        objectField ∈ FieldMerge.collectFields schema parentType
          (selectionSet ++ rest) ->
          ∃ abstractField,
            abstractField ∈ FieldMerge.collectFields schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest)
              ∧ scopedFieldSameSelection objectField abstractField
              ∧ FieldMerge.sameResponseShape schema objectField.outputType
                abstractField.outputType
              ∧ (abstractField.parentType = objectField.parentType
                ∨ ¬ schema.objectType abstractField.parentType) := by
    intro objectField hfield
    rw [FieldMerge.collectFields_append] at hfield
    rcases List.mem_append.mp hfield with hselection | hrest
    · rcases
        fieldMerge_collectFields_objectParent_possibleParent schema
          parentType typeCondition selectionSet objectField hschema hobject
          hpossible hselectionParentLookup hselectionTypeLookup hselection with
        ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
      have habstractOriginal :
          abstractField ∈ FieldMerge.collectFields schema parentType
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
        simp [FieldMerge.collectFields, habstractMem]
      exact ⟨abstractField, habstractOriginal, hsame, hshape, hparent⟩
    · have hshape :
          FieldMerge.sameResponseShape schema objectField.outputType
            objectField.outputType :=
        FieldMerge.sameResponseShape_refl schema objectField.outputType
          (fieldMerge_collectFields_mem_outputType schema parentType rest
            objectField hschema hrestLookup hrest)
      exact ⟨objectField,
        fieldMerge_collectFields_tail_mem schema parentType
          (Selection.inlineFragment (some typeCondition) [] selectionSet)
          rest objectField hrest,
        scopedFieldSameSelection_refl objectField, hshape, Or.inl rfl⟩
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (selectionSet ++ rest) ?_
  dsimp
  intro left hleft right hright hresponse
  rcases horiginalOf left hleft with
    ⟨abstractLeft, habstractLeftMem, hleftSame, hleftShape,
      hleftParent⟩
  rcases horiginalOf right hright with
    ⟨abstractRight, habstractRightMem, hrightSame, hrightShape,
      hrightParent⟩
  have habstractResponse :
      abstractLeft.responseName = abstractRight.responseName := by
    exact hleftSame.1.symm.trans (hresponse.trans hrightSame.1)
  have habstractMerge :
      FieldMerge.fieldsForNameCanMerge schema abstractLeft abstractRight :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge habstractLeftMem
      habstractRightMem habstractResponse
  exact fieldsForNameCanMerge_of_sameSelection_bridge schema left right
    abstractLeft abstractRight hleftSame hrightSame hleftShape hrightShape
    hleftParent hrightParent hresponse habstractMerge

theorem selectionSetLookupValid_withoutFieldsWithResponseName_core
    (schema : Schema) (responseName : Name) :
    ∀ parentType selectionSet,
      selectionSetLookupValid schema parentType selectionSet ->
        selectionSetLookupValid schema parentType
          (withoutFieldsWithResponseName schema responseName selectionSet)
  | _parentType, [], _hvalid => by
      simp [withoutFieldsWithResponseName, selectionSetLookupValid]
  | parentType, selection :: rest, hvalid => by
      have hhead :
          selectionLookupValid schema parentType selection := by
        unfold selectionSetLookupValid at hvalid
        exact hvalid selection (by simp)
      have htail :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hvalid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            simpa [selectionSetLookupValid] using
              selectionSetLookupValid_withoutFieldsWithResponseName_core
                schema responseName parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse,
              selectionSetLookupValid]
            constructor
            · exact hhead
            · simpa [selectionSetLookupValid] using
                selectionSetLookupValid_withoutFieldsWithResponseName_core
                  schema responseName parentType rest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [withoutFieldsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName_core
                    schema responseName parentType selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName_core
                    schema responseName parentType rest htail
          | some typeCondition =>
              simp [withoutFieldsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName_core
                    schema responseName typeCondition selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName_core
                    schema responseName parentType rest htail

mutual
  theorem selectionLookupValid_of_selectionValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name} :
      ∀ selection,
        Validation.selectionValid schema variableDefinitions parentType
          selection ->
          selectionLookupValid schema parentType selection
    | .field _responseName fieldName _arguments _directives _selectionSet,
        hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
        simpa [selectionLookupValid] using ⟨fieldDefinition, hlookup⟩
    | .inlineFragment none _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_none_selectionSetValid
              hvalid)
    | .inlineFragment (some typeCondition) _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_some_selectionSetValid
              hvalid)

  theorem selectionSetLookupValid_of_selectionSetValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name} :
      ∀ selectionSet,
        Validation.selectionSetValid schema variableDefinitions parentType
          selectionSet ->
          selectionSetLookupValid schema parentType selectionSet
    | [], _hvalid => by
        exact selectionSetLookupValid_nil schema parentType
    | selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetLookupValid]
        constructor
        · exact selectionLookupValid_of_selectionValid selection hhead
        · simpa [selectionSetLookupValid] using
            selectionSetLookupValid_of_selectionSetValid rest htail
end

mutual
  theorem selectionLookupValid_of_selectionValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
        objectType ∈ schema.getPossibleTypes parentType ->
          ∀ selection,
            Validation.selectionValid schema variableDefinitions parentType
              selection ->
              selectionLookupValid schema objectType selection
    | hschema, hpossible,
      .field _responseName fieldName _arguments _directives _selectionSet,
      hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
        simp [selectionLookupValid]
        exact
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
            hschema hpossible hlookup
    | hschema, hpossible,
      .inlineFragment none _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid_possibleObject
            schema variableDefinitions parentType objectType hschema
            hpossible selectionSet
            (Validation.selectionValid_inlineFragment_none_selectionSetValid
              hvalid)
    | _hschema, _hpossible,
      .inlineFragment (some _typeCondition) _directives selectionSet,
      hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_some_selectionSetValid
              hvalid)

theorem selectionSetLookupValid_of_selectionSetValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
        objectType ∈ schema.getPossibleTypes parentType ->
          ∀ selectionSet,
            Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet ->
              selectionSetLookupValid schema objectType selectionSet
    | _hschema, _hpossible, [], _hvalid => by
        exact selectionSetLookupValid_nil schema objectType
    | hschema, hpossible, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetLookupValid]
        constructor
        · exact selectionLookupValid_of_selectionValid_possibleObject schema
            variableDefinitions parentType objectType hschema hpossible
            selection hhead
        · simpa [selectionSetLookupValid] using
            selectionSetLookupValid_of_selectionSetValid_possibleObject
              schema variableDefinitions parentType objectType hschema
              hpossible rest htail
end



end GroundTypeNormalization

end NormalForm

end GraphQL
