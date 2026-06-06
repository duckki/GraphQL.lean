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

theorem selectionSetDirectiveFree_append_left
    {left right : List Selection} :
    selectionSetDirectiveFree (left ++ right) ->
      selectionSetDirectiveFree left := by
  intro hfree
  induction left with
  | nil =>
      exact selectionSetDirectiveFree_nil
  | cons selection rest ih =>
      exact ⟨hfree.1, ih hfree.2⟩

theorem selectionSetDirectiveFree_append_right
    {left right : List Selection} :
    selectionSetDirectiveFree (left ++ right) ->
      selectionSetDirectiveFree right := by
  intro hfree
  induction left with
  | nil =>
      simpa using hfree
  | cons selection rest ih =>
      exact ih hfree.2

theorem objectTypeNameBool_eq_true_of_objectType_base
    (schema : Schema) {typeName : Name} :
    schema.objectType typeName ->
      objectTypeNameBool schema typeName = true := by
  intro hobject
  unfold Schema.objectType at hobject
  rcases hobject with ⟨objectType, hlookup⟩
  simp [objectTypeNameBool, hlookup]

theorem object_typeIncludesObjectBool_eq_self
    (schema : Schema) {typeName objectName : Name} :
    schema.objectType typeName ->
      schema.typeIncludesObjectBool typeName objectName = true ->
        objectName = typeName := by
  intro hobject hinclude
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType] using hmatch
  simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup,
    hname] at hinclude
  exact hinclude

theorem object_typesOverlapBool_eq
    (schema : Schema) {left right : Name} :
    schema.objectType left ->
      schema.objectType right ->
        schema.typesOverlapBool left right = true ->
          right = left := by
  intro hleft hright hoverlap
  rcases hleft with ⟨leftObject, hleftLookup⟩
  have hleftName : leftObject.name = left := by
    have hmatch := List.find?_some hleftLookup
    simpa [Schema.lookupType] using hmatch
  simp [Schema.typesOverlapBool, Schema.getPossibleTypes, hleftLookup,
    hleftName] at hoverlap
  exact (object_typeIncludesObjectBool_eq_self schema
    (typeName := right) (objectName := left) hright hoverlap).symm

theorem object_typesOverlapBool_self
    (schema : Schema) {typeName : Name} :
    schema.objectType typeName ->
      schema.typesOverlapBool typeName typeName = true := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType] using hmatch
  simp [Schema.typesOverlapBool, Schema.typeIncludesObjectBool,
    Schema.getPossibleTypes, hlookup, hname]

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

theorem selectionSetDirectiveFree_fieldHead_merged
    (schema : Schema) (parentType responseName : Name)
    (fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection) :
    selectionSetDirectiveFree
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
      selectionSetDirectiveFree
        (subselections
          ++ mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName
              rest)) := by
  intro hfree
  apply selectionSetDirectiveFree_append
  · exact (selectionSetDirectiveFree_head hfree).2
  · apply selectionSetDirectiveFree_mergeSelectionSets
    exact validFieldsWithResponseName_directiveFree schema parentType
      responseName rest (selectionSetDirectiveFree_tail hfree)

theorem validFieldsWithResponseName_mem_field (schema : Schema)
    (parentType responseName : Name) :
    ∀ selectionSet selection,
      selection ∈ validFieldsWithResponseName schema parentType responseName
        selectionSet ->
        ∃ fieldName arguments directives subselections,
          selection =
            Selection.field responseName fieldName arguments directives
              subselections
  | [], selection, hselection => by
      simp [validFieldsWithResponseName] at hselection
  | source :: rest, selection, hselection => by
      cases source with
      | field fieldResponseName fieldName arguments directives subselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [validFieldsWithResponseName, hname] at hselection
            rcases hselection with hselection | hselection
            · subst selection
              have hresponseName : fieldResponseName = responseName :=
                beq_iff_eq.mp hname
              subst fieldResponseName
              exact ⟨fieldName, arguments, directives, subselections, rfl⟩
            · exact validFieldsWithResponseName_mem_field schema parentType
                responseName rest selection hselection
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [validFieldsWithResponseName, hfalse] at hselection
            exact validFieldsWithResponseName_mem_field schema parentType
              responseName rest selection hselection
      | inlineFragment typeCondition directives subselections =>
          cases typeCondition with
          | none =>
              simp [validFieldsWithResponseName] at hselection
              rcases hselection with hselection | hselection
              · exact validFieldsWithResponseName_mem_field schema parentType
                  responseName subselections selection hselection
              · exact validFieldsWithResponseName_mem_field schema parentType
                  responseName rest selection hselection
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · simp [validFieldsWithResponseName, hoverlap] at hselection
                rcases hselection with hselection | hselection
                · exact validFieldsWithResponseName_mem_field schema parentType
                    responseName subselections selection hselection
                · exact validFieldsWithResponseName_mem_field schema parentType
                    responseName rest selection hselection
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [validFieldsWithResponseName, hfalse] at hselection
                exact validFieldsWithResponseName_mem_field schema parentType
                  responseName rest selection hselection

theorem validFieldsWithResponseName_field_mem_collectFields_scoped
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (filterParent collectParent responseName : Name) :
    ∀ selectionSet fieldName arguments directives subselections,
      (schema.objectType collectParent ->
        schema.typesOverlapBool filterParent collectParent = true) ->
      Validation.selectionSetValid schema variableDefinitions collectParent
        selectionSet ->
      Selection.field responseName fieldName arguments directives subselections
        ∈ validFieldsWithResponseName schema filterParent responseName
          selectionSet ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema collectParent selectionSet
            ∧ scopedField.responseName = responseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
            ∧ (schema.objectType scopedField.parentType ->
              schema.typesOverlapBool filterParent scopedField.parentType = true)
  | [], fieldName, arguments, directives, subselections, _hoverlapScope,
      _hvalid, hfield => by
      simp [validFieldsWithResponseName] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hoverlapScope, hvalid, hfield => by
      have hhead :
          Validation.selectionValid schema variableDefinitions collectParent
            selection := by
        simp [Validation.selectionSetValid] at hvalid
        exact hvalid.1
      have htail :
          Validation.selectionSetValid schema variableDefinitions collectParent
            rest :=
        Validation.selectionSetValid_tail hvalid
      cases selection with
      | field fieldResponseName sourceFieldName sourceArguments
          sourceDirectives sourceSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [validFieldsWithResponseName, hname] at hfield
            rcases hfield with hfield | hfield
            · rcases hfield with
                ⟨hresponseEq, hfieldEq, hargumentsEq, hdirectivesEq,
                  hsubselectionsEq⟩
              subst fieldResponseName
              subst sourceFieldName
              subst sourceArguments
              subst sourceDirectives
              subst sourceSubselections
              rcases Validation.selectionValid_field_lookup hhead with
                ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
              refine ⟨{
                parentType := collectParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                outputType := fieldDefinition.outputType,
                selectionSet := subselections
              }, ?_, rfl, rfl, rfl, rfl, ?_⟩
              simp [FieldMerge.collectFields, hlookup]
              exact hoverlapScope
            · rcases
                validFieldsWithResponseName_field_mem_collectFields_scoped
                  schema variableDefinitions filterParent collectParent
                  responseName rest fieldName arguments directives
                  subselections hoverlapScope htail hfield with
                ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
              refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                hselectionSet, hscopedOverlap⟩
              rcases Validation.selectionValid_field_lookup hhead with
                ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [validFieldsWithResponseName, hfalse] at hfield
            rcases
              validFieldsWithResponseName_field_mem_collectFields_scoped
                schema variableDefinitions filterParent collectParent
                responseName rest fieldName arguments directives
                subselections hoverlapScope htail hfield with
              ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                hselectionSet, hscopedOverlap⟩
            refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
              hselectionSet, hscopedOverlap⟩
            rcases Validation.selectionValid_field_lookup hhead with
              ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition _fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    collectParent selectionSet :=
                Validation.selectionValid_inlineFragment_none_selectionSetValid
                  hhead
              simp [validFieldsWithResponseName] at hfield
              rcases hfield with hfield | hfield
              · rcases
                  validFieldsWithResponseName_field_mem_collectFields_scoped
                    schema variableDefinitions filterParent collectParent
                    responseName selectionSet fieldName arguments directives
                    subselections hoverlapScope hselectionSetValid hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
              · rcases
                  validFieldsWithResponseName_field_mem_collectFields_scoped
                    schema variableDefinitions filterParent collectParent
                    responseName rest fieldName arguments directives
                    subselections hoverlapScope htail hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    typeCondition selectionSet :=
                Validation.selectionValid_inlineFragment_some_selectionSetValid
                  hhead
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [validFieldsWithResponseName, hoverlap] at hfield
                rcases hfield with hfield | hfield
                · rcases
                    validFieldsWithResponseName_field_mem_collectFields_scoped
                      schema variableDefinitions filterParent typeCondition
                      responseName selectionSet fieldName arguments directives
                      subselections (fun _hobject => hoverlap)
                      hselectionSetValid hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                      hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases
                    validFieldsWithResponseName_field_mem_collectFields_scoped
                      schema variableDefinitions filterParent collectParent
                      responseName rest fieldName arguments directives
                      subselections hoverlapScope htail hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                      hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool filterParent typeCondition
                  · rfl
                  · contradiction
                simp [validFieldsWithResponseName, hfalse] at hfield
                rcases
                  validFieldsWithResponseName_field_mem_collectFields_scoped
                    schema variableDefinitions filterParent collectParent
                    responseName rest fieldName arguments directives
                    subselections hoverlapScope htail hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]

theorem selectionSetValid_mergeSelectionSets_of_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} :
    ∀ selections,
      (∀ selection, selection ∈ selections ->
        Validation.selectionSetValid schema variableDefinitions parentType
          selection.subselections) ->
        Validation.selectionSetValid schema variableDefinitions parentType
          (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, Validation.selectionSetValid]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply Validation.selectionSetValid_append
      · exact hvalid selection (by simp)
      · exact selectionSetValid_mergeSelectionSets_of_subselections rest
          (by
            intro candidate hcandidate
            exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetValid_mergeSelectionSets_of_field_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName : Name}
    (selections : List Selection) :
    (∀ selection, selection ∈ selections ->
      ∃ fieldName arguments directives subselections,
        selection =
          Selection.field responseName fieldName arguments directives
            subselections) ->
    (∀ fieldName arguments directives subselections,
      Selection.field responseName fieldName arguments directives
          subselections ∈ selections ->
        Validation.selectionSetValid schema variableDefinitions parentType
          subselections) ->
      Validation.selectionSetValid schema variableDefinitions parentType
        (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetValid_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem selectionSetValid_mergeSelectionSets_validFieldsWithResponseName
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName childType : Name}
    (selectionSet : List Selection) :
    (∀ fieldName arguments directives subselections,
      Selection.field responseName fieldName arguments directives subselections
        ∈ validFieldsWithResponseName schema parentType responseName
          selectionSet ->
        Validation.selectionSetValid schema variableDefinitions childType
          subselections) ->
      Validation.selectionSetValid schema variableDefinitions childType
        (mergeSelectionSets
          (validFieldsWithResponseName schema parentType responseName
            selectionSet)) := by
  intro hfields
  apply selectionSetValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact validFieldsWithResponseName_mem_field schema parentType responseName
      selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem fieldMerge_collectFields_mergeSelectionSets_mem
    (schema : Schema) (parentType : Name) (selections : List Selection)
    (scopedField : FieldMerge.ScopedField) :
    scopedField ∈ FieldMerge.collectFields schema parentType
      (mergeSelectionSets selections) ->
      ∃ selection,
        selection ∈ selections
          ∧ scopedField ∈ FieldMerge.collectFields schema parentType
            selection.subselections := by
  induction selections with
  | nil =>
      intro hfield
      simp [mergeSelectionSets, FieldMerge.collectFields] at hfield
  | cons selection rest ih =>
      intro hfield
      simp [mergeSelectionSets] at hfield
      rw [FieldMerge.collectFields_append] at hfield
      rcases List.mem_append.mp hfield with hhead | hrest
      · exact ⟨selection, by simp, hhead⟩
      · rcases ih hrest with
          ⟨sourceSelection, hsourceSelection, hsourceField⟩
        exact ⟨sourceSelection, by simp [hsourceSelection],
          hsourceField⟩

theorem fieldsInSetCanMerge_mergeSelectionSets_of_pairwise
    (schema : Schema) (parentType : Name) (selections : List Selection) :
    (∀ leftSelection, leftSelection ∈ selections ->
      ∀ rightSelection, rightSelection ∈ selections ->
        FieldMerge.fieldsInSetCanMerge schema parentType
          (leftSelection.subselections ++ rightSelection.subselections)) ->
      FieldMerge.fieldsInSetCanMerge schema parentType
        (mergeSelectionSets selections) := by
  intro hpairwise
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (mergeSelectionSets selections) ?_
  dsimp
  intro left hleft right hright hresponse
  rcases fieldMerge_collectFields_mergeSelectionSets_mem schema parentType
      selections left hleft with
    ⟨leftSelection, hleftSelection, hleftField⟩
  rcases fieldMerge_collectFields_mergeSelectionSets_mem schema parentType
      selections right hright with
    ⟨rightSelection, hrightSelection, hrightField⟩
  have hpair :
      FieldMerge.fieldsInSetCanMerge schema parentType
        (leftSelection.subselections ++ rightSelection.subselections) :=
    hpairwise leftSelection hleftSelection rightSelection hrightSelection
  have hleftPair :
      left ∈ FieldMerge.collectFields schema parentType
        (leftSelection.subselections ++ rightSelection.subselections) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_left
      (FieldMerge.collectFields schema parentType
        rightSelection.subselections)
      hleftField
  have hrightPair :
      right ∈ FieldMerge.collectFields schema parentType
        (leftSelection.subselections ++ rightSelection.subselections) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_right
      (FieldMerge.collectFields schema parentType leftSelection.subselections)
      hrightField
  exact FieldMerge.fieldsInSetCanMerge_pair hpair hleftPair hrightPair
    hresponse

theorem fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName objectType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    schema.objectType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
      FieldMerge.fieldsInSetCanMerge schema objectType
        (subselections
          ++ mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName
              rest)) := by
  intro hobject hvalid hmerge hlookup
  let headSelection : Selection :=
    Selection.field responseName fieldName arguments [] subselections
  let matching :=
    validFieldsWithResponseName schema parentType responseName rest
  let group := headSelection :: matching
  let headScoped : FieldMerge.ScopedField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      outputType := fieldDefinition.outputType,
      selectionSet := subselections
    }
  have htailValid :
      Validation.selectionSetValid schema variableDefinitions parentType rest :=
    Validation.selectionSetValid_tail hvalid
  have hoverlapSelf :
      schema.objectType parentType ->
        schema.typesOverlapBool parentType parentType = true := by
    intro hparentObject
    exact object_typesOverlapBool_self schema hparentObject
  have hheadMem :
      headScoped ∈ FieldMerge.collectFields schema parentType
        (headSelection :: rest) := by
    simp [headScoped, headSelection, FieldMerge.collectFields, hlookup]
  have hscopedOf :
      ∀ selection, selection ∈ group ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType
            (headSelection :: rest)
            ∧ scopedField.responseName = responseName
            ∧ scopedField.selectionSet = selection.subselections := by
    intro selection hselection
    rcases List.mem_cons.mp hselection with hhead | hmatched
    · subst selection
      exact ⟨headScoped, hheadMem, rfl, by
        simp [headScoped, headSelection, Selection.subselections]⟩
    · rcases
        validFieldsWithResponseName_mem_field schema parentType responseName
          rest selection hmatched with
        ⟨matchedFieldName, matchedArguments, matchedDirectives,
          matchedSubselections, hselectionEq⟩
      subst selection
      rcases
        validFieldsWithResponseName_field_mem_collectFields_scoped
          schema variableDefinitions parentType parentType responseName rest
          matchedFieldName matchedArguments matchedDirectives
          matchedSubselections hoverlapSelf htailValid
          hmatched with
        ⟨scopedField, hscopedRest, hresponse, _hfieldName,
          _harguments, hselectionSet, _hoverlap⟩
      have hscoped :
          scopedField ∈ FieldMerge.collectFields schema parentType
            (headSelection :: rest) := by
        simp [headSelection, FieldMerge.collectFields, hlookup,
          hscopedRest]
      exact ⟨scopedField, hscoped, hresponse, by
        simpa [Selection.subselections] using hselectionSet⟩
  have hgroupMerge :
      FieldMerge.fieldsInSetCanMerge schema objectType
        (mergeSelectionSets group) := by
    apply fieldsInSetCanMerge_mergeSelectionSets_of_pairwise
    intro leftSelection hleftSelection rightSelection hrightSelection
    rcases hscopedOf leftSelection hleftSelection with
      ⟨leftScoped, hleftScoped, hleftResponse, hleftSelectionSet⟩
    rcases hscopedOf rightSelection hrightSelection with
      ⟨rightScoped, hrightScoped, hrightResponse, hrightSelectionSet⟩
    have hresponse :
        leftScoped.responseName = rightScoped.responseName :=
      hleftResponse.trans hrightResponse.symm
    have hfieldMerge :
        FieldMerge.fieldsForNameCanMerge schema leftScoped rightScoped :=
      FieldMerge.fieldsInSetCanMerge_pair hmerge hleftScoped hrightScoped
        hresponse
    have hsubfields :=
      FieldMerge.fieldsForNameCanMerge_subfields hfieldMerge objectType
    rw [hleftSelectionSet, hrightSelectionSet] at hsubfields
    exact hsubfields
  simpa [group, headSelection, matching, mergeSelectionSets,
    Selection.subselections] using hgroupMerge

theorem validFieldsWithResponseName_matching_same_field_of_canMerge_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection) :
    schema.objectType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
      ∀ matchedFieldName matchedArguments matchedDirectives
        matchedSubselections,
        Selection.field responseName matchedFieldName matchedArguments
            matchedDirectives matchedSubselections
          ∈ validFieldsWithResponseName schema parentType responseName rest ->
          matchedFieldName = fieldName := by
  intro hobject hvalid hmerge matchedFieldName matchedArguments
    matchedDirectives matchedSubselections hmatched
  rcases Validation.selectionSetValid_field_head_lookup hvalid with
    ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
  let headScoped : FieldMerge.ScopedField := {
    parentType := parentType,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := subselections
  }
  have hheadMem :
      headScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simp [headScoped, FieldMerge.collectFields, hlookup]
  have htailValid :
      Validation.selectionSetValid schema variableDefinitions parentType rest :=
    Validation.selectionSetValid_tail hvalid
  rcases
      validFieldsWithResponseName_field_mem_collectFields_scoped schema
        variableDefinitions parentType parentType responseName rest
        matchedFieldName matchedArguments matchedDirectives
        matchedSubselections
        (fun _hobject => object_typesOverlapBool_self schema hobject)
        htailValid hmatched with
    ⟨matchedScoped, hmatchedMemRest, hmatchedResponse, hmatchedField,
      _hmatchedArguments, _hmatchedSelectionSet, hmatchedOverlap⟩
  have hmatchedMem :
      matchedScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hresponse :
      headScoped.responseName = matchedScoped.responseName := by
    simp [headScoped, hmatchedResponse]
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped matchedScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      hresponse
  have hparents :
      headScoped.parentType = matchedScoped.parentType
        ∨ ¬ schema.objectType headScoped.parentType
        ∨ ¬ schema.objectType matchedScoped.parentType := by
    by_cases hmatchedObject : schema.objectType matchedScoped.parentType
    · have hoverlap := hmatchedOverlap hmatchedObject
      have hmatchedParent :
          matchedScoped.parentType = parentType :=
        object_typesOverlapBool_eq schema hobject hmatchedObject hoverlap
      exact Or.inl (by simp [headScoped, hmatchedParent])
    · exact Or.inr (Or.inr hmatchedObject)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_identity hfieldMerge hparents
  have hheadField : headScoped.fieldName = fieldName := by
    rfl
  exact hmatchedField.symm.trans (hidentity.1.symm.trans hheadField)

theorem validFieldsWithResponseName_matching_field_shape_of_canMerge_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection) :
    schema.objectType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
      ∀ selection,
        selection ∈ validFieldsWithResponseName schema parentType responseName
          rest ->
          ∃ matchedArguments matchedDirectives matchedSubselections,
            selection =
              Selection.field responseName fieldName matchedArguments
                matchedDirectives matchedSubselections := by
  intro hobject hvalid hmerge selection hselection
  rcases validFieldsWithResponseName_mem_field schema parentType responseName
      rest selection hselection with
    ⟨matchedFieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionEq⟩
  subst selection
  have hsame :=
    validFieldsWithResponseName_matching_same_field_of_canMerge_object
      schema variableDefinitions parentType responseName fieldName arguments
      subselections rest hobject hvalid hmerge matchedFieldName
      matchedArguments matchedDirectives matchedSubselections hselection
  subst matchedFieldName
  exact ⟨matchedArguments, matchedDirectives, matchedSubselections, rfl⟩

theorem selectionSetValid_fieldHead_merged_of_matching
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName childType : Name)
    (_arguments : List Argument) (subselections rest : List Selection) :
    Validation.selectionSetValid schema variableDefinitions childType
      subselections ->
    (∀ selection,
      selection ∈ validFieldsWithResponseName schema parentType responseName
        rest ->
        ∃ matchedArguments matchedDirectives matchedSubselections,
          selection =
            Selection.field responseName fieldName matchedArguments
              matchedDirectives matchedSubselections) ->
    (∀ matchedArguments matchedDirectives matchedSubselections,
      Selection.field responseName fieldName matchedArguments matchedDirectives
          matchedSubselections
        ∈ validFieldsWithResponseName schema parentType responseName rest ->
        Validation.selectionSetValid schema variableDefinitions childType
          matchedSubselections) ->
      Validation.selectionSetValid schema variableDefinitions childType
        (subselections
          ++ mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName
              rest)) := by
  intro hhead hshape hmatching
  apply Validation.selectionSetValid_append hhead
  apply selectionSetValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    rcases hshape selection hselection with
      ⟨matchedArguments, matchedDirectives, matchedSubselections,
        hselectionShape⟩
    exact ⟨fieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionShape⟩
  · intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    have hmatchedShape :=
      hshape
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections)
        hmatched
    rcases hmatchedShape with
      ⟨shapeArguments, shapeDirectives, shapeSubselections, hshapeEq⟩
    injection hshapeEq with _hresponse hfield harguments hdirectives
      hsubselections
    subst matchedFieldName
    subst shapeArguments
    subst shapeDirectives
    subst shapeSubselections
    exact hmatching matchedArguments matchedDirectives matchedSubselections
      hmatched

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

theorem selectionSetLookupValid_withoutFieldsWithResponseName
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
              selectionSetLookupValid_withoutFieldsWithResponseName
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
                selectionSetLookupValid_withoutFieldsWithResponseName
                  schema responseName parentType rest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [withoutFieldsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName
                    schema responseName parentType selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName
                    schema responseName parentType rest htail
          | some typeCondition =>
              simp [withoutFieldsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName
                    schema responseName typeCondition selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldsWithResponseName
                    schema responseName parentType rest htail

theorem selectionSetLookupValid_field_head_lookup_none_false
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet rest : List Selection} :
    selectionSetLookupValid schema parentType
      (Selection.field responseName fieldName arguments directives selectionSet
        :: rest) ->
      schema.lookupField parentType fieldName = none ->
        False := by
  intro hvalid hnone
  have hhead :
      selectionLookupValid schema parentType
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    unfold selectionSetLookupValid at hvalid
    exact hvalid _ (by simp)
  simp [selectionLookupValid] at hhead
  rcases hhead with ⟨fieldDefinition, hlookup⟩
  rw [hnone] at hlookup
  contradiction

theorem selectionSetLookupValid_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name} :
    ∀ selections,
      (∀ selection, selection ∈ selections ->
        selectionSetLookupValid schema parentType selection.subselections) ->
        selectionSetLookupValid schema parentType
          (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, selectionSetLookupValid]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetLookupValid_append
      · exact hvalid selection (by simp)
      · exact selectionSetLookupValid_mergeSelectionSets_of_subselections rest
          (by
            intro candidate hcandidate
            exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetLookupValid_mergeSelectionSets_of_field_subselections
    {schema : Schema} {parentType responseName : Name}
    (selections : List Selection) :
    (∀ selection, selection ∈ selections ->
      ∃ fieldName arguments directives subselections,
        selection =
          Selection.field responseName fieldName arguments directives
            subselections) ->
    (∀ fieldName arguments directives subselections,
      Selection.field responseName fieldName arguments directives
          subselections ∈ selections ->
        selectionSetLookupValid schema parentType subselections) ->
      selectionSetLookupValid schema parentType (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetLookupValid_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem selectionSetLookupValid_mergeSelectionSets_validFieldsWithResponseName
    {schema : Schema} {parentType responseName childType : Name}
    (selectionSet : List Selection) :
    (∀ fieldName arguments directives subselections,
      Selection.field responseName fieldName arguments directives subselections
        ∈ validFieldsWithResponseName schema parentType responseName
          selectionSet ->
        selectionSetLookupValid schema childType subselections) ->
      selectionSetLookupValid schema childType
        (mergeSelectionSets
          (validFieldsWithResponseName schema parentType responseName
            selectionSet)) := by
  intro hfields
  apply selectionSetLookupValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact validFieldsWithResponseName_mem_field schema parentType responseName
      selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem selectionSetLookupValid_fieldHead_merged_of_matching
    (schema : Schema)
    (parentType responseName fieldName childType : Name)
    (_arguments : List Argument) (subselections rest : List Selection) :
    selectionSetLookupValid schema childType subselections ->
    (∀ selection,
      selection ∈ validFieldsWithResponseName schema parentType responseName
        rest ->
        ∃ matchedArguments matchedDirectives matchedSubselections,
          selection =
            Selection.field responseName fieldName matchedArguments
              matchedDirectives matchedSubselections) ->
    (∀ matchedArguments matchedDirectives matchedSubselections,
      Selection.field responseName fieldName matchedArguments matchedDirectives
          matchedSubselections
        ∈ validFieldsWithResponseName schema parentType responseName rest ->
        selectionSetLookupValid schema childType matchedSubselections) ->
      selectionSetLookupValid schema childType
        (subselections
          ++ mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName
              rest)) := by
  intro hhead hshape hmatching
  apply selectionSetLookupValid_append hhead
  apply selectionSetLookupValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    rcases hshape selection hselection with
      ⟨matchedArguments, matchedDirectives, matchedSubselections,
        hselectionShape⟩
    exact ⟨fieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionShape⟩
  · intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    have hmatchedShape :=
      hshape
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections)
        hmatched
    rcases hmatchedShape with
      ⟨shapeArguments, shapeDirectives, shapeSubselections, hshapeEq⟩
    injection hshapeEq with _hresponse hfield harguments hdirectives
      hsubselections
    subst matchedFieldName
    subst shapeArguments
    subst shapeDirectives
    subst shapeSubselections
    exact hmatching matchedArguments matchedDirectives matchedSubselections
      hmatched

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
        Execution.collectFields schema variableValues parentType source
          selectionSet
      else
        [] := by
  simp [Execution.collectSelection, Execution.selectionDirectivesAllowBool]

theorem rootSourceAppliesBool_normalizeOperation
    (schema : Schema) (operation : Operation) (source : Execution.Value) :
    Execution.rootSourceAppliesBool schema (normalizeOperation schema operation)
        source =
      Execution.rootSourceAppliesBool schema operation source := by
  rfl

theorem executeQuery_normalizeOperation_of_rootSource_not_apply
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (source : Execution.Value) :
    Execution.rootSourceAppliesBool schema operation source = false ->
      Execution.executeQuery schema resolvers variableValues operation source
        =
      Execution.executeQuery schema resolvers variableValues
        (normalizeOperation schema operation) source := by
  intro hroot
  simp [Execution.executeQuery, hroot,
    rootSourceAppliesBool_normalizeOperation]

theorem groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet
    (schema : Schema) (operation : Operation) :
    (∀ resolvers variableValues source,
      Execution.rootSourceAppliesBool schema operation source = true ->
        Execution.executeSelectionSet schema resolvers variableValues
          (Execution.executeQueryDepthBound operation)
          operation.rootType source operation.selectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues
          (Execution.executeQueryDepthBound
            (normalizeOperation schema operation))
          operation.rootType source
          (normalizeOperation schema operation).selectionSet) ->
      groundTypeNormalFormSemanticsPreserved schema operation := by
  intro hselection
  unfold groundTypeNormalFormSemanticsPreserved operationsEquivalent
  intro resolvers variableValues source
  by_cases hroot :
      Execution.rootSourceAppliesBool schema operation source = true
  · simp [Execution.executeQuery, hroot,
      rootSourceAppliesBool_normalizeOperation]
    exact hselection resolvers variableValues source hroot
  · have hrootFalse :
        Execution.rootSourceAppliesBool schema operation source = false := by
      cases hmatch : Execution.rootSourceAppliesBool schema operation source
      · rfl
      · contradiction
    exact executeQuery_normalizeOperation_of_rootSource_not_apply schema
      resolvers variableValues operation source hrootFalse

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
