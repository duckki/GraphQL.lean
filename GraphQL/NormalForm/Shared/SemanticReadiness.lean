import GraphQL.NormalForm.Shared.LookupValidity
import GraphQL.NormalForm.Shared.RuntimeTypes
import GraphQL.NormalForm.Shared.FieldMerge

/-!
Semantic readiness facts for ground-type normalization proofs.
-/
namespace GraphQL

namespace NormalForm


mutual
  def selectionSemanticsReady (schema : Schema)
      (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
            ∧ ∀ runtimeType,
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType runtimeType = true ->
                selectionSetSemanticsReady schema runtimeType selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetSemanticsReady schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetLookupValid schema typeCondition selectionSet
          ∧ (schema.typesOverlapBool parentType typeCondition = true ->
            selectionSetSemanticsReady schema parentType selectionSet)

  def selectionSetSemanticsReady (schema : Schema)
      (parentType : Name) (selectionSet : List Selection) : Prop :=
    ∀ selection, selection ∈ selectionSet ->
      selectionSemanticsReady schema parentType selection
end

theorem selectionSetSemanticsReady_nil (schema : Schema)
    (parentType : Name) :
    selectionSetSemanticsReady schema parentType [] := by
  simp [selectionSetSemanticsReady]

theorem selectionSetSemanticsReady_append
    {schema : Schema} {parentType : Name}
    {left right : List Selection} :
    selectionSetSemanticsReady schema parentType left ->
      selectionSetSemanticsReady schema parentType right ->
        selectionSetSemanticsReady schema parentType (left ++ right) := by
  intro hleft hright
  unfold selectionSetSemanticsReady at hleft hright ⊢
  intro selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem selectionSetSemanticsReady_append_left
    {schema : Schema} {parentType : Name}
    {left right : List Selection} :
    selectionSetSemanticsReady schema parentType (left ++ right) ->
      selectionSetSemanticsReady schema parentType left := by
  intro hready
  unfold selectionSetSemanticsReady at hready ⊢
  intro selection hselection
  exact hready selection (List.mem_append.mpr (Or.inl hselection))

theorem selectionSetSemanticsReady_append_right
    {schema : Schema} {parentType : Name}
    {left right : List Selection} :
    selectionSetSemanticsReady schema parentType (left ++ right) ->
      selectionSetSemanticsReady schema parentType right := by
  intro hready
  unfold selectionSetSemanticsReady at hready ⊢
  intro selection hselection
  exact hready selection (List.mem_append.mpr (Or.inr hselection))

theorem selectionSetSemanticsReady_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection} :
    selectionSetSemanticsReady schema parentType (selection :: selectionSet) ->
      selectionSetSemanticsReady schema parentType selectionSet := by
  intro hready
  unfold selectionSetSemanticsReady at hready ⊢
  intro candidate hcandidate
  exact hready candidate (List.mem_cons_of_mem selection hcandidate)

mutual
  theorem selectionLookupValid_of_selectionSemanticsReady
      {schema : Schema} {parentType : Name} :
      ∀ selection,
        selectionSemanticsReady schema parentType selection ->
          selectionLookupValid schema parentType selection
    | .field _responseName fieldName _arguments _directives _selectionSet,
      hready => by
        simp [selectionSemanticsReady, selectionLookupValid] at hready ⊢
        rcases hready with ⟨fieldDefinition, hlookup, _hchild⟩
        exact ⟨fieldDefinition, hlookup⟩
    | .inlineFragment none _directives selectionSet, hready => by
        have hbody :
            selectionSetSemanticsReady schema parentType selectionSet := by
          simpa [selectionSemanticsReady] using hready
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
            hbody
    | .inlineFragment (some _typeCondition) _directives selectionSet,
      hready => by
        have hpair :
            selectionSetLookupValid schema _typeCondition selectionSet
              ∧ (schema.typesOverlapBool parentType _typeCondition = true ->
                selectionSetSemanticsReady schema parentType selectionSet) := by
          simpa [selectionSemanticsReady] using hready
        simpa [selectionLookupValid] using hpair.1

  theorem selectionSetLookupValid_of_selectionSetSemanticsReady
      {schema : Schema} {parentType : Name} :
      ∀ selectionSet,
        selectionSetSemanticsReady schema parentType selectionSet ->
          selectionSetLookupValid schema parentType selectionSet
    | [], _hready => by
        exact selectionSetLookupValid_nil schema parentType
    | selection :: rest, hready => by
        have hhead :
            selectionSemanticsReady schema parentType selection := by
          unfold selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htail :
            selectionSetSemanticsReady schema parentType rest :=
          selectionSetSemanticsReady_tail hready
        simp [selectionSetLookupValid]
        constructor
        · exact selectionLookupValid_of_selectionSemanticsReady selection hhead
        · simpa [selectionSetLookupValid] using
            selectionSetLookupValid_of_selectionSetSemanticsReady rest htail
end

theorem selectionSetSemanticsReady_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name} :
    ∀ selections,
      (∀ selection, selection ∈ selections ->
        selectionSetSemanticsReady schema parentType selection.subselections) ->
        selectionSetSemanticsReady schema parentType
          (mergeSelectionSets selections)
  | [], _hready => by
      simp [mergeSelectionSets, selectionSetSemanticsReady]
  | selection :: rest, hready => by
      simp [mergeSelectionSets]
      apply selectionSetSemanticsReady_append
      · exact hready selection (by simp)
      · exact selectionSetSemanticsReady_mergeSelectionSets_of_subselections rest
          (by
            intro candidate hcandidate
            exact hready candidate (by simp [hcandidate]))

theorem selectionSetSemanticsReady_mergeSelectionSets_of_field_subselections
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
        selectionSetSemanticsReady schema parentType subselections) ->
      selectionSetSemanticsReady schema parentType
        (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetSemanticsReady_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem selectionSetSemanticsReady_withoutFieldsWithResponseName
    (schema : Schema) (responseName : Name) :
    ∀ parentType selectionSet,
      selectionSetSemanticsReady schema parentType selectionSet ->
        selectionSetSemanticsReady schema parentType
          (withoutFieldsWithResponseName schema responseName selectionSet)
  | _parentType, [], _hready => by
      simp [withoutFieldsWithResponseName, selectionSetSemanticsReady]
  | parentType, selection :: rest, hready => by
      have hhead :
          selectionSemanticsReady schema parentType selection := by
        unfold selectionSetSemanticsReady at hready
        exact hready selection (by simp)
      have htail :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, hname]
            simpa [selectionSetSemanticsReady] using
              selectionSetSemanticsReady_withoutFieldsWithResponseName
                schema responseName parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse,
              selectionSetSemanticsReady]
            constructor
            · exact hhead
            · simpa [selectionSetSemanticsReady] using
                selectionSetSemanticsReady_withoutFieldsWithResponseName
                  schema responseName parentType rest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [withoutFieldsWithResponseName,
                selectionSetSemanticsReady, selectionSemanticsReady]
              constructor
              · simpa [selectionSetSemanticsReady] using
                  selectionSetSemanticsReady_withoutFieldsWithResponseName
                    schema responseName parentType selectionSet
                    (by simpa [selectionSemanticsReady] using hhead)
              · simpa [selectionSetSemanticsReady] using
                  selectionSetSemanticsReady_withoutFieldsWithResponseName
                    schema responseName parentType rest htail
            | some typeCondition =>
                simp [withoutFieldsWithResponseName,
                  selectionSetSemanticsReady, selectionSemanticsReady]
                constructor
                · constructor
                  · have hheadPair :
                      selectionSetLookupValid schema typeCondition
                            selectionSet
                          ∧ (schema.typesOverlapBool parentType typeCondition =
                            true ->
                            selectionSetSemanticsReady schema parentType
                              selectionSet) := by
                      simpa [selectionSemanticsReady] using hhead
                    exact
                      selectionSetLookupValid_withoutFieldsWithResponseName_core
                        schema responseName typeCondition selectionSet
                        hheadPair.1
                  · intro hoverlap
                    have hheadPair :
                      selectionSetLookupValid schema typeCondition
                            selectionSet
                          ∧ (schema.typesOverlapBool parentType typeCondition =
                            true ->
                            selectionSetSemanticsReady schema parentType
                              selectionSet) := by
                      simpa [selectionSemanticsReady] using hhead
                    simpa [selectionSetSemanticsReady] using
                      selectionSetSemanticsReady_withoutFieldsWithResponseName
                        schema responseName parentType selectionSet
                        (hheadPair.2 hoverlap)
                · simpa [selectionSetSemanticsReady] using
                    selectionSetSemanticsReady_withoutFieldsWithResponseName
                      schema responseName parentType rest htail

theorem validFieldsWithResponseName_field_semanticsReady
    (schema : Schema) (parentType responseName : Name) :
    ∀ selectionSet fieldName arguments directives subselections,
      selectionSetSemanticsReady schema parentType selectionSet ->
      Selection.field responseName fieldName arguments directives subselections
        ∈ validFieldsWithResponseName schema parentType responseName
          selectionSet ->
        ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
            ∧ ∀ runtimeType,
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType runtimeType = true ->
                selectionSetSemanticsReady schema runtimeType subselections
  | [], fieldName, arguments, directives, subselections, _hready, hfield => by
      simp [validFieldsWithResponseName] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hready, hfield => by
      have hhead :
          selectionSemanticsReady schema parentType selection := by
        unfold selectionSetSemanticsReady at hready
        exact hready selection (by simp)
      have htail :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
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
              simpa [selectionSemanticsReady] using hhead
            · exact
                validFieldsWithResponseName_field_semanticsReady schema
                  parentType responseName rest fieldName arguments directives
                  subselections htail hfield
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [validFieldsWithResponseName, hfalse] at hfield
            exact
              validFieldsWithResponseName_field_semanticsReady schema
                parentType responseName rest fieldName arguments directives
                subselections htail hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbody :
                  selectionSetSemanticsReady schema parentType selectionSet := by
                simpa [selectionSemanticsReady] using hhead
              simp [validFieldsWithResponseName] at hfield
              rcases hfield with hfield | hfield
              · exact
                  validFieldsWithResponseName_field_semanticsReady schema
                    parentType responseName selectionSet fieldName arguments
                    directives subselections hbody hfield
              · exact
                  validFieldsWithResponseName_field_semanticsReady schema
                    parentType responseName rest fieldName arguments directives
                    subselections htail hfield
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hbody :
                    selectionSetSemanticsReady schema parentType
                      selectionSet := by
                  have hheadPair :
                    selectionSetLookupValid schema typeCondition selectionSet
                      ∧ (schema.typesOverlapBool parentType typeCondition =
                        true ->
                        selectionSetSemanticsReady schema parentType
                          selectionSet) := by
                    simpa [selectionSemanticsReady] using hhead
                  exact hheadPair.2 hoverlap
                simp [validFieldsWithResponseName, hoverlap] at hfield
                rcases hfield with hfield | hfield
                · exact
                    validFieldsWithResponseName_field_semanticsReady schema
                      parentType responseName selectionSet fieldName
                      arguments directives subselections hbody hfield
                · exact
                    validFieldsWithResponseName_field_semanticsReady schema
                      parentType responseName rest fieldName arguments
                      directives subselections htail hfield
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [validFieldsWithResponseName, hfalse] at hfield
                exact
                  validFieldsWithResponseName_field_semanticsReady schema
                    parentType responseName rest fieldName arguments directives
                    subselections htail hfield

mutual
  theorem selectionSemanticsReady_of_selectionValid_object
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
        schema.objectType parentType ->
          ∀ selection,
            Validation.selectionValid schema variableDefinitions parentType
              selection ->
              selectionSemanticsReady schema parentType selection
    | hschema, hobject,
      .field _responseName fieldName _arguments _directives selectionSet,
      hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, hchild⟩
        simp [selectionSemanticsReady]
        refine ⟨fieldDefinition, hlookup, ?_⟩
        intro runtimeType hinclude
        have hpossible :
            runtimeType ∈
              schema.getPossibleTypes fieldDefinition.outputType.namedType :=
          List.contains_iff_mem.mp hinclude
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet :=
          fieldSelectionSetValid_child_of_possibleType hchild hpossible
        exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
          schema variableDefinitions fieldDefinition.outputType.namedType
          runtimeType hschema hpossible selectionSet hchildValid
      | hschema, hobject,
        .inlineFragment none _directives selectionSet, hvalid => by
          simpa [selectionSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_object schema
              variableDefinitions parentType hschema hobject selectionSet
              (Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid)
      | hschema, hobject,
        .inlineFragment (some typeCondition) _directives selectionSet,
        hvalid => by
          simp [selectionSemanticsReady]
          constructor
          · exact selectionSetLookupValid_of_selectionSetValid selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)
          · intro hoverlap
            have hpossible :
                parentType ∈ schema.getPossibleTypes typeCondition :=
              List.contains_iff_mem.mp
                (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
                  hoverlap)
            exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
              schema variableDefinitions typeCondition parentType hschema
              hpossible selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)

  theorem selectionSetSemanticsReady_of_selectionSetValid_object
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
        schema.objectType parentType ->
          ∀ selectionSet,
            Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet ->
              selectionSetSemanticsReady schema parentType selectionSet
    | _hschema, _hobject, [], _hvalid => by
        exact selectionSetSemanticsReady_nil schema parentType
    | hschema, hobject, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetSemanticsReady]
        constructor
        · exact selectionSemanticsReady_of_selectionValid_object schema
            variableDefinitions parentType hschema hobject selection hhead
        · simpa [selectionSetSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_object schema
              variableDefinitions parentType hschema hobject rest htail

  theorem selectionSemanticsReady_of_selectionValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
        objectType ∈ schema.getPossibleTypes parentType ->
          ∀ selection,
            Validation.selectionValid schema variableDefinitions parentType
              selection ->
              selectionSemanticsReady schema objectType selection
    | hschema, hpossible,
      .field _responseName fieldName _arguments _directives selectionSet,
      hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨expectedDefinition, hexpected, _harguments, hchild⟩
        rcases
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
            hschema hpossible hexpected with
          ⟨implementationDefinition, himplementation⟩
        simp [selectionSemanticsReady]
        refine ⟨implementationDefinition, himplementation, ?_⟩
        intro runtimeType hincludeImplementation
        have hsubtype :
            schema.outputTypeSubtype implementationDefinition.outputType
              expectedDefinition.outputType :=
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
            hschema hpossible hexpected himplementation
        have hincludeExpected :
            schema.typeIncludesObjectBool
              expectedDefinition.outputType.namedType runtimeType = true :=
          typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
            hsubtype hincludeImplementation
        have hpossibleExpected :
            runtimeType ∈
              schema.getPossibleTypes expectedDefinition.outputType.namedType :=
          List.contains_iff_mem.mp hincludeExpected
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              expectedDefinition.outputType.namedType selectionSet :=
          fieldSelectionSetValid_child_of_possibleType hchild
            hpossibleExpected
        exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
          schema variableDefinitions expectedDefinition.outputType.namedType
          runtimeType hschema hpossibleExpected selectionSet hchildValid
      | hschema, hpossible,
        .inlineFragment none _directives selectionSet, hvalid => by
          simpa [selectionSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_possibleObject
              schema variableDefinitions parentType objectType hschema
              hpossible selectionSet
              (Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid)
      | hschema, hpossible,
        .inlineFragment (some typeCondition) _directives selectionSet,
        hvalid => by
          simp [selectionSemanticsReady]
          constructor
          · exact selectionSetLookupValid_of_selectionSetValid selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)
          · intro hoverlap
            have hobject :
                schema.objectType objectType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema parentType objectType hpossible
            have hfragmentPossible :
                objectType ∈ schema.getPossibleTypes typeCondition :=
              List.contains_iff_mem.mp
                (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
                  hoverlap)
            exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
              schema variableDefinitions typeCondition objectType hschema
              hfragmentPossible selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)

  theorem selectionSetSemanticsReady_of_selectionSetValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name) :
      SchemaWellFormedness.schemaWellFormed schema ->
        objectType ∈ schema.getPossibleTypes parentType ->
          ∀ selectionSet,
            Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet ->
              selectionSetSemanticsReady schema objectType selectionSet
    | _hschema, _hpossible, [], _hvalid => by
        exact selectionSetSemanticsReady_nil schema objectType
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
        simp [selectionSetSemanticsReady]
        constructor
        · exact
            selectionSemanticsReady_of_selectionValid_possibleObject schema
              variableDefinitions parentType objectType hschema hpossible
              selection hhead
        · simpa [selectionSetSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_possibleObject
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

theorem validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
    (schema : Schema)
    (filterParent collectParent responseName : Name) :
    ∀ selectionSet fieldName arguments directives subselections,
      (schema.objectType collectParent ->
        schema.typesOverlapBool filterParent collectParent = true) ->
      selectionSetLookupValid schema collectParent selectionSet ->
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
      _hlookupValid, hfield => by
      simp [validFieldsWithResponseName] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hoverlapScope, hlookupValid, hfield => by
      have hheadLookup :
          selectionLookupValid schema collectParent selection := by
        unfold selectionSetLookupValid at hlookupValid
        exact hlookupValid selection (by simp)
      have htailLookup :
          selectionSetLookupValid schema collectParent rest :=
        selectionSetLookupValid_tail hlookupValid
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSubselections =>
          simp [selectionLookupValid] at hheadLookup
          rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
          by_cases hname : selectionResponseName == responseName
          · simp [validFieldsWithResponseName, hname] at hfield
            rcases hfield with hfield | hfield
            · rcases hfield with
                ⟨hresponse, hfieldName, harguments, hdirectives,
                  hsubselections⟩
              subst selectionResponseName
              subst selectionFieldName
              subst selectionArguments
              subst selectionDirectives
              subst selectionSubselections
              refine ⟨{
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  outputType := fieldDefinition.outputType,
                  selectionSet := subselections
                }, ?_, rfl, rfl, rfl, rfl, ?_⟩
              simp [FieldMerge.collectFields, hlookup]
              simpa using hoverlapScope
            · rcases
                validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
                  schema filterParent collectParent responseName rest
                  fieldName arguments directives subselections hoverlapScope
                  htailLookup
                  hfield with
                ⟨scopedField, hscoped, hresponse, hfieldName,
                  harguments, hselectionSet, hscopedOverlap⟩
              refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                hselectionSet, hscopedOverlap⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · have hfalse : (selectionResponseName == responseName) = false := by
              cases hmatch : selectionResponseName == responseName
              · rfl
              · exact False.elim (hname hmatch)
            simp [validFieldsWithResponseName, hfalse] at hfield
            rcases
              validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
                schema filterParent collectParent responseName rest
                fieldName arguments directives subselections hoverlapScope
                htailLookup hfield
              with
                ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
            refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
              hselectionSet, hscopedOverlap⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              simp [validFieldsWithResponseName] at hfield
              simp [selectionLookupValid] at hheadLookup
              rcases hfield with hfield | hfield
              · rcases
                  validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
                    schema filterParent collectParent responseName selectionSet
                    fieldName arguments directives subselections hoverlapScope
                    hheadLookup
                    hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
              · rcases
                  validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
                    schema filterParent collectParent responseName rest
                    fieldName arguments directives subselections hoverlapScope
                    htailLookup
                    hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [validFieldsWithResponseName, hoverlap] at hfield
                simp [selectionLookupValid] at hheadLookup
                rcases hfield with hfield | hfield
                · rcases
                    validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
                      schema filterParent typeCondition responseName
                      selectionSet fieldName arguments directives
                      subselections (fun _hobject => hoverlap) hheadLookup
                      hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName,
                      harguments, hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases
                    validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
                      schema filterParent collectParent responseName rest
                      fieldName arguments directives subselections
                      hoverlapScope htailLookup hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName,
                      harguments, hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition =
                      false := by
                    cases hmatch :
                        schema.typesOverlapBool filterParent typeCondition
                    · rfl
                    · exact False.elim (hoverlap hmatch)
                simp [validFieldsWithResponseName, hfalse] at hfield
                rcases
                  validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
                    schema filterParent collectParent responseName rest
                    fieldName arguments directives subselections hoverlapScope
                    htailLookup hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]

theorem fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
    (schema : Schema)
    (parentType responseName fieldName objectType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    schema.objectType parentType ->
    selectionSetLookupValid schema parentType
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
  intro hobject hlookupValid hmerge hlookup
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
  have htailLookup :
      selectionSetLookupValid schema parentType rest :=
    selectionSetLookupValid_tail hlookupValid
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
        validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
          schema parentType parentType responseName rest matchedFieldName
          matchedArguments matchedDirectives matchedSubselections
          hoverlapSelf htailLookup hmatched with
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

theorem validFieldsWithResponseName_matching_same_field_of_canMerge_object_lookupValid
    (schema : Schema)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection) :
    schema.objectType parentType ->
    selectionSetLookupValid schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
      ∀ matchedFieldName matchedArguments matchedDirectives
        matchedSubselections,
        Selection.field responseName matchedFieldName matchedArguments
            matchedDirectives matchedSubselections
          ∈ validFieldsWithResponseName schema parentType responseName
            rest ->
          matchedFieldName = fieldName := by
  intro hobject hlookupValid hmerge matchedFieldName matchedArguments
    matchedDirectives matchedSubselections hmatched
  have hheadLookup :
      selectionLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] subselections) := by
    unfold selectionSetLookupValid at hlookupValid
    exact hlookupValid _ (by simp)
  simp [selectionLookupValid] at hheadLookup
  rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
  let headScoped : FieldMerge.ScopedField :=
    {
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
  have htailLookup :
      selectionSetLookupValid schema parentType rest :=
    selectionSetLookupValid_tail hlookupValid
  rcases
    validFieldsWithResponseName_field_mem_collectFields_scoped_lookupValid
      schema parentType parentType responseName rest matchedFieldName
      matchedArguments matchedDirectives matchedSubselections
      (fun hobject => object_typesOverlapBool_self schema hobject)
      htailLookup hmatched with
    ⟨matchedScoped, hmatchedMemRest, hmatchedResponse,
      hmatchedField, _hmatchedArguments, _hmatchedSelectionSet,
      hmatchedOverlap⟩
  have hmatchedMem :
      matchedScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped matchedScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      (by simpa [headScoped] using hmatchedResponse.symm)
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

theorem validFieldsWithResponseName_matching_field_shape_of_canMerge_object_lookupValid
    (schema : Schema)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection) :
    schema.objectType parentType ->
    selectionSetLookupValid schema parentType
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
  intro hobject hlookupValid hmerge selection hselection
  rcases validFieldsWithResponseName_mem_field schema parentType responseName
      rest selection hselection with
    ⟨matchedFieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionEq⟩
  subst selection
  have hsame :=
    validFieldsWithResponseName_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hselection
  subst matchedFieldName
  exact ⟨matchedArguments, matchedDirectives, matchedSubselections, rfl⟩

theorem validFieldsWithResponseName_matching_subselections_lookupValid_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.objectType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
      runtimeType = true ->
      ∀ matchedFieldName matchedArguments matchedDirectives
        matchedSubselections,
        Selection.field responseName matchedFieldName matchedArguments
            matchedDirectives matchedSubselections
          ∈ validFieldsWithResponseName schema parentType responseName rest ->
          selectionSetLookupValid schema runtimeType matchedSubselections := by
  intro hschema hobject hvalid hmerge hlookup hinclude matchedFieldName
    matchedArguments matchedDirectives matchedSubselections hmatched
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
    validFieldsWithResponseName_field_mem_collectFields_scoped_source_object
      schema variableDefinitions parentType parentType responseName rest
      matchedFieldName matchedArguments matchedDirectives matchedSubselections
      (fun hobject => object_typeIncludesObjectBool_self schema hobject)
      htailValid hmatched with
    ⟨matchedScoped, hmatchedMemRest, hmatchedResponse, hmatchedField,
      _hmatchedArguments, hmatchedSelectionSet, hmatchedSource⟩
  have hmatchedMem :
      matchedScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped matchedScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      (by simpa [headScoped] using hmatchedResponse.symm)
  have hparents :
      headScoped.parentType = matchedScoped.parentType
        ∨ ¬ schema.objectType headScoped.parentType
        ∨ ¬ schema.objectType matchedScoped.parentType := by
    by_cases hmatchedObject : schema.objectType matchedScoped.parentType
    · have hsource := hmatchedSource hobject
      have hparentEq :
          parentType = matchedScoped.parentType :=
        object_typeIncludesObjectBool_eq_self schema hmatchedObject hsource
      exact Or.inl (by simp [headScoped, hparentEq])
    · exact Or.inr (Or.inr hmatchedObject)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_identity hfieldMerge hparents
  have hmatchedFieldName :
      matchedFieldName = fieldName := by
    have hsame : headScoped.fieldName = matchedScoped.fieldName :=
      hidentity.1
    exact hmatchedField.symm.trans (hsame.symm.trans (by rfl))
  rcases
    collectFields_scoped_mem_fieldSelectionSetValid schema variableDefinitions
      parentType rest matchedScoped htailValid hmatchedMemRest with
    ⟨matchedDefinition, hmatchedLookup, hmatchedOutput,
      hmatchedChild⟩
  have hmatchedPossible :
      runtimeType ∈
        schema.getPossibleTypes matchedDefinition.outputType.namedType := by
    by_cases hmatchedObject : schema.objectType matchedScoped.parentType
    · have hsource := hmatchedSource hobject
      have hparentEq :
          parentType = matchedScoped.parentType :=
        object_typeIncludesObjectBool_eq_self schema hmatchedObject hsource
      have hlookupEq :
          matchedDefinition = fieldDefinition := by
        have hlookup' :
            schema.lookupField parentType fieldName = some matchedDefinition := by
          simpa [hparentEq, hmatchedFieldName, hmatchedField] using
            hmatchedLookup
        rw [hlookup] at hlookup'
        cases hlookup'
        rfl
      subst matchedDefinition
      exact List.contains_iff_mem.mp hinclude
    · have hmatchedFieldEq : matchedScoped.fieldName = fieldName := by
        simpa [hmatchedFieldName] using hmatchedField
      have himplementationLookup :
          schema.lookupField parentType matchedScoped.fieldName =
            some fieldDefinition := by
        simpa [hmatchedFieldEq] using hlookup
      have hpossibleParent :
          parentType ∈ schema.getPossibleTypes matchedScoped.parentType :=
        List.contains_iff_mem.mp (hmatchedSource hobject)
      have hsubtype :
          schema.outputTypeSubtype fieldDefinition.outputType
            matchedDefinition.outputType :=
        SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
          hschema hpossibleParent hmatchedLookup himplementationLookup
      have hmatchedInclude :
          schema.typeIncludesObjectBool matchedDefinition.outputType.namedType
            runtimeType = true :=
        typeIncludesObjectBool_of_outputTypeSubtype_namedType schema hsubtype
          hinclude
      exact List.contains_iff_mem.mp hmatchedInclude
  have hmatchedSelectionValid :
      Validation.selectionSetValid schema variableDefinitions
        matchedDefinition.outputType.namedType matchedSubselections := by
    have hchild :
        Validation.fieldSelectionSetValid schema variableDefinitions
          matchedDefinition matchedSubselections := by
      simpa [hmatchedSelectionSet, hmatchedOutput] using hmatchedChild
    exact fieldSelectionSetValid_child_of_possibleType hchild
      hmatchedPossible
  exact selectionSetLookupValid_of_selectionSetValid_possibleObject schema
    variableDefinitions matchedDefinition.outputType.namedType runtimeType
    hschema hmatchedPossible matchedSubselections hmatchedSelectionValid

theorem validFieldsWithResponseName_matching_subselections_semanticsReady_of_child_object
    (schema : Schema)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    schema.objectType parentType ->
    selectionSetSemanticsReady schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    selectionSetLookupValid schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
      runtimeType = true ->
      ∀ matchedFieldName matchedArguments matchedDirectives
        matchedSubselections,
        Selection.field responseName matchedFieldName matchedArguments
            matchedDirectives matchedSubselections
          ∈ validFieldsWithResponseName schema parentType responseName rest ->
          selectionSetSemanticsReady schema runtimeType
            matchedSubselections := by
  intro hobject hready hlookupValid hmerge hlookup hinclude
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailReady :
      selectionSetSemanticsReady schema parentType rest :=
    selectionSetSemanticsReady_tail hready
  rcases
    validFieldsWithResponseName_field_semanticsReady schema parentType
      responseName rest matchedFieldName matchedArguments matchedDirectives
      matchedSubselections htailReady hmatched with
    ⟨matchedDefinition, hmatchedLookup, hmatchedReady⟩
  have hsame :
      matchedFieldName = fieldName :=
    validFieldsWithResponseName_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  have hdefinitionEq : matchedDefinition = fieldDefinition := by
    rw [hlookup] at hmatchedLookup
    cases hmatchedLookup
    rfl
  subst matchedDefinition
  exact hmatchedReady runtimeType hinclude

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

theorem selectionSetLookupValid_fieldHead_merged_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.objectType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
      runtimeType = true ->
      selectionSetLookupValid schema runtimeType
        (subselections ++
          mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName
              rest)) := by
  intro hschema hobject hvalid hmerge hlookup hinclude
  rcases Validation.selectionSetValid_field_head_lookup hvalid with
    ⟨headDefinition, hheadLookup, _harguments, hheadChild⟩
  have hdefinitionEq : headDefinition = fieldDefinition := by
    rw [hlookup] at hheadLookup
    cases hheadLookup
    rfl
  subst headDefinition
  have hheadSelectionValid :
      Validation.selectionSetValid schema variableDefinitions
        fieldDefinition.outputType.namedType subselections :=
    fieldSelectionSetValid_child_of_possibleType hheadChild
      (List.contains_iff_mem.mp hinclude)
  have hheadLookupValid :
      selectionSetLookupValid schema runtimeType subselections :=
    selectionSetLookupValid_of_selectionSetValid_possibleObject schema
      variableDefinitions fieldDefinition.outputType.namedType runtimeType
      hschema (List.contains_iff_mem.mp hinclude) subselections
      hheadSelectionValid
  have hlookupValid :
      selectionSetLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) :=
    selectionSetLookupValid_of_selectionSetValid
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hvalid
  apply selectionSetLookupValid_fieldHead_merged_of_matching schema parentType
    responseName fieldName runtimeType arguments subselections rest
  · exact hheadLookupValid
  · exact
      validFieldsWithResponseName_matching_field_shape_of_canMerge_object_lookupValid
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge
  · intro matchedArguments matchedDirectives matchedSubselections hmatched
    exact
      validFieldsWithResponseName_matching_subselections_lookupValid_of_child_object
        schema variableDefinitions parentType responseName fieldName
        runtimeType arguments subselections rest fieldDefinition hschema
        hobject hvalid hmerge hlookup hinclude fieldName matchedArguments
        matchedDirectives matchedSubselections hmatched

theorem selectionSetSemanticsReady_fieldHead_merged_of_child_object
    (schema : Schema)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    schema.objectType parentType ->
    selectionSetSemanticsReady schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    selectionSetLookupValid schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
      runtimeType = true ->
      selectionSetSemanticsReady schema runtimeType
        (subselections ++
          mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName
              rest)) := by
  intro hobject hready hlookupValid hmerge hlookup hinclude
  have hheadReady :
      selectionSemanticsReady schema parentType
        (Selection.field responseName fieldName arguments [] subselections) := by
    unfold selectionSetSemanticsReady at hready
    exact hready _ (by simp)
  have hheadChildReady :
      selectionSetSemanticsReady schema runtimeType subselections := by
    simp [selectionSemanticsReady] at hheadReady
    rcases hheadReady with ⟨headDefinition, hheadLookup, hchildReady⟩
    rw [hlookup] at hheadLookup
    cases hheadLookup
    exact hchildReady runtimeType hinclude
  apply selectionSetSemanticsReady_append hheadChildReady
  apply selectionSetSemanticsReady_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    rcases
      validFieldsWithResponseName_matching_field_shape_of_canMerge_object_lookupValid
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge selection hselection with
      ⟨matchedArguments, matchedDirectives, matchedSubselections, hselectionEq⟩
    exact
      ⟨fieldName, matchedArguments, matchedDirectives, matchedSubselections,
        hselectionEq⟩
  · intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    have hmatchedShape :=
      validFieldsWithResponseName_matching_field_shape_of_canMerge_object_lookupValid
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge
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
    exact
      validFieldsWithResponseName_matching_subselections_semanticsReady_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition hobject hready hlookupValid
        hmerge hlookup hinclude fieldName matchedArguments
        matchedDirectives matchedSubselections hmatched




end NormalForm

end GraphQL
