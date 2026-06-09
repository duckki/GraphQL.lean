import GraphQL.NormalForm.CompleteNormalization.BoolCaseRuntime

/-!
Runtime type, field-merge, and readiness transport facts for complete normalization.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem leafTypeNameBool_false_of_objectTypeNameBool_true
    (schema : Schema) {typeName : Name} :
    objectTypeNameBool schema typeName = true ->
      leafTypeNameBool schema typeName = false := by
  intro hobject
  unfold objectTypeNameBool at hobject
  unfold leafTypeNameBool
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition <;> simp [hlookup] at hobject ⊢

theorem groundObjectTypesForType_objects
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (returnType : Name) :
    ∀ objectType, objectType ∈ groundObjectTypesForType schema returnType ->
      objectTypeNameBool schema objectType = true := by
  intro objectType hmem
  unfold groundObjectTypesForType at hmem
  cases hobject : objectTypeNameBool schema returnType with
  | false =>
      simp [hobject] at hmem
      exact GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
        schema
        (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
          hschema returnType objectType hmem)
  | true =>
      simp [hobject] at hmem
      subst objectType
      exact hobject

theorem groundObjectTypesForType_nodup
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (returnType : Name) :
    (groundObjectTypesForType schema returnType).Nodup := by
  unfold groundObjectTypesForType
  cases hobject : objectTypeNameBool schema returnType with
  | false =>
      simp
      exact SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
        hschema returnType
  | true =>
      simp

theorem typeIncludesObjectBool_mem_groundObjectTypesForType
    (schema : Schema) (returnType runtimeType : Name) :
    leafTypeNameBool schema returnType = false ->
    schema.typeIncludesObjectBool returnType runtimeType = true ->
      runtimeType ∈ groundObjectTypesForType schema returnType := by
  intro _hleafFalse hinclude
  unfold groundObjectTypesForType
  cases hobject : objectTypeNameBool schema returnType with
  | false =>
      simp
      exact List.contains_iff_mem.mp hinclude
  | true =>
      have hruntimeEq :
          runtimeType = returnType :=
        GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
          schema hobject hinclude
      subst runtimeType
      simp

theorem groundObjectTypesForType_mem_typeIncludesObjectBool
    (schema : Schema) (returnType runtimeType : Name) :
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
      schema.typeIncludesObjectBool returnType runtimeType = true := by
  intro _hleafFalse hmem
  unfold groundObjectTypesForType at hmem
  cases hobject : objectTypeNameBool schema returnType with
  | false =>
      simp [hobject] at hmem
      exact List.contains_iff_mem.mpr hmem
  | true =>
      simp [hobject] at hmem
      subst runtimeType
      exact GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
        schema hobject

theorem fieldMerge_collectFields_mergeSelectionSets_mem_of_mem
    (schema : Schema) (parentType : Name) :
    ∀ selections selection scopedField,
      selection ∈ selections ->
      scopedField ∈ FieldMerge.collectFields schema parentType
        selection.subselections ->
        scopedField ∈ FieldMerge.collectFields schema parentType
          (mergeSelectionSets selections)
  | [], selection, scopedField, hselection, _hfield => by
      cases hselection
  | head :: rest, selection, scopedField, hselection, hfield => by
      rw [mergeSelectionSets]
      rw [FieldMerge.collectFields_append]
      rcases List.mem_cons.mp hselection with hhead | htail
      · subst selection
        exact List.mem_append_left
          (FieldMerge.collectFields schema parentType
            (mergeSelectionSets rest))
          hfield
      · exact List.mem_append_right
          (FieldMerge.collectFields schema parentType head.subselections)
          (fieldMerge_collectFields_mergeSelectionSets_mem_of_mem schema
            parentType rest selection scopedField htail hfield)

theorem fieldMerge_collectFields_staticScoped_merged_mem_fieldHead_merged
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName runtimeType : Name)
    (selectionSet rest : List Selection)
    (scopedField : FieldMerge.ScopedField) :
    schema.typeIncludesObjectBool lookupParent groundType = true ->
    scopedField ∈ FieldMerge.collectFields schema runtimeType
        (selectionSet ++
          mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName rest))) ->
      scopedField ∈ FieldMerge.collectFields schema runtimeType
        (selectionSet ++
          mergeSelectionSets
            (validFieldsWithResponseName schema lookupParent responseName
              rest)) := by
  intro hground hfield
  rw [FieldMerge.collectFields_append] at hfield ⊢
  rcases List.mem_append.mp hfield with hchild | hmatched
  · exact List.mem_append_left
      (FieldMerge.collectFields schema runtimeType
        (mergeSelectionSets
          (validFieldsWithResponseName schema lookupParent responseName
            rest)))
      hchild
  · rcases
      fieldMerge_collectFields_mergeSelectionSets_mem
        schema runtimeType
        (eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName rest))
        scopedField hmatched with
      ⟨selection, hselection, hselectionField⟩
    have hvalid :
        selection ∈
          validFieldsWithResponseName schema lookupParent responseName rest :=
      erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
        schema boolCase lookupParent groundType responseName rest selection
        hground hselection
    exact List.mem_append_right
      (FieldMerge.collectFields schema runtimeType selectionSet)
      (fieldMerge_collectFields_mergeSelectionSets_mem_of_mem schema
        runtimeType
        (validFieldsWithResponseName schema lookupParent responseName rest)
        selection scopedField hvalid hselectionField)

theorem selectionSetLookupValid_field_head_clear_directives
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    selectionSetLookupValid schema parentType
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
      selectionSetLookupValid schema parentType
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) := by
  intro hlookupValid
  unfold selectionSetLookupValid at hlookupValid ⊢
  intro selection hmem
  rcases List.mem_cons.mp hmem with hhead | htail
  · subst selection
    have hheadValid :=
      hlookupValid
        (Selection.field responseName fieldName arguments directives
          selectionSet) (by simp)
    simpa [selectionLookupValid] using hheadValid
  · exact hlookupValid selection
      (List.mem_cons_of_mem
        (Selection.field responseName fieldName arguments directives
          selectionSet)
        htail)

theorem selectionSetValid_field_head_clear_directives
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
      Validation.selectionSetValid schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) := by
  intro hvalid
  unfold Validation.selectionSetValid at hvalid ⊢
  intro selection hmem
  rcases List.mem_cons.mp hmem with hhead | htail
  · subst selection
    have hheadValid :
        Validation.selectionValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments directives
            selectionSet) :=
      hvalid
        (Selection.field responseName fieldName arguments directives
          selectionSet) (by simp)
    simp [Validation.selectionValid] at hheadValid ⊢
    rcases hheadValid with
      ⟨_hdirectives, fieldDefinition, hlookup, harguments, hchild⟩
    refine ⟨?_, fieldDefinition, hlookup, harguments, hchild⟩
    simp [Validation.directivesValid]
  · exact hvalid selection
      (List.mem_cons_of_mem
        (Selection.field responseName fieldName arguments directives
          selectionSet)
        htail)

theorem selectionSetSemanticsReady_field_head_clear_directives
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    selectionSetSemanticsReady schema parentType
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
      selectionSetSemanticsReady schema parentType
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) := by
  intro hready
  unfold selectionSetSemanticsReady at hready ⊢
  intro selection hmem
  rcases List.mem_cons.mp hmem with hhead | htail
  · subst selection
    have hheadReady :=
      hready
        (Selection.field responseName fieldName arguments directives
          selectionSet) (by simp)
    simpa [selectionSemanticsReady] using hheadReady
  · exact hready selection
      (List.mem_cons_of_mem
        (Selection.field responseName fieldName arguments directives
          selectionSet)
        htail)

theorem fieldsInSetCanMerge_field_head_clear_directives
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
      FieldMerge.fieldsInSetCanMerge schema parentType
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (Selection.field responseName fieldName arguments [] selectionSet :: rest)
    ?_
  dsimp
  intro left hleft right hright hresponse
  have liftMem :
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema parentType
          (Selection.field responseName fieldName arguments []
            selectionSet :: rest) ->
        scopedField ∈ FieldMerge.collectFields schema parentType
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest) := by
    intro scopedField hfield
    cases hlookup : schema.lookupField parentType fieldName <;>
      simpa [FieldMerge.collectFields, hlookup] using hfield
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (liftMem left hleft) (liftMem right hright) hresponse

theorem selectionSetLookupValid_field_staticScoped_merged_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (boolCase : BoolCase)
    (lookupParent groundType responseName fieldName runtimeType : Name)
    (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.objectType lookupParent ->
    Validation.selectionSetValid schema variableDefinitions lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool lookupParent groundType = true ->
    schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
      runtimeType = true ->
      selectionSetLookupValid schema runtimeType
        (selectionSet ++
          mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName rest))) := by
  intro hschema hobject hvalid hmerge hlookup hground hinclude
  have hvalidNoDirectives :
      Validation.selectionSetValid schema variableDefinitions lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    selectionSetValid_field_head_clear_directives schema variableDefinitions
      lookupParent responseName fieldName arguments directives selectionSet rest
      hvalid
  have hlookupValidNoDirectives :
      selectionSetLookupValid schema lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    selectionSetLookupValid_of_selectionSetValid
      (Selection.field responseName fieldName arguments [] selectionSet :: rest)
      hvalidNoDirectives
  have hmergeNoDirectives :
      FieldMerge.fieldsInSetCanMerge schema lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    fieldsInSetCanMerge_field_head_clear_directives schema lookupParent
      responseName fieldName arguments directives selectionSet rest hmerge
  apply selectionSetLookupValid_append
  · have hheadValid :
        Validation.selectionValid schema variableDefinitions lookupParent
          (Selection.field responseName fieldName arguments [] selectionSet) :=
      by
        unfold Validation.selectionSetValid at hvalidNoDirectives
        exact hvalidNoDirectives
          (Selection.field responseName fieldName arguments [] selectionSet)
          (by simp)
    rcases Validation.selectionValid_field_lookup hheadValid with
      ⟨headDefinition, hheadLookup, _harguments, hchild⟩
    rw [hlookup] at hheadLookup
    cases hheadLookup
    have hpossible :
        runtimeType ∈
          schema.getPossibleTypes fieldDefinition.outputType.namedType :=
      List.contains_iff_mem.mp hinclude
    have hchildValid :
        Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType selectionSet :=
      fieldSelectionSetValid_child_of_possibleType
        hchild hpossible
    exact
      selectionSetLookupValid_of_selectionSetValid_possibleObject
        schema variableDefinitions fieldDefinition.outputType.namedType
        runtimeType hschema hpossible selectionSet hchildValid
  · apply
      selectionSetLookupValid_mergeSelectionSets_of_field_subselections
    · intro selection hselection
      have hvalidSelection :
          selection ∈
            validFieldsWithResponseName schema lookupParent responseName
              rest :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName rest
          selection hground hselection
      rcases
        validFieldsWithResponseName_matching_field_shape_of_canMerge_object_lookupValid
          schema lookupParent responseName fieldName arguments selectionSet
          rest hobject hlookupValidNoDirectives hmergeNoDirectives
          selection hvalidSelection with
        ⟨matchedArguments, matchedDirectives, matchedSubselections,
          hselectionShape⟩
      exact ⟨fieldName, matchedArguments, matchedDirectives,
        matchedSubselections, hselectionShape⟩
    · intro matchedFieldName matchedArguments matchedDirectives
        matchedSubselections hmatched
      have hvalidMatched :
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ validFieldsWithResponseName schema lookupParent responseName
              rest :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName rest
          (Selection.field responseName matchedFieldName matchedArguments
            matchedDirectives matchedSubselections)
          hground hmatched
      exact
        validFieldsWithResponseName_matching_subselections_lookupValid_of_child_object
          schema variableDefinitions lookupParent responseName fieldName
          runtimeType arguments selectionSet rest fieldDefinition hschema
          hobject hvalidNoDirectives hmergeNoDirectives hlookup hinclude
          matchedFieldName matchedArguments matchedDirectives
          matchedSubselections hvalidMatched

theorem fieldsInSetCanMerge_field_staticScoped_merged_object
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName fieldName runtimeType : Name)
    (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    schema.objectType lookupParent ->
    selectionSetLookupValid schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool lookupParent groundType = true ->
      FieldMerge.fieldsInSetCanMerge schema runtimeType
        (selectionSet ++
          mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName rest))) := by
  intro hobject hlookupValid hmerge hlookup hground
  have hlookupValidNoDirectives :
      selectionSetLookupValid schema lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    selectionSetLookupValid_field_head_clear_directives schema lookupParent
      responseName fieldName arguments directives selectionSet rest
      hlookupValid
  have hmergeNoDirectives :
      FieldMerge.fieldsInSetCanMerge schema lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    fieldsInSetCanMerge_field_head_clear_directives schema lookupParent
      responseName fieldName arguments directives selectionSet rest hmerge
  have hfull :
      FieldMerge.fieldsInSetCanMerge schema runtimeType
        (selectionSet ++
          mergeSelectionSets
            (validFieldsWithResponseName schema lookupParent responseName
              rest)) :=
    fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
      schema lookupParent responseName fieldName runtimeType arguments
      selectionSet rest fieldDefinition hobject hlookupValidNoDirectives
      hmergeNoDirectives hlookup
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro runtimeType
    (selectionSet ++
      mergeSelectionSets
        (eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName rest)))
    ?_
  dsimp
  intro left hleft right hright hresponse
  exact FieldMerge.fieldsInSetCanMerge_pair hfull
    (fieldMerge_collectFields_staticScoped_merged_mem_fieldHead_merged
      schema boolCase lookupParent groundType responseName runtimeType
      selectionSet rest left hground hleft)
    (fieldMerge_collectFields_staticScoped_merged_mem_fieldHead_merged
      schema boolCase lookupParent groundType responseName runtimeType
      selectionSet rest right hground hright)
    hresponse

theorem selectionSetSemanticsReady_field_staticScoped_merged_object
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName fieldName runtimeType : Name)
    (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    schema.objectType lookupParent ->
    selectionSetSemanticsReady schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    selectionSetLookupValid schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool lookupParent groundType = true ->
    schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
      runtimeType = true ->
      selectionSetSemanticsReady schema runtimeType
        (selectionSet ++
          mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName rest))) := by
  intro hobject hready hlookupValid hmerge hlookup hground hinclude
  have hreadyNoDirectives :
      selectionSetSemanticsReady schema lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    selectionSetSemanticsReady_field_head_clear_directives schema lookupParent
      responseName fieldName arguments directives selectionSet rest hready
  have hlookupValidNoDirectives :
      selectionSetLookupValid schema lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    selectionSetLookupValid_field_head_clear_directives schema lookupParent
      responseName fieldName arguments directives selectionSet rest
      hlookupValid
  have hmergeNoDirectives :
      FieldMerge.fieldsInSetCanMerge schema lookupParent
        (Selection.field responseName fieldName arguments []
          selectionSet :: rest) :=
    fieldsInSetCanMerge_field_head_clear_directives schema lookupParent
      responseName fieldName arguments directives selectionSet rest hmerge
  apply selectionSetSemanticsReady_append
  · have hheadReady :
        selectionSemanticsReady schema lookupParent
          (Selection.field responseName fieldName arguments []
            selectionSet) := by
      unfold selectionSetSemanticsReady at hreadyNoDirectives
      exact hreadyNoDirectives
        (Selection.field responseName fieldName arguments [] selectionSet)
        (by simp)
    simp [selectionSemanticsReady] at hheadReady
    rcases hheadReady with ⟨headDefinition, hheadLookup, hchildReady⟩
    rw [hlookup] at hheadLookup
    cases hheadLookup
    exact hchildReady runtimeType hinclude
  · apply
      selectionSetSemanticsReady_mergeSelectionSets_of_field_subselections
    · intro selection hselection
      have hvalid :
          selection ∈
            validFieldsWithResponseName schema lookupParent responseName
              rest :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName rest
          selection hground hselection
      rcases
        validFieldsWithResponseName_matching_field_shape_of_canMerge_object_lookupValid
          schema lookupParent responseName fieldName arguments selectionSet
          rest hobject hlookupValidNoDirectives hmergeNoDirectives
          selection hvalid with
        ⟨matchedArguments, matchedDirectives, matchedSubselections,
          hselectionShape⟩
      exact ⟨fieldName, matchedArguments, matchedDirectives,
        matchedSubselections, hselectionShape⟩
    · intro matchedFieldName matchedArguments matchedDirectives
        matchedSubselections hmatched
      have hvalid :
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ validFieldsWithResponseName schema lookupParent responseName
              rest :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName rest
          (Selection.field responseName matchedFieldName matchedArguments
            matchedDirectives matchedSubselections)
          hground hmatched
      exact
        validFieldsWithResponseName_matching_subselections_semanticsReady_of_child_object
          schema lookupParent responseName fieldName runtimeType arguments
          selectionSet rest fieldDefinition hobject hreadyNoDirectives
          hlookupValidNoDirectives hmergeNoDirectives hlookup hinclude
          matchedFieldName matchedArguments matchedDirectives
          matchedSubselections hvalid

theorem typeIncludesObjectBool_false_of_leafTypeNameBool
    (schema : Schema) (returnType runtimeType : Name) :
    leafTypeNameBool schema returnType = true ->
      schema.typeIncludesObjectBool returnType runtimeType = false := by
  intro hleaf
  unfold leafTypeNameBool at hleaf
  unfold Schema.typeIncludesObjectBool
  cases hlookup : schema.lookupType returnType with
  | none =>
      simp [hlookup] at hleaf
  | some typeDefinition =>
      cases typeDefinition with
      | builtinScalar scalar =>
          simp [Schema.getPossibleTypes, hlookup]
      | customScalar scalar =>
          simp [Schema.getPossibleTypes, hlookup]
      | object objectType =>
          simp [hlookup] at hleaf
      | interface interfaceType =>
          simp [hlookup] at hleaf
      | union unionType =>
          simp [hlookup] at hleaf
      | enum enumType =>
          simp [Schema.getPossibleTypes, hlookup]
      | inputObject inputObjectType =>
          simp [hlookup] at hleaf


end CompleteNormalization

end NormalForm

end GraphQL
