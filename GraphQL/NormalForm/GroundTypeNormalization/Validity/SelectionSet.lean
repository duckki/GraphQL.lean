import GraphQL.NormalForm.GroundTypeNormalization.Validity.Support

/-! Selection-set validity preservation for ground-type normalization. -/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem normalizeSelectionSet_normalizedValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfeasibleAll :
      selectionSetsTypeConditionFeasibleInEveryScope schema) :
    ∀ parentType selectionSet,
      schema.objectType parentType ->
      selectionSetSemanticsReady schema parentType selectionSet ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions parentType selectionSet ->
      FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
      selectionSetDirectiveFree selectionSet ->
        NormalizedSelectionSetValid schema variableDefinitions parentType
          (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _hobject _hready _himplementation _hmerge _hfree
      simpa [normalizeSelectionSet] using
        normalizedSelectionSetValid_nil schema variableDefinitions parentType
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro hobject hready himplementation hmerge hfree
      have htailImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType rest :=
        selectionSetImplementationValidInScope_tail himplementation
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest hmerge
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType
            (withoutFieldsWithResponseName schema responseName rest) :=
        selectionSetImplementationValidInScope_withoutFieldsWithResponseName
          schema responseName variableDefinitions parentType rest
          htailImplementation
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldsWithResponseName schema responseName rest) :=
        withoutFieldsWithResponseName_directiveFree schema responseName rest
          hrestFree
      simpa [normalizeSelectionSet, hlookup] using
        hrest hobject hfilteredReady hfilteredImplementation hfilteredMerge
          hfilteredFree
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro hobject hready himplementation hmerge hfree
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      let normalizedSelection :=
        normalizedField schema returnType responseName fieldName arguments []
          normalizedSubselections
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hsubselectionsFree : selectionSetDirectiveFree subselections :=
        hselectionFree.2
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType rest :=
        selectionSetImplementationValidInScope_tail himplementation
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments []
            subselections)
          rest hmerge
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType
            (withoutFieldsWithResponseName schema responseName rest) :=
        selectionSetImplementationValidInScope_withoutFieldsWithResponseName
          schema responseName variableDefinitions parentType rest
          htailImplementation
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldsWithResponseName schema responseName rest) :=
        withoutFieldsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have hnormalizedRest :
          NormalizedSelectionSetValid schema variableDefinitions parentType
            (normalizeSelectionSet schema parentType
              (withoutFieldsWithResponseName schema responseName rest)) :=
        hrest hobject hfilteredReady hfilteredImplementation hfilteredMerge
          hfilteredFree
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments []
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments []
            subselections :: rest)
          hready
      have hmatchingFree :
          selectionSetDirectiveFree matching := by
        subst matching
        exact validFieldsWithResponseName_directiveFree schema parentType
          responseName rest hrestFree
      have hmergedFree :
          selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetDirectiveFree_append hsubselectionsFree
          (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hnormalizedSubselectionsValid :
          NormalizedSelectionSetValid schema variableDefinitions returnType
            normalizedSubselections := by
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType] using
              object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
          have hchildImplementation :
              Validation.selectionSetImplementationValidInScope schema
                variableDefinitions returnType mergedSubselections :=
            selectionSetImplementationValidInScope_fieldHead_merged_of_child_object
              schema variableDefinitions parentType responseName fieldName
              returnType arguments subselections rest fieldDefinition hobject
              hlookupValid himplementation hmerge hlookup
              (by simpa [returnType] using hinclude)
          have hchildMerge :
              FieldMerge.fieldsInSetCanMerge schema returnType
                mergedSubselections :=
            fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hlookupValid hmerge
              hlookup
          simpa [hreturnObject] using
            hmerged hreturnObjectType hchildReady hchildImplementation
              hchildMerge hmergedFree
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          apply possibleTypeNormalizations_normalizedValid schema
            variableDefinitions returnType (schema.getPossibleTypes returnType)
            mergedSubselections
          · intro objectType hobjectType
            exact
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType
          · intro objectType hobjectType
            exact hobjectType
          · intro objectType hobjectType
            have hobjectBranch :
                schema.objectType objectType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType
            have hinclude :
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType objectType = true :=
              List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType)
            have hchildReady :
                selectionSetSemanticsReady schema objectType
                  mergedSubselections :=
              selectionSetSemanticsReady_fieldHead_merged_of_child_object
                schema parentType responseName fieldName objectType arguments
                subselections rest fieldDefinition hobject hready hlookupValid
                hmerge hlookup (by simpa [returnType] using hinclude)
            have hchildImplementation :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions objectType mergedSubselections :=
              selectionSetImplementationValidInScope_fieldHead_merged_of_child_object
                schema variableDefinitions parentType responseName fieldName
                objectType arguments subselections rest fieldDefinition hobject
                hlookupValid himplementation hmerge hlookup
                (by simpa [returnType] using hinclude)
            have hchildMerge :
                FieldMerge.fieldsInSetCanMerge schema objectType
                  mergedSubselections :=
              fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName objectType arguments
                subselections rest fieldDefinition hobject hlookupValid hmerge
                hlookup
            exact hpossible objectType hobjectBranch hchildReady
              hchildImplementation hchildMerge hmergedFree
          · have hreturnLookup :
                selectionSetLookupValid schema returnType
                  mergedSubselections := by
              subst mergedSubselections
              simpa [returnType] using
                selectionSetLookupValid_fieldHead_merged_of_returnType
                  schema variableDefinitions parentType responseName fieldName
                  arguments subselections rest fieldDefinition hobject
                  hlookupValid himplementation hmerge hlookup
            have hreadyBranches :
                ∀ objectType,
                  objectType ∈ schema.getPossibleTypes returnType ->
                    selectionSetSemanticsReady schema objectType
                      mergedSubselections := by
              intro objectType hobjectType
              have hinclude :
                  schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType objectType = true :=
                List.contains_iff_mem.mpr
                  (by simpa [returnType] using hobjectType)
              exact
                selectionSetSemanticsReady_fieldHead_merged_of_child_object
                  schema parentType responseName fieldName objectType arguments
                  subselections rest fieldDefinition hobject hready
                  hlookupValid hmerge hlookup
                  (by simpa [returnType] using hinclude)
            have hmergeReturn :
                FieldMerge.fieldsInSetCanMerge schema returnType
                  mergedSubselections := by
              subst mergedSubselections
              exact
                fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                  schema parentType responseName fieldName returnType arguments
                  subselections rest fieldDefinition hobject hlookupValid hmerge
                  hlookup
            exact
              normalizedDistinctBranchesPairwiseMerge_of_abstractMerge
                schema variableDefinitions hschema returnType
                (schema.getPossibleTypes returnType) mergedSubselections
                (by
                  intro objectType hobjectType
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hobjectType)
                (by
                  intro objectType hobjectType
                  exact hobjectType)
                hreturnLookup hreadyBranches hmergeReturn
      have hnilIfLeaf :
          leafTypeNameBool schema fieldDefinition.outputType.namedType = true ->
            normalizedSubselections = [] := by
        intro hleaf
        subst normalizedSubselections
        have hobjectFalse :
            objectTypeNameBool schema returnType = false :=
          objectTypeNameBool_eq_false_of_isLeafType schema
            (by
              have hleafType :=
                leafTypeNameBool_eq_true_isLeafType schema
                  (by simpa [returnType] using hleaf)
              simpa [returnType] using hleafType)
        have hpossibleNil :
            schema.getPossibleTypes returnType = [] :=
          possibleTypes_eq_nil_of_leafTypeNameBool schema
            (by simpa [returnType] using hleaf)
        simp [hobjectFalse, hpossibleNil, possibleTypeNormalizations]
      have hnormalizedSubselectionsPossible :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes
                fieldDefinition.outputType.namedType ->
              Validation.selectionSetImplementationValidInScope schema
                variableDefinitions objectType normalizedSubselections := by
        intro objectType hobjectType
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hobjectEq : objectType = returnType :=
            object_typeIncludesObjectBool_eq_self schema hreturnObjectType
              (List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType))
          subst objectType
          simpa [hreturnObject] using
            hnormalizedSubselectionsValid.implementationValid
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          apply possibleTypeNormalizations_implementationValidInScope
          · intro branchType hbranchType
            exact
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType branchType hbranchType
          · intro branchType hbranchType
            have hbranchObject :
                schema.objectType branchType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType branchType hbranchType
            have hinclude :
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType branchType = true :=
              List.contains_iff_mem.mpr (by simpa [returnType] using hbranchType)
            have hchildReady :
                selectionSetSemanticsReady schema branchType
                  mergedSubselections :=
              selectionSetSemanticsReady_fieldHead_merged_of_child_object
                schema parentType responseName fieldName branchType arguments
                subselections rest fieldDefinition hobject hready hlookupValid
                hmerge hlookup (by simpa [returnType] using hinclude)
            have hchildImplementation :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions branchType mergedSubselections :=
              selectionSetImplementationValidInScope_fieldHead_merged_of_child_object
                schema variableDefinitions parentType responseName fieldName
                branchType arguments subselections rest fieldDefinition hobject
                hlookupValid himplementation hmerge hlookup
                (by simpa [returnType] using hinclude)
            have hchildMerge :
                FieldMerge.fieldsInSetCanMerge schema branchType
                  mergedSubselections :=
              fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName branchType arguments
                subselections rest fieldDefinition hobject hlookupValid hmerge
                hlookup
            exact hpossible branchType hbranchObject hchildReady
              hchildImplementation hchildMerge hmergedFree
      have hnormalizedSubselectionsNonempty :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            normalizedSubselections ≠ [] := by
        intro hcomposite
        have hsourceImplementation :
            Validation.selectionImplementationValid schema variableDefinitions
              parentType
              (Selection.field responseName fieldName arguments []
                subselections) :=
          selectionSetImplementationValidInScope_head himplementation
        have hsourceSelection :
            Validation.selectionValid schema variableDefinitions parentType
              (Selection.field responseName fieldName arguments []
                subselections) := by
          simpa [Validation.selectionImplementationValid, hlookup] using
            hsourceImplementation.1
        rcases Validation.selectionValid_field_lookup hsourceSelection with
          ⟨sourceDefinition, hsourceLookup, _harguments, hsourceChild⟩
        have hdefinitionEq : sourceDefinition = fieldDefinition := by
          rw [hlookup] at hsourceLookup
          cases hsourceLookup
          rfl
        subst sourceDefinition
        have hsubselectionsNonempty : subselections ≠ [] := by
          simp [Validation.fieldSelectionSetValid] at hsourceChild
          rcases hsourceChild.2 with hleaf | hsourceComposite
          · exact False.elim
              (isLeafType_not_isCompositeType hleaf.1 hcomposite)
          · exact hsourceComposite.2.1
        have hmergedNonempty : mergedSubselections ≠ [] := by
          subst mergedSubselections
          cases subselections with
          | nil =>
              exact False.elim (hsubselectionsNonempty rfl)
          | cons selection rest =>
              simp
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType] using
              object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
          have hmergedFeasible :
              selectionSetContainsTypeConditionFeasibleField schema
                [returnType] mergedSubselections :=
            (hfeasibleAll returnType mergedSubselections
              hmergedNonempty).1
          simpa [hreturnObject] using
            normalizeSelectionSet_ne_nil_of_feasible_forValidity schema
              returnType
              mergedSubselections hreturnObjectType hchildReady
              hmergedFeasible
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          have hreturnFeasible :
              selectionSetContainsTypeConditionFeasibleField schema
                [returnType] mergedSubselections :=
            (hfeasibleAll returnType mergedSubselections
              hmergedNonempty).1
          rcases
              typeConditionStackFeasible_of_selectionSetContains_forValidity
                schema [returnType] mergedSubselections hreturnFeasible with
            ⟨objectType, hobjectTypeAll⟩
          have hobjectType :
              objectType ∈ schema.getPossibleTypes returnType :=
            hobjectTypeAll returnType (by simp)
          have hnormalizedNonempty :
              possibleTypeNormalizations schema
                (schema.getPossibleTypes returnType) mergedSubselections ≠ [] := by
              have hobjectBranch :
                  schema.objectType objectType :=
                SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  hschema returnType objectType hobjectType
              have hinclude :
                  schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType objectType = true :=
                List.contains_iff_mem.mpr
                  (by simpa [returnType] using hobjectType)
              have hchildReady :
                  selectionSetSemanticsReady schema objectType
                    mergedSubselections :=
                selectionSetSemanticsReady_fieldHead_merged_of_child_object
                  schema parentType responseName fieldName objectType arguments
                  subselections rest fieldDefinition hobject hready
                  hlookupValid hmerge hlookup
                  (by simpa [returnType] using hinclude)
              have hmergedFeasible :
                  selectionSetContainsTypeConditionFeasibleField schema
                    [objectType] mergedSubselections :=
                (hfeasibleAll objectType mergedSubselections
                  hmergedNonempty).1
              have hbranchNonempty :
                  normalizeSelectionSet schema objectType
                    mergedSubselections ≠ [] :=
                normalizeSelectionSet_ne_nil_of_feasible_forValidity schema
                  objectType
                  mergedSubselections hobjectBranch hchildReady
                  hmergedFeasible
              exact
                possibleTypeNormalizations_ne_nil_of_branch_forValidity schema
                  hobjectType hbranchNonempty
          change
            (if objectTypeNameBool schema returnType then
              normalizeSelectionSet schema returnType mergedSubselections
            else
              possibleTypeNormalizations schema
                (schema.getPossibleTypes returnType) mergedSubselections) ≠ []
          simpa [hreturnObjectFalse] using hnormalizedNonempty
      have hnormalizedFieldImplementation :
          Validation.selectionImplementationValid schema variableDefinitions
            parentType normalizedSelection := by
        change
          Validation.selectionImplementationValid schema variableDefinitions
            parentType
            (Selection.field responseName fieldName arguments []
              normalizedSubselections)
        exact normalizedField_selectionImplementationValid
          (selectionSetImplementationValidInScope_head himplementation)
          hlookup hnormalizedSubselectionsValid.selectionSetValid
          hnormalizedSubselectionsNonempty
          hnormalizedSubselectionsValid.implementationValid
          hnormalizedSubselectionsPossible
          hnilIfLeaf
      have himplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType (normalizedSelection ::
              normalizeSelectionSet schema parentType
                (withoutFieldsWithResponseName schema responseName rest)) :=
        selectionSetImplementationValidInScope_cons
          hnormalizedFieldImplementation
          hnormalizedRest.implementationValid
      have hselectionSetValid :
          Validation.selectionSetValid schema variableDefinitions parentType
            (normalizedSelection ::
              normalizeSelectionSet schema parentType
                (withoutFieldsWithResponseName schema responseName rest)) :=
        selectionSetValid_of_allFields_implementationValidInScope schema
          variableDefinitions parentType
          (normalizedSelection ::
            normalizeSelectionSet schema parentType
              (withoutFieldsWithResponseName schema responseName rest))
          (by
            intro selection hselection
            simp at hselection
            rcases hselection with hhead | htail
            · subst selection
              simp [normalizedSelection, normalizedField, Selection.isField]
            · exact normalizeSelectionSet_allFields schema parentType
                (withoutFieldsWithResponseName schema responseName rest)
                selection htail)
          himplementation
      have hrestFreeResponse :
          selectionSetResponseNameFree schema parentType responseName
            (normalizeSelectionSet schema parentType
              (withoutFieldsWithResponseName schema responseName rest)) :=
        normalizeSelectionSet_responseNameFree schema parentType responseName
          (withoutFieldsWithResponseName schema responseName rest)
          (withoutFieldsWithResponseName_responseNameFree schema parentType
            responseName rest)
      have hfieldMergePair :
          FieldMerge.fieldsInSetCanMerge schema parentType
              (Selection.field responseName fieldName arguments []
                  normalizedSubselections ::
                normalizeSelectionSet schema parentType
                  (withoutFieldsWithResponseName schema responseName rest))
            ∧ ∀ mergeParent,
              FieldMerge.fieldsInSetCanMerge schema mergeParent
              ((Selection.field responseName fieldName arguments []
                    normalizedSubselections ::
                  normalizeSelectionSet schema parentType
                    (withoutFieldsWithResponseName schema responseName rest))
                ++
                (Selection.field responseName fieldName arguments []
                    normalizedSubselections ::
                  normalizeSelectionSet schema parentType
                    (withoutFieldsWithResponseName schema responseName rest))) := by
        apply fieldsInSetCanMerge_field_cons_of_rest_responseNameFree
        · exact hschema
        · exact hlookup
        · exact FieldMerge.sameResponseShape_refl schema
            fieldDefinition.outputType
            (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
              hschema hlookup)
        · exact argumentsEquivalent_refl arguments
        · intro objectType
          exact hnormalizedSubselectionsValid.fieldsCanMergeSelf objectType
        · exact hnormalizedRest.fieldsCanMerge
        · exact hnormalizedRest.fieldsCanMergeSelf
        · exact normalizeSelectionSet_allFields schema parentType
            (withoutFieldsWithResponseName schema responseName rest)
        · exact hrestFreeResponse
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [normalizeSelectionSet, hlookup, normalizedSelection,
          normalizedField] using
          hselectionSetValid
      · simpa [normalizeSelectionSet, hlookup, normalizedSelection,
          normalizedField] using
          himplementation
      · simpa [normalizeSelectionSet, hlookup, normalizedSelection,
          normalizedField] using
          hfieldMergePair.1
      · intro mergeParent
        simpa [normalizeSelectionSet, hlookup, normalizedSelection,
          normalizedField] using
          hfieldMergePair.2 mergeParent
  | case4 parentType rest directives subselections happend =>
      intro hobject hready himplementation hmerge hfree
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hhead :
            selectionSemanticsReady schema parentType
              (Selection.inlineFragment none [] subselections) := by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
        simpa [selectionSemanticsReady] using hhead
      have hbodyImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType subselections := by
        have hhead :=
          selectionSetImplementationValidInScope_head himplementation
        simpa [Validation.selectionImplementationValid] using hhead
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :=
        selectionSetImplementationValidInScope_tail himplementation
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType (subselections ++ rest) :=
        selectionSetImplementationValidInScope_append hbodyImplementation
          htailImplementation
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType
          subselections rest hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      simpa [normalizeSelectionSet] using
        happend hobject hbodyTailReady hbodyTailImplementation
          hbodyTailMerge hbodyTailFree
  | case5 parentType rest typeCondition directives subselections hoverlap
      hrest happend =>
      intro hobject hready himplementation hmerge hfree
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) []
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hheadImplementation :=
        selectionSetImplementationValidInScope_head himplementation
      have hbodyImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType subselections := by
        have hfragment :
            Validation.selectionSetImplementationValidInScope schema
                variableDefinitions typeCondition subselections
              ∧ ∀ objectType,
                objectType ∈ schema.getPossibleTypes typeCondition ->
                  Validation.selectionSetImplementationValidInScope schema
                    variableDefinitions objectType subselections := by
          simpa [Validation.selectionImplementationValid] using
            hheadImplementation hoverlap
        have hparentPossible :
            parentType ∈ schema.getPossibleTypes typeCondition :=
          List.contains_iff_mem.mp
            (typeIncludesObjectBool_of_object_typesOverlapBool schema
              hobject hoverlap)
        exact hfragment.2 parentType hparentPossible
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :=
        selectionSetImplementationValidInScope_tail himplementation
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailImplementation :
          Validation.selectionSetImplementationValidInScope schema
            variableDefinitions parentType (subselections ++ rest) :=
        selectionSetImplementationValidInScope_append hbodyImplementation
          htailImplementation
      have hlookupBodyType :
          selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hlookupBodyParent :
          selectionSetLookupValid schema parentType subselections :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hbodyReady
      have hlookupRest :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
          schema parentType typeCondition subselections rest hschema hobject
          hoverlap hlookupBodyParent hlookupBodyType hlookupRest hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      simpa [normalizeSelectionSet, hoverlap] using
        happend hobject hbodyTailReady hbodyTailImplementation
          hbodyTailMerge hbodyTailFree
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro hobject hready himplementation hmerge hfree
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :=
        selectionSetImplementationValidInScope_tail himplementation
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) directives
            subselections)
          rest hmerge
      have htailFree :=
        selectionSetDirectiveFree_tail hfree
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using
      hrest hobject htailReady htailImplementation htailMerge htailFree

mutual
  def selectionInlineFragmentsNonempty : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetInlineFragmentsNonempty selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSet ≠ [] ∧ selectionSetInlineFragmentsNonempty selectionSet

  def selectionSetInlineFragmentsNonempty (selectionSet : List Selection) :
      Prop :=
    ∀ selection, selection ∈ selectionSet ->
      selectionInlineFragmentsNonempty selection
end

mutual
  theorem selectionInlineFragmentsNonempty_of_selectionValid
      (schema : Schema) (variableDefinitions : List VariableDefinition) :
      ∀ parentType selection,
        Validation.selectionValid schema variableDefinitions parentType
          selection ->
          selectionInlineFragmentsNonempty selection
    | parentType,
      .field _responseName _fieldName _arguments _directives selectionSet,
      hvalid => by
        unfold selectionInlineFragmentsNonempty
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, _hlookup, _harguments, hchild⟩
        simp [Validation.fieldSelectionSetValid] at hchild
        rcases hchild.2 with hleaf | hcomposite
        · rw [hleaf.2]
          unfold selectionSetInlineFragmentsNonempty
          intro selection hselection
          cases hselection
        · exact
            selectionSetInlineFragmentsNonempty_of_selectionSetValid
              schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet
              hcomposite.2.2
    | parentType,
      .inlineFragment none _directives selectionSet, hvalid => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        exact ⟨hvalid'.2.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid
            schema variableDefinitions parentType selectionSet hvalid'.2.2⟩
    | _parentType,
      .inlineFragment (some typeCondition) _directives selectionSet,
      hvalid => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        exact ⟨hvalid'.2.2.2.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid
            schema variableDefinitions typeCondition selectionSet
            hvalid'.2.2.2.2⟩

  theorem selectionSetInlineFragmentsNonempty_of_selectionSetValid
      (schema : Schema) (variableDefinitions : List VariableDefinition) :
      ∀ parentType selectionSet,
        Validation.selectionSetValid schema variableDefinitions parentType
          selectionSet ->
          selectionSetInlineFragmentsNonempty selectionSet
    | parentType, selectionSet, hvalid => by
        unfold selectionSetInlineFragmentsNonempty
        unfold Validation.selectionSetValid at hvalid
        intro selection hselection
        exact selectionInlineFragmentsNonempty_of_selectionValid schema
          variableDefinitions parentType selection (hvalid selection hselection)
end


end GroundTypeNormalization

end NormalForm

end GraphQL
