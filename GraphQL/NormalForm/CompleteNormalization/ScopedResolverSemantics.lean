import GraphQL.NormalForm.CompleteNormalization.BoolCaseChildSemantics

/-!
Scoped resolver and store-backed static-collection facts for complete normalization.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

def completeScopedFieldOutputValuesInclude {ObjectIdentity : Type}
    (schema : Schema) (boolCase : BoolCase)
    (value : Execution.Value ObjectIdentity)
    (scopedSelections : List CompleteScopedSelection) : Prop :=
  ∀ scopedSelection, scopedSelection ∈ scopedSelections ->
    ∃ responseName fieldName arguments directives subselections
        fieldDefinition,
      scopedSelection.selection =
        Selection.field responseName fieldName arguments directives
          subselections
        ∧ directivesAllowIn boolCase directives = true
        ∧ schema.lookupField scopedSelection.lookupParent fieldName =
          some fieldDefinition
        ∧ GroundTypeNormalization.executionValueObjectsInclude schema
          fieldDefinition.outputType.namedType value

theorem completeScopedFieldOutputValuesInclude_runtimeReady_of_object
    {ObjectIdentity : Type}
    (schema : Schema) (boolCase : BoolCase)
    (runtimeType : Name) (identity : ObjectIdentity)
    (scopedMatches : List CompleteScopedSelection) :
    completeScopedFieldOutputValuesInclude schema boolCase
      (.object runtimeType identity) scopedMatches ->
      ∀ scopedSelection, scopedSelection ∈ scopedMatches ->
        completeScopedSelectionRuntimeReady schema boolCase runtimeType
          scopedSelection := by
  intro hmatches scopedSelection hmem
  rcases hmatches scopedSelection hmem with
    ⟨responseName, fieldName, arguments, directives, subselections,
      fieldDefinition, hselection, hallow, hlookup, hincludes⟩
  rw [completeScopedSelectionRuntimeReady, hselection]
  refine ⟨hallow, fieldDefinition, hlookup, ?_, ?_⟩
  · cases hleaf :
      leafTypeNameBool schema fieldDefinition.outputType.namedType
    · rfl
    · have hfalse :=
        typeIncludesObjectBool_false_of_leafTypeNameBool schema
          fieldDefinition.outputType.namedType runtimeType hleaf
      have hincludeBool :
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
              runtimeType =
            true := by
        simpa [GroundTypeNormalization.executionValueObjectsInclude] using
          hincludes
      rw [hincludeBool] at hfalse
      cases hfalse
  · exact
      typeIncludesObjectBool_mem_groundObjectTypesForType schema
        fieldDefinition.outputType.namedType runtimeType
        (by
          cases hleaf :
            leafTypeNameBool schema fieldDefinition.outputType.namedType
          · rfl
          · have hfalse :=
              typeIncludesObjectBool_false_of_leafTypeNameBool schema
                fieldDefinition.outputType.namedType runtimeType hleaf
            have hincludeBool :
                schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType runtimeType =
                  true := by
              simpa [GroundTypeNormalization.executionValueObjectsInclude]
                using hincludes
            rw [hincludeBool] at hfalse
            cases hfalse)
        (by
          simpa [GroundTypeNormalization.executionValueObjectsInclude] using
            hincludes)

theorem completeValue_normalizeForTypeIn_staticScoped_eq_of_valueObjectsInclude_lt
    {ObjectIdentity : Type}
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth actualType expectedType groundType variables boolCase
      selectionSet scopedMatches value,
      GroundTypeNormalization.executionValueObjectsInclude schema
        expectedType value ->
      completeScopedFieldOutputValuesInclude schema boolCase value
        scopedMatches ->
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool actualType runtimeType = true ->
          Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (staticCollectForGround schema variables runtimeType
              runtimeType boolCase
              (selectionSet
                ++ mergeSelectionSets
                  (eraseCompleteScopedSelectionSet scopedMatches)))
          =
          Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (selectionSet
              ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet scopedMatches))) ->
        Execution.completeValue schema resolvers variableValues depth
            actualType
            (normalizeForTypeIn schema
                variables boolCase expectedType selectionSet
              ++ mergeSelectionSets
                (staticCollectCompleteScopedSelectionSet schema variables
                  groundType boolCase scopedMatches))
            value
          =
        Execution.completeValue schema resolvers variableValues depth actualType
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches))
          value
  | 0, _actualType, _expectedType, _groundType, _variables, _boolCase,
    _selectionSet, _scopedMatches, _value, _hheadInclude,
    _hmatchesInclude, _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, actualType, expectedType, groundType, variables, boolCase,
    selectionSet, scopedMatches, value, hheadInclude, hmatchesInclude,
    hrecursive => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType identity =>
          by_cases hactual :
              schema.typeIncludesObjectBool actualType runtimeType = true
          · have hexpected :
                schema.typeIncludesObjectBool expectedType runtimeType = true := by
              simpa [GroundTypeNormalization.executionValueObjectsInclude]
                using hheadInclude
            cases hleaf : leafTypeNameBool schema expectedType
            · have hmem :
                  runtimeType ∈ groundObjectTypesForType schema expectedType :=
                typeIncludesObjectBool_mem_groundObjectTypesForType schema
                  expectedType runtimeType hleaf hexpected
              have hscopedReady :
                  ∀ scopedSelection, scopedSelection ∈ scopedMatches ->
                    completeScopedSelectionRuntimeReady schema boolCase
                      runtimeType scopedSelection :=
                completeScopedFieldOutputValuesInclude_runtimeReady_of_object
                  schema boolCase runtimeType identity scopedMatches
                  hmatchesInclude
              have hselection :
                  Execution.executeSelectionSet schema resolvers variableValues
                      depth runtimeType (.object runtimeType identity)
                      (normalizeForTypeIn
                          schema variables boolCase expectedType
                          selectionSet
                        ++ mergeSelectionSets
                          (staticCollectCompleteScopedSelectionSet schema
                            variables groundType boolCase scopedMatches))
                    =
                  Execution.executeSelectionSet schema resolvers variableValues
                    depth runtimeType (.object runtimeType identity)
                    (selectionSet
                      ++ mergeSelectionSets
                        (eraseCompleteScopedSelectionSet scopedMatches)) := by
                calc
                  Execution.executeSelectionSet schema resolvers variableValues
                      depth runtimeType (.object runtimeType identity)
                      (normalizeForTypeIn
                          schema variables boolCase expectedType
                          selectionSet
                        ++ mergeSelectionSets
                          (staticCollectCompleteScopedSelectionSet schema
                            variables groundType boolCase scopedMatches))
                    =
                  Execution.executeSelectionSet schema resolvers variableValues
                      depth runtimeType (.object runtimeType identity)
                      (staticCollectForGround schema variables
                        runtimeType runtimeType boolCase
                        (selectionSet
                          ++ mergeSelectionSets
                            (eraseCompleteScopedSelectionSet scopedMatches))) := by
                      exact
                        executeSelectionSet_normalizeForTypeIn_staticScoped_runtime
                          schema resolvers variableValues variables
                          boolCase depth expectedType groundType runtimeType
                          identity selectionSet scopedMatches hschema hleaf
                          hmem hscopedReady
                  _ =
                  Execution.executeSelectionSet schema resolvers variableValues
                      depth runtimeType (.object runtimeType identity)
                      (selectionSet
                        ++ mergeSelectionSets
                          (eraseCompleteScopedSelectionSet scopedMatches)) :=
                    hrecursive depth runtimeType identity
                      (Nat.lt_succ_self depth) hactual
              simp [Execution.completeValue, hactual]
              exact hselection
            · have hexpectedFalse :
                  schema.typeIncludesObjectBool expectedType runtimeType =
                    false :=
                typeIncludesObjectBool_false_of_leafTypeNameBool schema
                  expectedType runtimeType hleaf
              rw [hexpected] at hexpectedFalse
              cases hexpectedFalse
          · have hactualFalse :
                schema.typeIncludesObjectBool actualType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool actualType runtimeType
              · rfl
              · exact False.elim (hactual hmatch)
            simp [Execution.completeValue, hactualFalse]
      | list values =>
          have hheadElements :
              ∀ value, value ∈ values ->
                GroundTypeNormalization.executionValueObjectsInclude schema
                  expectedType value := by
            simpa [GroundTypeNormalization.executionValueObjectsInclude] using
              hheadInclude
          have hmatchesElements :
              ∀ value, value ∈ values ->
                completeScopedFieldOutputValuesInclude schema boolCase value
                  scopedMatches := by
            intro value hvalue scopedSelection hscoped
            rcases hmatchesInclude scopedSelection hscoped with
              ⟨responseName, fieldName, arguments, directives, subselections,
                fieldDefinition, hselection, hallow, hlookup, hincludes⟩
            refine ⟨responseName, fieldName, arguments, directives,
              subselections, fieldDefinition, hselection, hallow, hlookup,
              ?_⟩
            have hincludesElements :
                ∀ value, value ∈ values ->
                  GroundTypeNormalization.executionValueObjectsInclude schema
                    fieldDefinition.outputType.namedType value := by
              simpa [GroundTypeNormalization.executionValueObjectsInclude]
                using hincludes
            exact hincludesElements value hvalue
          simp [Execution.completeValue]
          intro element helement
          exact
            completeValue_normalizeForTypeIn_staticScoped_eq_of_valueObjectsInclude_lt
              schema resolvers variableValues hschema depth actualType
              expectedType groundType variables boolCase selectionSet
              scopedMatches element (hheadElements element helement)
              (hmatchesElements element helement)
              (by
                intro childDepth runtimeType identity hlt hinclude
                exact hrecursive childDepth runtimeType identity
                  (Nat.lt_trans hlt (Nat.lt_succ_self depth)) hinclude)

theorem completeScopedSelectionSetStaticFieldsWithResponseName_valuesInclude_on_store
    (schema : Schema) (store : DataModel.Store)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (execParent lookupParent groundType : Name)
    (identity : DataModel.ObjectPath)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (rest : List CompleteScopedSelection) :
    schema.objectType execParent ->
    schema.typeIncludesObjectBool execParent groundType = true ->
    completeScopedSelectionSetSemanticsReady schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetLookupValid schema
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetCanMerge schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetGroundApplies schema groundType rest ->
      completeScopedFieldOutputValuesInclude schema boolCase
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object groundType identity))
        (completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName rest) := by
  intro hobject hground hready hlookup hmerge hmatchesGround scopedSelection
    hscoped
  have herased :
      scopedSelection.selection ∈
        eraseCompleteScopedSelectionSet
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName rest) :=
    eraseCompleteScopedSelectionSet_mem_of_mem hscoped
  have hstaticErased :
      scopedSelection.selection ∈
        eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase execParent
            groundType responseName
            (eraseCompleteScopedSelectionSet rest)) := by
    simpa [
      eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
        schema boolCase execParent groundType responseName rest] using
      herased
  have hvalidMatched :
      scopedSelection.selection ∈
        validFieldsWithResponseName schema execParent responseName
          (eraseCompleteScopedSelectionSet rest) :=
    erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
      schema boolCase execParent groundType responseName
      (eraseCompleteScopedSelectionSet rest) scopedSelection.selection
      hground hstaticErased
  rcases
      GroundTypeNormalization.validFieldsWithResponseName_mem_field
        schema execParent responseName
        (eraseCompleteScopedSelectionSet rest) scopedSelection.selection
        hvalidMatched with
    ⟨matchedFieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionShape⟩
  have hvalidMatchedField :
      Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections
        ∈ validFieldsWithResponseName schema execParent responseName
          (eraseCompleteScopedSelectionSet rest) := by
    simpa [hselectionShape] using hvalidMatched
  have hmatchesLookup :
      completeScopedSelectionSetLookupValid schema
        (completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName rest) :=
    completeScopedSelectionSetStaticFieldsWithResponseName_lookupValid schema
      boolCase groundType responseName rest
      (completeScopedSelectionSetLookupValid_tail hlookup)
  have hmatchedLookupSelection :
      GroundTypeNormalization.selectionLookupValid schema
        scopedSelection.lookupParent scopedSelection.selection :=
    hmatchesLookup scopedSelection hscoped
  have hmatchedLookupField :
      ∃ fieldDefinition,
        schema.lookupField scopedSelection.lookupParent matchedFieldName =
          some fieldDefinition := by
    simpa [hselectionShape,
      GroundTypeNormalization.selectionLookupValid] using
      hmatchedLookupSelection
  rcases hmatchedLookupField with
    ⟨matchedFieldDefinition, hmatchedLookup⟩
  have hrawReady :
      GroundTypeNormalization.selectionSetSemanticsReady schema execParent
        (Selection.field responseName fieldName arguments directives
            selectionSet
          :: eraseCompleteScopedSelectionSet rest) := by
    simpa [completeScopedSelectionSetSemanticsReady,
      eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection] using
      hready
  have hrawLookup :
      GroundTypeNormalization.selectionSetLookupValid schema execParent
        (Selection.field responseName fieldName arguments directives
            selectionSet
          :: eraseCompleteScopedSelectionSet rest) :=
    GroundTypeNormalization.selectionSetLookupValid_of_selectionSetSemanticsReady
      (Selection.field responseName fieldName arguments directives
          selectionSet
        :: eraseCompleteScopedSelectionSet rest)
      hrawReady
  have hlookupNoDirectives :
      GroundTypeNormalization.selectionSetLookupValid schema execParent
        (Selection.field responseName fieldName arguments [] selectionSet
          :: eraseCompleteScopedSelectionSet rest) :=
    selectionSetLookupValid_field_head_clear_directives schema execParent
      responseName fieldName arguments directives selectionSet
      (eraseCompleteScopedSelectionSet rest) hrawLookup
  have hmergeNoDirectives :
      FieldMerge.fieldsInSetCanMerge schema execParent
        (Selection.field responseName fieldName arguments [] selectionSet
          :: eraseCompleteScopedSelectionSet rest) :=
    fieldsInSetCanMerge_field_head_clear_directives schema execParent
      responseName fieldName arguments directives selectionSet
      (eraseCompleteScopedSelectionSet rest)
      (by
        simpa [completeScopedSelectionSetCanMerge,
          eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection]
          using hmerge)
  have hsameField :
      matchedFieldName = fieldName :=
    GroundTypeNormalization.validFieldsWithResponseName_matching_same_field_of_canMerge_object_lookupValid
      schema execParent responseName fieldName arguments selectionSet
      (eraseCompleteScopedSelectionSet rest) hobject hlookupNoDirectives
      hmergeNoDirectives matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hvalidMatchedField
  subst matchedFieldName
  have hmatchedApplies :
      schema.typeIncludesObjectBool scopedSelection.lookupParent groundType =
        true :=
    completeScopedSelectionSetStaticFieldsWithResponseName_groundApplies
      schema boolCase groundType responseName rest hmatchesGround
      scopedSelection hscoped
  have hincludeValue :
      GroundTypeNormalization.executionValueObjectsInclude schema
        matchedFieldDefinition.outputType.namedType
        (store.resolve schema fieldName arguments
          (.object groundType identity)) :=
    GroundTypeNormalization.resolve_objectsInclude_of_static_lookupField
      schema store scopedSelection.lookupParent groundType identity fieldName
      arguments matchedFieldDefinition hschema hstore hmatchedApplies
      hmatchedLookup
  have hallow :
      directivesAllowIn boolCase matchedDirectives = true :=
    completeScopedSelectionSetStaticFieldsWithResponseName_mem_field_allowed
      schema boolCase groundType responseName rest scopedSelection
      responseName fieldName matchedArguments matchedDirectives
      matchedSubselections hscoped
      (by simp [hselectionShape])
  refine ⟨responseName, fieldName, matchedArguments, matchedDirectives,
    matchedSubselections, matchedFieldDefinition, hselectionShape, hallow,
    hmatchedLookup, ?_⟩
  simpa [DataModel.Store.resolvers] using hincludeValue

theorem executeSelectionSet_staticCollectCompleteScopedSelectionSet_field_allowed_of_value_includes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat)
    (execParent lookupParent groundType : Name)
    (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (rest : List CompleteScopedSelection) :
    schema.objectType execParent ->
    schema.typeIncludesObjectBool execParent groundType = true ->
    completeScopedSelectionSetSemanticsReady schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetLookupValid schema
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetCanMerge schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetGroundApplies schema groundType
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (eraseCompleteScopedSelectionSet
          ({ lookupParent := lookupParent,
             selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
            :: rest)) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    (∀ execFieldDefinition lookupFieldDefinition,
      schema.lookupField execParent fieldName = some execFieldDefinition ->
      schema.lookupField lookupParent fieldName = some lookupFieldDefinition ->
        GroundTypeNormalization.executionValueObjectsInclude schema
            lookupFieldDefinition.outputType.namedType
            (resolvers.resolve execParent fieldName arguments
              (.object groundType identity))
          ∧
        completeScopedFieldOutputValuesInclude schema boolCase
          (resolvers.resolve execParent fieldName arguments
            (.object groundType identity))
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName rest)) ->
    Execution.executeSelectionSet schema resolvers
        variableValues depth execParent (.object groundType identity)
        (staticCollectCompleteScopedSelectionSet schema
          (operationBoolVars operation) groundType
          boolCase
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName rest))
      =
      Execution.executeSelectionSet schema resolvers
        variableValues depth execParent (.object groundType identity)
        (eraseCompleteScopedSelectionSet
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName rest)) ->
    (∀ childDepth runtimeType childIdentity,
      childDepth < depth - 1 ->
      schema.typeIncludesObjectBool
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          runtimeType = true ->
        Execution.executeSelectionSet schema resolvers
          variableValues childDepth runtimeType
          (.object runtimeType childIdentity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType boolCase
            (selectionSet
              ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (completeScopedSelectionSetStaticFieldsWithResponseName
                    schema boolCase groundType responseName rest))))
        =
        Execution.executeSelectionSet schema resolvers
          variableValues childDepth runtimeType
          (.object runtimeType childIdentity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (completeScopedSelectionSetStaticFieldsWithResponseName
                  schema boolCase groundType responseName rest)))) ->
      Execution.executeSelectionSet schema resolvers
          variableValues depth execParent (.object groundType identity)
          (staticCollectCompleteScopedSelectionSet schema
            (operationBoolVars operation) groundType
            boolCase
            ({ lookupParent := lookupParent,
               selection :=
                Selection.field responseName fieldName arguments directives
                  selectionSet }
              :: rest))
        =
      Execution.executeSelectionSet schema resolvers
        variableValues depth execParent (.object groundType identity)
        (eraseCompleteScopedSelectionSet
          ({ lookupParent := lookupParent,
             selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
            :: rest)) := by
  intro hobject hground hready hlookup hmerge happlies hagrees hsourceVars
    hallow hvalueIncludes hfiltered hchildren
  cases depth with
  | zero =>
      simp [Execution.executeSelectionSet,
        GroundTypeNormalization.executeCollectedFields_zero]
  | succ fieldDepth =>
      rcases
          completeScopedFieldHead_lookupPair_of_semanticsReady_lookupValid
            schema execParent lookupParent responseName fieldName arguments
            directives selectionSet rest hready hlookup with
        ⟨execFieldDefinition, lookupFieldDefinition, hexecLookup,
          hlookupField⟩
      let normalizedSelectionSet :=
        normalizeForTypeIn schema
          (operationBoolVars operation) boolCase
          lookupFieldDefinition.outputType.namedType selectionSet
      let normalizedRest :=
        staticCollectCompleteScopedSelectionSet schema
          (operationBoolVars operation) groundType boolCase
          rest
      let normalizedField : Execution.ExecutableField := {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := normalizedSelectionSet
      }
      let sourceField : Execution.ExecutableField := {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      }
      rcases
          GroundTypeNormalization.collectFields_field_head_exists schema
            variableValues execParent (.object groundType identity)
            responseName fieldName arguments normalizedSelectionSet
            normalizedRest with
        ⟨normalizedFields, normalizedTail, hnormalizedCollectRaw⟩
      have hnormalizedCollect :
          Execution.collectFields schema variableValues execParent
              (.object groundType identity)
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase
                ({ lookupParent := lookupParent,
                   selection :=
                    Selection.field responseName fieldName arguments
                      directives selectionSet }
                  :: rest))
            =
          (responseName, normalizedField :: normalizedFields)
            :: normalizedTail := by
        rw [staticCollectCompleteScopedSelectionSet,
          staticCollectCompleteScopedSelection]
        rw [staticCollectForGround_field_allowed schema
          (operationBoolVars operation) lookupParent
          groundType responseName fieldName boolCase arguments directives
          selectionSet [] hallow]
        simp [hlookupField, staticCollectForGround]
        simpa [normalizedSelectionSet, normalizedRest, normalizedField] using
          hnormalizedCollectRaw
      have hsourceVarsRaw :
          ∀ varName,
            varName ∈ selectionSetBooleanVariables
              (Selection.field responseName fieldName arguments directives
                  selectionSet
                :: eraseCompleteScopedSelectionSet rest) ->
            varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hsourceVars varName
          (by simpa [eraseCompleteScopedSelectionSet,
            eraseCompleteScopedSelection] using hmem)
      rcases
          collectFields_field_directives_allowed_exists_of_case schema
            variableValues operation execParent (.object groundType identity)
            boolCase responseName fieldName arguments directives
            selectionSet (eraseCompleteScopedSelectionSet rest) hagrees
            hsourceVarsRaw hallow with
        ⟨sourceFields, sourceTail, hsourceCollectRaw⟩
      have hsourceCollect :
          Execution.collectFields schema variableValues execParent
              (.object groundType identity)
              (eraseCompleteScopedSelectionSet
                ({ lookupParent := lookupParent,
                   selection :=
                    Selection.field responseName fieldName arguments
                      directives selectionSet }
                  :: rest))
            =
          (responseName, sourceField :: sourceFields) :: sourceTail := by
        simpa [eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
          sourceField] using hsourceCollectRaw
      have hnormalizedProjection :=
        mergedFieldSelectionSet_staticCollectCompleteScoped_field_head_eq_staticFields
          schema variableValues (operationBoolVars operation)
          execParent lookupParent groundType (.object groundType identity)
          boolCase responseName fieldName arguments directives selectionSet
          rest lookupFieldDefinition normalizedFields normalizedTail hallow
          hlookupField hnormalizedCollect
      have hsourceProjection :=
        mergedFieldSelectionSet_source_completeScoped_field_head_eq_staticFields
          schema variableValues operation execParent lookupParent groundType
          identity boolCase responseName fieldName arguments directives
          selectionSet rest sourceFields sourceTail hagrees hsourceVars hallow
          hsourceCollect
      have hvalueIncludes' :=
        hvalueIncludes execFieldDefinition lookupFieldDefinition hexecLookup
          hlookupField
      have hheadInclude :
          GroundTypeNormalization.executionValueObjectsInclude schema
            lookupFieldDefinition.outputType.namedType
            (resolvers.resolve execParent fieldName arguments
              (.object groundType identity)) :=
        hvalueIncludes'.1
      have hmatchesInclude :
          completeScopedFieldOutputValuesInclude schema boolCase
            (resolvers.resolve execParent fieldName arguments
              (.object groundType identity))
            (completeScopedSelectionSetStaticFieldsWithResponseName schema
              boolCase groundType responseName rest) :=
        hvalueIncludes'.2
      have hreturn :
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
            =
          execFieldDefinition.outputType.namedType :=
        by
          simp [Schema.fieldReturnType?, hexecLookup]
      have hcomplete :
          Execution.completeValue schema resolvers
              variableValues fieldDepth
              ((schema.fieldReturnType? execParent fieldName).getD fieldName)
              (Execution.mergedFieldSelectionSet
                (normalizedField :: normalizedFields))
              (resolvers.resolve execParent fieldName arguments
                (.object groundType identity))
            =
          Execution.completeValue schema resolvers
            variableValues fieldDepth
            ((schema.fieldReturnType? execParent fieldName).getD fieldName)
            (Execution.mergedFieldSelectionSet
              (sourceField :: sourceFields))
            (resolvers.resolve execParent fieldName arguments
              (.object groundType identity)) := by
        rw [hnormalizedProjection, hsourceProjection, hreturn]
        exact
          completeValue_normalizeForTypeIn_staticScoped_eq_of_valueObjectsInclude_lt
            schema resolvers variableValues hschema fieldDepth
            execFieldDefinition.outputType.namedType
            lookupFieldDefinition.outputType.namedType groundType
            (operationBoolVars operation) boolCase
            selectionSet
            (completeScopedSelectionSetStaticFieldsWithResponseName schema
              boolCase groundType responseName rest)
            (resolvers.resolve execParent fieldName arguments
              (.object groundType identity))
            hheadInclude hmatchesInclude
            (by
              intro childDepth runtimeType childIdentity hlt hinclude
              exact hchildren childDepth runtimeType childIdentity
                (by simpa using hlt)
                (by simpa [hreturn] using hinclude))
      have hnormalizedTailCollect :
          Execution.collectFields schema variableValues execParent
              (.object groundType identity)
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase
                (completeScopedSelectionSetWithoutFieldsWithResponseName
                  schema responseName rest))
            =
          normalizedTail := by
        have hfilteredCollect :=
          collectFields_withoutFieldsWithResponseName_eq_sourceRest_of_cons_directives
            schema variableValues execParent (.object groundType identity)
            responseName (normalizedField :: normalizedFields)
            normalizedTail
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              ({ lookupParent := lookupParent,
                 selection :=
                  Selection.field responseName fieldName arguments directives
                    selectionSet }
                :: rest))
            hnormalizedCollect
        rw [staticCollectCompleteScopedSelectionSet_withoutFieldsWithResponseName]
          at hfilteredCollect
        simpa [completeScopedSelectionSetWithoutFieldsWithResponseName,
          staticCollectCompleteScopedSelectionSet,
          staticCollectCompleteScopedSelection,
          staticCollectForGround] using hfilteredCollect
      have hsourceTailCollect :
          Execution.collectFields schema variableValues execParent
              (.object groundType identity)
              (eraseCompleteScopedSelectionSet
                (completeScopedSelectionSetWithoutFieldsWithResponseName
                  schema responseName rest))
            =
          sourceTail := by
        have hsourceTailRaw :=
          collectFields_withoutFieldsWithResponseName_fieldHead_rest_eq_sourceRest_directives
            schema variableValues execParent (.object groundType identity)
            responseName fieldName arguments directives selectionSet
            (eraseCompleteScopedSelectionSet rest) sourceFields sourceTail
            (by simpa [sourceField] using hsourceCollectRaw)
        simpa [eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName]
          using hsourceTailRaw
      have htailCollected :
          Execution.executeCollectedFields schema resolvers
              variableValues (fieldDepth + 1) (.object groundType identity)
              normalizedTail
            =
          Execution.executeCollectedFields schema resolvers
            variableValues (fieldDepth + 1) (.object groundType identity)
            sourceTail := by
        simpa [Execution.executeSelectionSet, hnormalizedTailCollect,
          hsourceTailCollect] using hfiltered
      simpa [normalizedField, sourceField] using
        GroundTypeNormalization.executeSelectionSet_field_head_same_group_eq_of_completeValue
          schema resolvers variableValues fieldDepth execParent
          (.object groundType identity) responseName fieldName arguments
          normalizedSelectionSet selectionSet
          (staticCollectCompleteScopedSelectionSet schema
            (operationBoolVars operation) groundType
            boolCase
            ({ lookupParent := lookupParent,
               selection :=
                Selection.field responseName fieldName arguments directives
                  selectionSet }
              :: rest))
          (eraseCompleteScopedSelectionSet
            ({ lookupParent := lookupParent,
               selection :=
                Selection.field responseName fieldName arguments directives
                  selectionSet }
              :: rest))
          normalizedFields sourceFields normalizedTail sourceTail
          hnormalizedCollect hsourceCollect hcomplete htailCollected

theorem executeSelectionSet_staticCollectCompleteScopedSelectionSet_field_allowed_on_store_of_recursions
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (depth : Nat)
    (execParent lookupParent groundType : Name)
    (identity : DataModel.ObjectPath)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (rest : List CompleteScopedSelection) :
    schema.objectType execParent ->
    schema.typeIncludesObjectBool execParent groundType = true ->
    completeScopedSelectionSetSemanticsReady schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetLookupValid schema
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetCanMerge schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetGroundApplies schema groundType
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (eraseCompleteScopedSelectionSet
          ({ lookupParent := lookupParent,
             selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
            :: rest)) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object groundType identity)
        (staticCollectCompleteScopedSelectionSet schema
          (operationBoolVars operation) groundType
          boolCase
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName rest))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object groundType identity)
        (eraseCompleteScopedSelectionSet
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName rest)) ->
    (∀ childDepth runtimeType childIdentity,
      childDepth < depth - 1 ->
      schema.typeIncludesObjectBool
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          runtimeType = true ->
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth runtimeType
          (.object runtimeType childIdentity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType boolCase
            (selectionSet
              ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (completeScopedSelectionSetStaticFieldsWithResponseName
                    schema boolCase groundType responseName rest))))
        =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth runtimeType
          (.object runtimeType childIdentity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (completeScopedSelectionSetStaticFieldsWithResponseName
                  schema boolCase groundType responseName rest)))) ->
      Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth execParent (.object groundType identity)
          (staticCollectCompleteScopedSelectionSet schema
            (operationBoolVars operation) groundType
            boolCase
            ({ lookupParent := lookupParent,
               selection :=
                Selection.field responseName fieldName arguments directives
                  selectionSet }
              :: rest))
        =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object groundType identity)
        (eraseCompleteScopedSelectionSet
          ({ lookupParent := lookupParent,
             selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
            :: rest)) := by
  intro hobject hground hready hlookup hmerge happlies hagrees hsourceVars
    hallow hfiltered hchildren
  apply
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_field_allowed_of_value_includes
      schema (store.resolvers schema) variableValues operation hschema depth
      execParent lookupParent groundType identity boolCase responseName
      fieldName arguments directives selectionSet rest hobject hground
      hready hlookup hmerge happlies hagrees hsourceVars hallow
  · intro execFieldDefinition lookupFieldDefinition hexecLookup hlookupField
    have hheadApplies :
        schema.typeIncludesObjectBool lookupParent groundType = true :=
      happlies
        { lookupParent := lookupParent,
          selection :=
            Selection.field responseName fieldName arguments directives
              selectionSet }
        (by simp)
    have hheadInclude :
        GroundTypeNormalization.executionValueObjectsInclude schema
          lookupFieldDefinition.outputType.namedType
          ((store.resolvers schema).resolve execParent fieldName arguments
            (.object groundType identity)) := by
      rw [GroundTypeNormalization.store_resolvers_parentType_insensitive
        schema store execParent lookupParent fieldName arguments
        (.object groundType identity)]
      simpa [DataModel.Store.resolvers] using
        GroundTypeNormalization.resolve_objectsInclude_of_static_lookupField
          schema store lookupParent groundType identity fieldName arguments
          lookupFieldDefinition hschema hstore hheadApplies hlookupField
    have hmatchesInclude :
        completeScopedFieldOutputValuesInclude schema boolCase
          ((store.resolvers schema).resolve execParent fieldName arguments
            (.object groundType identity))
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName rest) :=
      completeScopedSelectionSetStaticFieldsWithResponseName_valuesInclude_on_store
        schema store hschema hstore execParent lookupParent groundType
        identity boolCase responseName fieldName arguments directives
        selectionSet rest hobject hground hready hlookup hmerge
        (completeScopedSelectionSetGroundApplies_tail happlies)
    exact ⟨hheadInclude, hmatchesInclude⟩
  · exact hfiltered
  · exact hchildren

def completeScopedResolverFieldValuesInclude {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity) :
    Prop :=
  ∀ (_depth : Nat) (execParent lookupParent groundType : Name)
    (identity : ObjectIdentity) (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection),
    schema.objectType execParent ->
    schema.typeIncludesObjectBool execParent groundType = true ->
    completeScopedSelectionSetSemanticsReady schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetLookupValid schema
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetCanMerge schema execParent
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    completeScopedSelectionSetGroundApplies schema groundType
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest) ->
    directivesAllowIn boolCase directives = true ->
    ∀ execFieldDefinition lookupFieldDefinition,
      schema.lookupField execParent fieldName = some execFieldDefinition ->
      schema.lookupField lookupParent fieldName = some lookupFieldDefinition ->
        GroundTypeNormalization.executionValueObjectsInclude schema
            lookupFieldDefinition.outputType.namedType
            (resolvers.resolve execParent fieldName arguments
              (.object groundType identity))
          ∧
        completeScopedFieldOutputValuesInclude schema boolCase
          (resolvers.resolve execParent fieldName arguments
            (.object groundType identity))
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName rest)

theorem executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hresolverIncludes :
      completeScopedResolverFieldValuesInclude schema resolvers) :
    ∀ depth execParent groundType (identity : ObjectIdentity) boolCase
      scopedSelections,
      schema.objectType execParent ->
      schema.typeIncludesObjectBool execParent groundType = true ->
      completeScopedSelectionSetSemanticsReady schema execParent
        scopedSelections ->
      completeScopedSelectionSetLookupValid schema scopedSelections ->
      completeScopedSelectionSetCanMerge schema execParent scopedSelections ->
      completeScopedSelectionSetGroundApplies schema groundType
        scopedSelections ->
      variableValuesAgreeWithCase variableValues boolCase
        (operationBoolVars operation) ->
      (∀ varName,
        varName ∈ selectionSetBooleanVariables
            (eraseCompleteScopedSelectionSet scopedSelections) ->
          varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
        Execution.executeSelectionSet schema resolvers
            variableValues depth execParent (.object groundType identity)
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation)
              groundType boolCase scopedSelections)
          =
        Execution.executeSelectionSet schema resolvers
          variableValues depth execParent (.object groundType identity)
          (eraseCompleteScopedSelectionSet scopedSelections)
  | depth, execParent, groundType, identity, boolCase, [], _hobject,
    _hground, _hready, _hlookup, _hmerge, _happlies, _hagrees,
    _hsourceVars => by
      simp [staticCollectCompleteScopedSelectionSet,
        eraseCompleteScopedSelectionSet, Execution.executeSelectionSet,
        Execution.collectFields]
  | depth, execParent, groundType, identity, boolCase,
      scopedSelection :: rest, hobject, hground, hready, hlookup, hmerge,
      happlies, hagrees, hsourceVars => by
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field responseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · apply
                  executeSelectionSet_staticCollectCompleteScopedSelectionSet_field_skipped_execution_case
                    schema resolvers variableValues operation
                    depth execParent lookupParent groundType identity
                    boolCase responseName fieldName arguments directives
                    selectionSet rest hagrees hsourceVars hallow
                exact
                  executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
                    schema resolvers variableValues operation hschema
                    hresolverIncludes depth
                    execParent groundType identity boolCase rest hobject
                    hground
                    (completeScopedSelectionSetSemanticsReady_tail hready)
                    (completeScopedSelectionSetLookupValid_tail hlookup)
                    (completeScopedSelectionSetCanMerge_tail schema
                      execParent
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field responseName fieldName arguments
                            directives selectionSet }
                      rest hmerge)
                    (completeScopedSelectionSetGroundApplies_tail happlies)
                    hagrees
                    (by
                      intro varName hmem
                      exact hsourceVars varName
                        (by
                          simp [eraseCompleteScopedSelectionSet,
                            eraseCompleteScopedSelection,
                            selectionSetBooleanVariables, hmem]))
              · apply
                  executeSelectionSet_staticCollectCompleteScopedSelectionSet_field_allowed_of_value_includes
                    schema resolvers variableValues operation hschema depth
                    execParent lookupParent groundType identity boolCase
                    responseName fieldName arguments directives selectionSet
                    rest hobject hground hready hlookup hmerge happlies
                    hagrees hsourceVars hallow
                    (hresolverIncludes depth execParent lookupParent
                      groundType identity boolCase responseName fieldName
                      arguments directives selectionSet rest hobject hground
                      hready hlookup hmerge happlies hallow)
                · exact
                    executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
                      schema resolvers variableValues operation hschema
                      hresolverIncludes
                      depth execParent groundType identity boolCase
                      (completeScopedSelectionSetWithoutFieldsWithResponseName
                        schema responseName rest)
                      hobject hground
                      (completeScopedSelectionSetWithoutFieldsWithResponseName_semanticsReady
                        schema execParent responseName rest
                        (completeScopedSelectionSetSemanticsReady_tail hready))
                      (completeScopedSelectionSetWithoutFieldsWithResponseName_lookupValid
                        schema responseName rest
                        (completeScopedSelectionSetLookupValid_tail hlookup))
                      (completeScopedSelectionSetWithoutFieldsWithResponseName_canMerge
                        schema execParent responseName rest
                        (completeScopedSelectionSetCanMerge_tail schema
                          execParent
                          { lookupParent := lookupParent,
                            selection :=
                              Selection.field responseName fieldName
                                arguments directives selectionSet }
                          rest hmerge))
                      (completeScopedSelectionSetWithoutFieldsWithResponseName_groundApplies
                        schema groundType responseName rest
                        (completeScopedSelectionSetGroundApplies_tail
                          happlies))
                      hagrees
                      (by
                        intro varName hmem
                        have hmemRaw :
                            varName ∈ selectionSetBooleanVariables
                              (withoutFieldsWithResponseName schema
                                responseName
                                (eraseCompleteScopedSelectionSet rest)) := by
                          simpa [eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName]
                            using hmem
                        exact hsourceVars varName
                          (by
                            simp [eraseCompleteScopedSelectionSet,
                              eraseCompleteScopedSelection,
                              selectionSetBooleanVariables]
                            exact Or.inr
                              (selectionSetBooleanVariables_withoutFieldsWithResponseName_mem
                                schema responseName varName
                                (eraseCompleteScopedSelectionSet rest)
                                hmemRaw)))
                · intro childDepth runtimeType childIdentity hlt hinclude
                  let childSelectionSet : List Selection :=
                    selectionSet ++
                      mergeSelectionSets
                        (eraseCompleteScopedSelectionSet
                          (completeScopedSelectionSetStaticFieldsWithResponseName
                            schema boolCase groundType responseName rest))
                  have hchildObjectBool :
                      objectTypeNameBool schema runtimeType = true := by
                    exact GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
                      schema
                      (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                        hschema
                        ((schema.fieldReturnType? execParent fieldName).getD
                          fieldName)
                        runtimeType (List.contains_iff_mem.mp hinclude))
                  have hchildObject : schema.objectType runtimeType := by
                    exact
                      GroundTypeNormalization.objectType_of_objectTypeNameBool_eq_true
                        schema hchildObjectBool
                  have hchildGround :
                      schema.typeIncludesObjectBool runtimeType runtimeType =
                        true :=
                    GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
                      schema hchildObjectBool
                  rcases
                      completeScopedFieldHead_lookupPair_of_semanticsReady_lookupValid
                        schema execParent lookupParent responseName fieldName
                        arguments directives selectionSet rest hready hlookup with
                    ⟨execFieldDefinition, _lookupFieldDefinition,
                      hexecLookup, _hlookupField⟩
                  have hreturn :
                      ((schema.fieldReturnType? execParent fieldName).getD
                          fieldName)
                        =
                      execFieldDefinition.outputType.namedType := by
                    simp [Schema.fieldReturnType?, hexecLookup]
                  have hrawReady :
                      GroundTypeNormalization.selectionSetSemanticsReady schema
                        execParent
                        (Selection.field responseName fieldName arguments
                            directives selectionSet
                          :: eraseCompleteScopedSelectionSet rest) := by
                    simpa [completeScopedSelectionSetSemanticsReady,
                      eraseCompleteScopedSelectionSet,
                      eraseCompleteScopedSelection] using hready
                  have hrawLookup :
                      GroundTypeNormalization.selectionSetLookupValid schema
                        execParent
                        (Selection.field responseName fieldName arguments
                            directives selectionSet
                          :: eraseCompleteScopedSelectionSet rest) :=
                    GroundTypeNormalization.selectionSetLookupValid_of_selectionSetSemanticsReady
                      (Selection.field responseName fieldName arguments
                          directives selectionSet
                        :: eraseCompleteScopedSelectionSet rest)
                      hrawReady
                  have hrawMerge :
                      FieldMerge.fieldsInSetCanMerge schema execParent
                        (Selection.field responseName fieldName arguments
                            directives selectionSet
                          :: eraseCompleteScopedSelectionSet rest) := by
                    simpa [completeScopedSelectionSetCanMerge,
                      eraseCompleteScopedSelectionSet,
                      eraseCompleteScopedSelection] using hmerge
                  have hincludeExec :
                      schema.typeIncludesObjectBool
                          execFieldDefinition.outputType.namedType
                          runtimeType =
                        true := by
                    simpa [hreturn] using hinclude
                  have hchildReadyRaw :
                      GroundTypeNormalization.selectionSetSemanticsReady schema
                        runtimeType childSelectionSet := by
                    have hstaticReady :=
                      selectionSetSemanticsReady_field_staticScoped_merged_object
                        schema boolCase execParent groundType responseName
                        fieldName runtimeType arguments directives
                        selectionSet (eraseCompleteScopedSelectionSet rest)
                        execFieldDefinition hobject hrawReady hrawLookup
                        hrawMerge hexecLookup hground hincludeExec
                    simpa [childSelectionSet,
                      eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                        schema boolCase execParent groundType responseName
                        rest] using hstaticReady
                  have hchildLookup :
                      completeScopedSelectionSetLookupValid schema
                        (completeScopedSelectionSet runtimeType
                          childSelectionSet) :=
                    (completeScopedSelectionSetLookupValid_completeScopedSelectionSet
                      schema runtimeType childSelectionSet).mpr
                      (GroundTypeNormalization.selectionSetLookupValid_of_selectionSetSemanticsReady
                        childSelectionSet hchildReadyRaw)
                  have hchildMergeRaw :
                      FieldMerge.fieldsInSetCanMerge schema runtimeType
                        childSelectionSet := by
                    have hstaticMerge :=
                      fieldsInSetCanMerge_field_staticScoped_merged_object
                        schema boolCase execParent groundType responseName
                        fieldName runtimeType arguments directives
                        selectionSet (eraseCompleteScopedSelectionSet rest)
                        execFieldDefinition hobject hrawLookup hrawMerge
                        hexecLookup hground
                    simpa [childSelectionSet,
                      eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                        schema boolCase execParent groundType responseName
                        rest] using hstaticMerge
                  have hchildSourceVars :
                      ∀ varName,
                        varName ∈ selectionSetBooleanVariables
                            childSelectionSet ->
                        varName ∈ selectionSetBooleanVariables
                          operation.selectionSet := by
                    intro varName hmem
                    have hmem' :
                        varName ∈ selectionSetBooleanVariables
                          (selectionSet ++
                            mergeSelectionSets
                              (eraseCompleteScopedSelectionSet
                                (staticScopedFieldsWithResponseName schema
                                  boolCase execParent groundType
                                  responseName
                                  (eraseCompleteScopedSelectionSet rest)))) := by
                      simpa [childSelectionSet,
                        eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                          schema boolCase execParent groundType responseName
                          rest] using hmem
                    exact
                      sourceSelectionSetVariables_field_staticScoped_merged
                        operation schema boolCase execParent groundType
                        responseName fieldName arguments directives
                        selectionSet (eraseCompleteScopedSelectionSet rest)
                        (by
                          intro candidate hcandidate
                          exact hsourceVars candidate
                            (by simpa [eraseCompleteScopedSelectionSet,
                              eraseCompleteScopedSelection] using hcandidate))
                        varName hmem'
                  have hchildGroundApplies :
                      completeScopedSelectionSetGroundApplies schema
                        runtimeType
                        (completeScopedSelectionSet runtimeType
                          childSelectionSet) := by
                    intro scopedSelection hmem
                    have hparent :=
                      completeScopedSelectionSet_lookupParent_eq hmem
                    rw [hparent]
                    exact hchildGround
                  have hchildEq :=
                    executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
                      schema resolvers variableValues operation hschema
                      hresolverIncludes
                      childDepth runtimeType runtimeType childIdentity
                      boolCase
                      (completeScopedSelectionSet runtimeType
                        childSelectionSet)
                      hchildObject hchildGround
                      ((completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
                        schema runtimeType runtimeType
                        childSelectionSet).mpr hchildReadyRaw)
                      hchildLookup
                      ((completeScopedSelectionSetCanMerge_completeScopedSelectionSet
                        schema runtimeType runtimeType
                        childSelectionSet).mpr hchildMergeRaw)
                      hchildGroundApplies hagrees
                      (by
                        intro varName hmem
                        exact hchildSourceVars varName
                          (by
                            simpa [eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
                              using hmem))
                  simpa [childSelectionSet,
                    staticCollectCompleteScopedSelectionSet_completeScopedSelectionSet,
                    eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
                    using hchildEq
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_none_skipped_execution_case
                        schema resolvers variableValues
                        operation depth execParent lookupParent groundType
                        identity boolCase directives selectionSet rest
                        hagrees hsourceVars hallow
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
                        schema resolvers variableValues operation hschema
                        hresolverIncludes
                        depth execParent groundType identity boolCase rest
                        hobject hground
                        (completeScopedSelectionSetSemanticsReady_tail hready)
                        (completeScopedSelectionSetLookupValid_tail hlookup)
                        (completeScopedSelectionSetCanMerge_tail schema
                          execParent
                          { lookupParent := lookupParent,
                            selection :=
                              Selection.inlineFragment none directives
                                selectionSet }
                          rest hmerge)
                        (completeScopedSelectionSetGroundApplies_tail happlies)
                        hagrees
                        (by
                          intro varName hmem
                          exact hsourceVars varName
                            (by
                              simp [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection,
                                selectionSetBooleanVariables, hmem]))
                  · apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_none_allowed_flatten_case
                        schema resolvers variableValues
                        operation depth execParent lookupParent groundType
                        identity boolCase directives selectionSet rest
                        hagrees hsourceVars hallow
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
                        schema resolvers variableValues operation hschema
                        hresolverIncludes
                        depth execParent groundType identity boolCase
                        (completeScopedSelectionSet lookupParent selectionSet
                          ++ rest)
                        hobject hground
                        (completeScopedSelectionSetSemanticsReady_append
                          ((completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
                            schema execParent lookupParent selectionSet).mpr
                            (by
                              have hheadReady :
                                  GroundTypeNormalization.selectionSemanticsReady
                                    schema execParent
                                    (Selection.inlineFragment none directives
                                      selectionSet) := by
                                unfold completeScopedSelectionSetSemanticsReady at hready
                                unfold GroundTypeNormalization.selectionSetSemanticsReady at hready
                                exact hready _ (by
                                  simp [eraseCompleteScopedSelectionSet,
                                    eraseCompleteScopedSelection])
                              simpa [GroundTypeNormalization.selectionSemanticsReady] using
                                hheadReady))
                          (completeScopedSelectionSetSemanticsReady_tail
                            hready))
                        (completeScopedSelectionSetLookupValid_append
                          ((completeScopedSelectionSetLookupValid_completeScopedSelectionSet
                            schema lookupParent selectionSet).mpr
                            (by
                              have hheadLookup :
                                  GroundTypeNormalization.selectionLookupValid
                                    schema lookupParent
                                    (Selection.inlineFragment none directives
                                      selectionSet) :=
                                hlookup
                                  { lookupParent := lookupParent,
                                    selection :=
                                      Selection.inlineFragment none directives
                                        selectionSet }
                                  (by simp)
                              simpa [GroundTypeNormalization.selectionLookupValid] using
                                hheadLookup))
                          (completeScopedSelectionSetLookupValid_tail hlookup))
                        (by
                          have hmergeNoDirectives :
                              FieldMerge.fieldsInSetCanMerge schema execParent
                                (Selection.inlineFragment none [] selectionSet
                                  :: eraseCompleteScopedSelectionSet rest) :=
                            fieldsInSetCanMerge_inline_none_head_clear_directives
                              schema execParent directives selectionSet
                              (eraseCompleteScopedSelectionSet rest)
                              (by
                                simpa [completeScopedSelectionSetCanMerge,
                                  eraseCompleteScopedSelectionSet,
                                  eraseCompleteScopedSelection] using hmerge)
                          simpa [completeScopedSelectionSetCanMerge,
                            eraseCompleteScopedSelectionSet_append,
                            eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
                            GroundTypeNormalization.fieldsInSetCanMerge_inlineFragment_none_flatten
                              schema execParent selectionSet
                              (eraseCompleteScopedSelectionSet rest)
                              hmergeNoDirectives)
                        (completeScopedSelectionSetGroundApplies_append
                          (by
                            intro scopedSelection hmem
                            have hparent :=
                              completeScopedSelectionSet_lookupParent_eq hmem
                            rw [hparent]
                            exact happlies
                              { lookupParent := lookupParent,
                                selection :=
                                  Selection.inlineFragment none directives
                                    selectionSet }
                              (by simp))
                          (completeScopedSelectionSetGroundApplies_tail
                            happlies))
                        hagrees
                        (by
                          intro varName hmem
                          have hmemRaw :
                              varName ∈ selectionSetBooleanVariables
                                (selectionSet
                                  ++ eraseCompleteScopedSelectionSet rest) := by
                            simpa [eraseCompleteScopedSelectionSet_append,
                              eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
                              using hmem
                          have hsourceVarsRaw :
                              ∀ varName,
                                varName ∈ selectionSetBooleanVariables
                                  (Selection.inlineFragment none directives
                                      selectionSet
                                    :: eraseCompleteScopedSelectionSet rest) ->
                                varName ∈
                                  selectionSetBooleanVariables
                                    operation.selectionSet := by
                            intro candidate hcandidate
                            exact hsourceVars candidate
                              (by simpa [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection] using hcandidate)
                          rcases
                              List.mem_append.mp
                                (by
                                  simpa [selectionSetBooleanVariables_append]
                                    using hmemRaw) with hchild | htail
                          · exact
                              sourceSelectionSetVariables_inline_child
                                operation none directives selectionSet
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName hchild
                          · exact
                              sourceSelectionSetVariables_tail operation
                                (Selection.inlineFragment none directives
                                  selectionSet)
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName htail)
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_some_skipped_execution_case
                        schema resolvers variableValues
                        operation depth execParent lookupParent groundType
                        typeCondition identity boolCase directives
                        selectionSet rest hagrees hsourceVars hbranch
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
                        schema resolvers variableValues operation hschema
                        hresolverIncludes
                        depth execParent groundType identity boolCase rest
                        hobject hground
                        (completeScopedSelectionSetSemanticsReady_tail hready)
                        (completeScopedSelectionSetLookupValid_tail hlookup)
                        (completeScopedSelectionSetCanMerge_tail schema
                          execParent
                          { lookupParent := lookupParent,
                            selection :=
                              Selection.inlineFragment (some typeCondition)
                                directives selectionSet }
                          rest hmerge)
                        (completeScopedSelectionSetGroundApplies_tail happlies)
                        hagrees
                        (by
                          intro varName hmem
                          exact hsourceVars varName
                            (by
                              simp [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection,
                                selectionSetBooleanVariables, hmem]))
                  · have hallow :
                        directivesAllowIn boolCase
                            directives =
                          true := by
                      cases hallow' :
                          directivesAllowIn boolCase
                            directives
                      · simp [hallow'] at hbranch
                      · rfl
                    have hincludes :
                        schema.typeIncludesObjectBool typeCondition
                            groundType =
                          true := by
                      cases hincludes' :
                          schema.typeIncludesObjectBool typeCondition
                            groundType
                      · simp [hallow, hincludes'] at hbranch
                      · rfl
                    apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_some_allowed_flatten_case
                        schema resolvers variableValues
                        operation depth execParent lookupParent groundType
                        typeCondition identity boolCase directives
                        selectionSet rest hagrees hsourceVars hallow hincludes
                    have hobjectBool :
                        objectTypeNameBool schema execParent = true :=
                      GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
                        schema hobject
                    have happly :
                        Execution.doesFragmentTypeApplyBool schema execParent
                            (.object groundType identity) typeCondition =
                          true := by
                      simpa [Execution.doesFragmentTypeApplyBool,
                        Execution.runtimeObjectType?] using hincludes
                    have hsource :
                        ∃ runtimeType identity',
                          (Execution.Value.object groundType identity :
                              Execution.Value ObjectIdentity)
                            = .object runtimeType identity'
                            ∧ schema.typeIncludesObjectBool execParent
                              runtimeType = true :=
                      ⟨groundType, identity, rfl, hground⟩
                    have hoverlap :
                        schema.typesOverlapBool execParent typeCondition =
                          true := by
                      rw [← GroundTypeNormalization.doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
                        schema hobjectBool hsource]
                      exact happly
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
                        schema resolvers variableValues operation hschema
                        hresolverIncludes
                        depth execParent groundType identity boolCase
                        (completeScopedSelectionSet typeCondition selectionSet
                          ++ rest)
                        hobject hground
                        (completeScopedSelectionSetSemanticsReady_append
                          ((completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
                            schema execParent typeCondition selectionSet).mpr
                            (by
                              have hheadReady :
                                  GroundTypeNormalization.selectionSemanticsReady
                                    schema execParent
                                    (Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet) := by
                                unfold completeScopedSelectionSetSemanticsReady at hready
                                unfold GroundTypeNormalization.selectionSetSemanticsReady at hready
                                exact hready _ (by
                                  simp [eraseCompleteScopedSelectionSet,
                                    eraseCompleteScopedSelection])
                              have hpair :
                                  GroundTypeNormalization.selectionSetLookupValid
                                    schema typeCondition selectionSet
                                    ∧
                                  (schema.typesOverlapBool execParent
                                      typeCondition = true ->
                                    GroundTypeNormalization.selectionSetSemanticsReady
                                      schema execParent selectionSet) := by
                                simpa [GroundTypeNormalization.selectionSemanticsReady] using
                                  hheadReady
                              exact hpair.2 hoverlap))
                          (completeScopedSelectionSetSemanticsReady_tail
                            hready))
                        (completeScopedSelectionSetLookupValid_append
                          ((completeScopedSelectionSetLookupValid_completeScopedSelectionSet
                            schema typeCondition selectionSet).mpr
                            (by
                              have hheadLookup :
                                  GroundTypeNormalization.selectionLookupValid
                                    schema lookupParent
                                    (Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet) :=
                                hlookup
                                  { lookupParent := lookupParent,
                                    selection :=
                                      Selection.inlineFragment
                                        (some typeCondition) directives
                                        selectionSet }
                                  (by simp)
                              simpa [GroundTypeNormalization.selectionLookupValid] using
                                hheadLookup))
                          (completeScopedSelectionSetLookupValid_tail hlookup))
                        (by
                          have hselectionParentLookup :
                              GroundTypeNormalization.selectionSetLookupValid
                                schema execParent selectionSet :=
                            GroundTypeNormalization.selectionSetLookupValid_of_selectionSetSemanticsReady
                              selectionSet
                              (by
                                have hheadReady :
                                    GroundTypeNormalization.selectionSemanticsReady
                                      schema execParent
                                      (Selection.inlineFragment
                                        (some typeCondition) directives
                                        selectionSet) := by
                                  unfold completeScopedSelectionSetSemanticsReady at hready
                                  unfold GroundTypeNormalization.selectionSetSemanticsReady at hready
                                  exact hready _ (by
                                    simp [eraseCompleteScopedSelectionSet,
                                      eraseCompleteScopedSelection])
                                have hpair :
                                    GroundTypeNormalization.selectionSetLookupValid
                                      schema typeCondition selectionSet
                                      ∧
                                    (schema.typesOverlapBool execParent
                                        typeCondition = true ->
                                      GroundTypeNormalization.selectionSetSemanticsReady
                                        schema execParent selectionSet) := by
                                  simpa [GroundTypeNormalization.selectionSemanticsReady] using
                                    hheadReady
                                exact hpair.2 hoverlap)
                          have hselectionTypeLookup :
                              GroundTypeNormalization.selectionSetLookupValid
                                schema typeCondition selectionSet := by
                            have hheadLookup :
                                GroundTypeNormalization.selectionLookupValid
                                  schema lookupParent
                                  (Selection.inlineFragment
                                    (some typeCondition) directives
                                    selectionSet) :=
                              hlookup
                                { lookupParent := lookupParent,
                                  selection :=
                                    Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet }
                                (by simp)
                            simpa [GroundTypeNormalization.selectionLookupValid] using
                              hheadLookup
                          have htailLookup :
                              GroundTypeNormalization.selectionSetLookupValid
                                schema execParent
                                (eraseCompleteScopedSelectionSet rest) :=
                            GroundTypeNormalization.selectionSetLookupValid_of_selectionSetSemanticsReady
                              (eraseCompleteScopedSelectionSet rest)
                              (completeScopedSelectionSetSemanticsReady_tail
                                hready)
                          have hmergeNoDirectives :
                              FieldMerge.fieldsInSetCanMerge schema execParent
                                (Selection.inlineFragment
                                    (some typeCondition) [] selectionSet
                                  :: eraseCompleteScopedSelectionSet rest) :=
                            fieldsInSetCanMerge_inline_some_head_clear_directives
                              schema execParent typeCondition directives
                              selectionSet
                              (eraseCompleteScopedSelectionSet rest)
                              (by
                                simpa [completeScopedSelectionSetCanMerge,
                                  eraseCompleteScopedSelectionSet,
                                  eraseCompleteScopedSelection] using hmerge)
                          simpa [completeScopedSelectionSetCanMerge,
                            eraseCompleteScopedSelectionSet_append,
                            eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
                            GroundTypeNormalization.fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
                              schema execParent typeCondition selectionSet
                              (eraseCompleteScopedSelectionSet rest) hschema
                              hobject hoverlap hselectionParentLookup
                              hselectionTypeLookup htailLookup
                              hmergeNoDirectives)
                        (completeScopedSelectionSetGroundApplies_append
                          (by
                            intro scopedSelection hmem
                            have hparent :=
                              completeScopedSelectionSet_lookupParent_eq hmem
                            rw [hparent]
                            exact hincludes)
                          (completeScopedSelectionSetGroundApplies_tail
                            happlies))
                        hagrees
                        (by
                          intro varName hmem
                          have hmemRaw :
                              varName ∈ selectionSetBooleanVariables
                                (selectionSet
                                  ++ eraseCompleteScopedSelectionSet rest) := by
                            simpa [eraseCompleteScopedSelectionSet_append,
                              eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
                              using hmem
                          have hsourceVarsRaw :
                              ∀ varName,
                                varName ∈ selectionSetBooleanVariables
                                  (Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet
                                    :: eraseCompleteScopedSelectionSet rest) ->
                                varName ∈
                                  selectionSetBooleanVariables
                                    operation.selectionSet := by
                            intro candidate hcandidate
                            exact hsourceVars candidate
                              (by simpa [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection] using hcandidate)
                          rcases
                              List.mem_append.mp
                                (by
                                  simpa [selectionSetBooleanVariables_append]
                                    using hmemRaw) with hchild | htail
                          · exact
                              sourceSelectionSetVariables_inline_child
                                operation (some typeCondition) directives
                                selectionSet
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName hchild
                          · exact
                              sourceSelectionSetVariables_tail operation
                                (Selection.inlineFragment
                                  (some typeCondition) directives
                                  selectionSet)
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName htail)
termination_by depth _execParent _groundType _identity _boolCase scopedSelections =>
  (depth, SelectionSet.size (eraseCompleteScopedSelectionSet scopedSelections))
decreasing_by
  all_goals
    try subst_vars
    try
      exact Prod.Lex.right _
        (eraseCompleteScopedSelectionSet_tail_size_lt
          { lookupParent := lookupParent,
            selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
          rest)
    try
      exact Prod.Lex.right _
        (eraseCompleteScopedSelectionSet_tail_size_lt
          { lookupParent := lookupParent,
            selection :=
              Selection.inlineFragment none directives selectionSet }
          rest)
    try
      exact Prod.Lex.right _
        (eraseCompleteScopedSelectionSet_tail_size_lt
          { lookupParent := lookupParent,
            selection :=
              Selection.inlineFragment (some typeCondition) directives
                selectionSet }
          rest)
    try
      exact Prod.Lex.right _
        (eraseCompleteScopedSelectionSet_inlineFragment_none_flatten_size_lt
          lookupParent selectionSet rest)
    try
      exact Prod.Lex.right _
        (eraseCompleteScopedSelectionSet_inlineFragment_some_flatten_size_lt
          lookupParent typeCondition selectionSet rest)
    try
      exact Prod.Lex.right _
        (eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName_size_lt_field_directives
          schema lookupParent responseName fieldName arguments directives
          selectionSet rest)
    try
      exact Prod.Lex.left _ _ (by omega)

theorem executeSelectionSet_staticCollectCompleteScopedSelectionSet_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema) :
    ∀ depth execParent groundType identity boolCase scopedSelections,
      schema.objectType execParent ->
      schema.typeIncludesObjectBool execParent groundType = true ->
      completeScopedSelectionSetSemanticsReady schema execParent
        scopedSelections ->
      completeScopedSelectionSetLookupValid schema scopedSelections ->
      completeScopedSelectionSetCanMerge schema execParent scopedSelections ->
      completeScopedSelectionSetGroundApplies schema groundType
        scopedSelections ->
      variableValuesAgreeWithCase variableValues boolCase
        (operationBoolVars operation) ->
      (∀ varName,
        varName ∈ selectionSetBooleanVariables
            (eraseCompleteScopedSelectionSet scopedSelections) ->
          varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
        Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues depth execParent (.object groundType identity)
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation)
              groundType boolCase scopedSelections)
          =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth execParent (.object groundType identity)
          (eraseCompleteScopedSelectionSet scopedSelections) := by
  refine
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
      schema (store.resolvers schema) variableValues operation hschema ?_
  unfold completeScopedResolverFieldValuesInclude
  intro depth execParent lookupParent groundType identity boolCase
    responseName fieldName arguments directives selectionSet rest hobject
    hground hready hlookup hmerge happlies hallow execFieldDefinition
    lookupFieldDefinition hexecLookup hlookupField
  have hheadApplies :
      schema.typeIncludesObjectBool lookupParent groundType = true :=
    happlies
      { lookupParent := lookupParent,
        selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
      (by simp)
  have hheadInclude :
      GroundTypeNormalization.executionValueObjectsInclude schema
        lookupFieldDefinition.outputType.namedType
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object groundType identity)) := by
    rw [GroundTypeNormalization.store_resolvers_parentType_insensitive
      schema store execParent lookupParent fieldName arguments
      (.object groundType identity)]
    simpa [DataModel.Store.resolvers] using
      GroundTypeNormalization.resolve_objectsInclude_of_static_lookupField
        schema store lookupParent groundType identity fieldName arguments
        lookupFieldDefinition hschema hstore hheadApplies hlookupField
  have hmatchesInclude :
      completeScopedFieldOutputValuesInclude schema boolCase
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object groundType identity))
        (completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName rest) :=
    completeScopedSelectionSetStaticFieldsWithResponseName_valuesInclude_on_store
      schema store hschema hstore execParent lookupParent groundType
      identity boolCase responseName fieldName arguments directives
      selectionSet rest hobject hground hready hlookup hmerge
      (completeScopedSelectionSetGroundApplies_tail happlies)
  exact ⟨hheadInclude, hmatchesInclude⟩


end CompleteNormalization

end NormalForm

end GraphQL
