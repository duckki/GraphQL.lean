import GraphQL.NormalForm.CompleteNormalization.ScopedResolverSemantics

/-!
Child completion and duplicate-field-group facts for complete normalization.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem completeValue_normalizeForTypeIn_eq_of_child
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (depth : Nat) (returnType : Name)
    (selectionSet : List Selection)
    (value : Execution.Value ObjectIdentity) :
    leafTypeNameBool schema returnType = false ->
    (∀ childDepth runtimeType identity,
      childDepth < depth ->
      runtimeType ∈ groundObjectTypesForType schema returnType ->
        Execution.executeSelectionSet schema resolvers variableValues childDepth
          runtimeType (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet)
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          selectionSet) ->
      Execution.completeValue schema resolvers variableValues depth returnType
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet)
          value
        =
      Execution.completeValue schema resolvers variableValues depth returnType
        selectionSet value := by
  intro hleafFalse hchild
  apply GroundTypeNormalization.completeValue_eq_of_child_object_lt_includes
    schema resolvers variableValues
  intro childDepth runtimeType identity hlt hinclude
  simpa [Execution.mergedFieldSelectionSet] using
    hchild childDepth runtimeType identity hlt
      (typeIncludesObjectBool_mem_groundObjectTypesForType schema returnType
        runtimeType hleafFalse hinclude)

theorem completeValue_normalizeForType_eq_of_child
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (returnType : Name)
    (selectionSet : List Selection)
    (value : Execution.Value ObjectIdentity) :
    leafTypeNameBool schema returnType = false ->
    (∀ childDepth runtimeType identity,
      childDepth < depth ->
      runtimeType ∈ groundObjectTypesForType schema returnType ->
        Execution.executeSelectionSet schema resolvers variableValues childDepth
          runtimeType (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType
            selectionSet)
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          selectionSet) ->
      Execution.completeValue schema resolvers variableValues depth returnType
          (normalizeForType schema
            (operationBoolVars operation) returnType
            selectionSet)
          value
        =
      Execution.completeValue schema resolvers variableValues depth returnType
        selectionSet value := by
  intro hleafFalse hchild
  apply GroundTypeNormalization.completeValue_eq_of_child_object_lt_includes
    schema resolvers variableValues
  intro childDepth runtimeType identity hlt hinclude
  simpa [Execution.mergedFieldSelectionSet] using
    hchild childDepth runtimeType identity hlt
      (typeIncludesObjectBool_mem_groundObjectTypesForType schema returnType
        runtimeType hleafFalse hinclude)

theorem fieldReturnType?_getD_eq_of_lookupField
    (schema : Schema) (lookupParent fieldName : Name)
    (fieldDefinition : FieldDefinition) :
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
      ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        =
      fieldDefinition.outputType.namedType := by
  intro hlookup
  simp [Schema.fieldReturnType?, hlookup]

theorem completeValue_eq_of_lookupField_leaf
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (lookupParent fieldName : Name)
    (fieldDefinition : FieldDefinition)
    (left right : List Selection)
    (value : Execution.Value ObjectIdentity) :
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    leafTypeNameBool schema fieldDefinition.outputType.namedType = true ->
      Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          left value
        =
      Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        right value := by
  intro hlookup hleaf
  rw [fieldReturnType?_getD_eq_of_lookupField schema lookupParent fieldName
    fieldDefinition hlookup]
  exact completeValue_eq_of_leafTypeNameBool schema resolvers variableValues
    fieldDefinition.outputType.namedType left right depth value hleaf

theorem completeValue_normalizeForTypeIn_eq_of_staticCollect_child
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (depth : Nat) (lookupParent fieldName : Name)
    (fieldDefinition : FieldDefinition)
    (selectionSet : List Selection)
    (value : Execution.Value ObjectIdentity) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    (∀ childDepth runtimeType identity,
      childDepth < depth ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          (staticCollectForGround schema variables runtimeType
            runtimeType boolCase selectionSet)
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          selectionSet) ->
      Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          (normalizeForTypeIn schema variables
            boolCase fieldDefinition.outputType.namedType selectionSet)
          value
        =
      Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        selectionSet value := by
  intro hschema hlookup hchild
  cases hleaf : leafTypeNameBool schema fieldDefinition.outputType.namedType with
  | true =>
      exact completeValue_eq_of_lookupField_leaf schema resolvers
        variableValues depth lookupParent fieldName fieldDefinition
        (normalizeForTypeIn schema variables
          boolCase fieldDefinition.outputType.namedType selectionSet)
        selectionSet value hlookup hleaf
  | false =>
      rw [fieldReturnType?_getD_eq_of_lookupField schema lookupParent
        fieldName fieldDefinition hlookup]
      apply completeValue_normalizeForTypeIn_eq_of_child
        schema resolvers variableValues variables boolCase depth
        fieldDefinition.outputType.namedType selectionSet value hleaf
      intro childDepth runtimeType identity hlt hmem
      calc
        Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (normalizeForTypeIn schema
              variables boolCase fieldDefinition.outputType.namedType
              selectionSet)
          =
        Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (staticCollectForGround schema variables runtimeType
              runtimeType boolCase selectionSet) := by
            exact
              executeSelectionSet_normalizeForTypeIn_runtime_of_schemaWellFormed
                schema resolvers variableValues variables boolCase
                childDepth fieldDefinition.outputType.namedType runtimeType
                identity selectionSet hschema hleaf hmem
        _ =
        Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            selectionSet := hchild childDepth runtimeType identity hlt hmem

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_no_duplicate_child_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.Value ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    SchemaWellFormedness.schemaWellFormed schema ->
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    responseName ∉
      (Execution.collectFields schema variableValues lookupParent source
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase rest)).map Prod.fst ->
    responseName ∉
      (Execution.collectFields schema variableValues lookupParent source
        rest).map Prod.fst ->
    (∀ childDepth runtimeType identity,
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType boolCase selectionSet)
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          selectionSet) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent source
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase rest)
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent source rest ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent source
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent source
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  intro hschema hagrees hsourceVars hallow hlookup hnormalizedNotin
    hsourceNotin hchild htail
  have hcomplete :
      Execution.completeValue schema resolvers variableValues (depth - 1)
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          (normalizeForTypeIn schema
            (operationBoolVars operation)
            boolCase
            fieldDefinition.outputType.namedType selectionSet)
          (resolvers.resolve lookupParent fieldName arguments source)
        =
      Execution.completeValue schema resolvers variableValues (depth - 1)
        ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        selectionSet
        (resolvers.resolve lookupParent fieldName arguments source) :=
    completeValue_normalizeForTypeIn_eq_of_staticCollect_child
      schema resolvers variableValues
      (operationBoolVars operation) boolCase (depth - 1)
      lookupParent fieldName fieldDefinition selectionSet
      (resolvers.resolve lookupParent fieldName arguments source) hschema
      hlookup hchild
  have hcompleteSingleton :
      Execution.completeValue schema resolvers variableValues (depth - 1)
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          [{
            parentType := lookupParent,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet :=
              normalizeForTypeIn schema
                (operationBoolVars operation)
                boolCase
                fieldDefinition.outputType.namedType selectionSet
          }]
          (resolvers.resolve lookupParent fieldName arguments source)
        =
      Execution.completeValue schema resolvers variableValues (depth - 1)
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          [{
            parentType := lookupParent,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }]
          (resolvers.resolve lookupParent fieldName arguments source) := by
    have hleft :=
      GroundTypeNormalization.completeValue_singleton_selectionSet_eq
        schema resolvers variableValues (depth - 1)
        ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        {
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }
        (normalizeForTypeIn schema
          (operationBoolVars operation)
          boolCase
          fieldDefinition.outputType.namedType selectionSet)
        (resolvers.resolve lookupParent fieldName arguments source)
    have hright :=
      GroundTypeNormalization.completeValue_singleton_selectionSet_eq
        schema resolvers variableValues (depth - 1)
        ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        {
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }
        selectionSet
        (resolvers.resolve lookupParent fieldName arguments source)
    exact hleft.trans (hcomplete.trans hright.symm)
  exact
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_no_duplicate_case
      schema resolvers variableValues operation depth lookupParent groundType
      source boolCase responseName fieldName arguments directives
      selectionSet rest fieldDefinition hagrees hsourceVars hallow hlookup
      hnormalizedNotin hsourceNotin hcompleteSingleton htail

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_leaf_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail :
      List (Name × List Execution.ExecutableField)) :
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    leafTypeNameBool schema fieldDefinition.outputType.namedType = true ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet :=
          normalizeForTypeIn schema
            (operationBoolVars operation)
            boolCase
            fieldDefinition.outputType.namedType selectionSet
      } :: normalizedFields) :: normalizedTail ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest)
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      } :: sourceFields) :: sourceTail ->
    Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (withoutFieldsWithResponseName schema responseName rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (withoutFieldsWithResponseName schema responseName rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  intro hagrees hsourceVars hallow hlookup hleaf hnormalizedCollect
    hsourceCollect hfiltered
  have hprojectedComplete :
      Execution.completeValue schema resolvers variableValues (depth - 1)
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          (normalizeForTypeIn schema
              (operationBoolVars operation)
              boolCase
              fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))
          (resolvers.resolve lookupParent fieldName arguments
            (.object groundType identity))
        =
      Execution.completeValue schema resolvers variableValues (depth - 1)
        ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        (selectionSet
          ++ mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName rest)))
        (resolvers.resolve lookupParent fieldName arguments
          (.object groundType identity)) :=
    by
      have hleafComplete :=
        completeValue_eq_of_lookupField_leaf schema resolvers variableValues
          (depth - 1) lookupParent fieldName fieldDefinition
          (normalizeForTypeIn schema
              (operationBoolVars operation)
              boolCase fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))
          (resolvers.resolve lookupParent fieldName arguments
            (.object groundType identity))
          hlookup hleaf
      simpa [List.map_append] using hleafComplete
  exact
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_projected_case
      schema resolvers variableValues operation depth lookupParent groundType
      identity boolCase responseName fieldName arguments directives
      selectionSet rest fieldDefinition normalizedFields sourceFields
      normalizedTail sourceTail hagrees hsourceVars hallow hlookup
      hnormalizedCollect hsourceCollect hprojectedComplete hfiltered

theorem completeValue_normalizeForType_staticScoped_eq_of_child
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (lookupParent groundType fieldName : Name)
    (boolCase : BoolCase)
    (fieldDefinition : FieldDefinition)
    (selectionSet : List Selection)
    (scopedMatches : List CompleteScopedSelection)
    (value : Execution.Value ObjectIdentity) :
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    leafTypeNameBool schema fieldDefinition.outputType.namedType = false ->
    (∀ childDepth runtimeType identity,
      childDepth < depth ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          (normalizeForTypeIn schema
              (operationBoolVars operation)
              boolCase
              fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase scopedMatches))
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches))) ->
      Execution.completeValue schema resolvers variableValues depth
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          (normalizeForTypeIn schema
              (operationBoolVars operation)
              boolCase
              fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase scopedMatches))
          value
        =
      Execution.completeValue schema resolvers variableValues depth
        ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
        (selectionSet
          ++ mergeSelectionSets
            (eraseCompleteScopedSelectionSet scopedMatches))
        value := by
  intro hlookup hleafFalse hchild
  rw [fieldReturnType?_getD_eq_of_lookupField schema lookupParent fieldName
    fieldDefinition hlookup]
  apply GroundTypeNormalization.completeValue_eq_of_child_object_lt_includes
    schema resolvers variableValues
  intro childDepth runtimeType identity hlt hinclude
  simpa [Execution.mergedFieldSelectionSet_append] using
    hchild childDepth runtimeType identity hlt
      (typeIncludesObjectBool_mem_groundObjectTypesForType schema
        fieldDefinition.outputType.namedType runtimeType hleafFalse hinclude)

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_child_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail :
      List (Name × List Execution.ExecutableField)) :
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    leafTypeNameBool schema fieldDefinition.outputType.namedType = false ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet :=
          normalizeForTypeIn schema
            (operationBoolVars operation)
            boolCase
            fieldDefinition.outputType.namedType selectionSet
      } :: normalizedFields) :: normalizedTail ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest)
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      } :: sourceFields) :: sourceTail ->
    (∀ childDepth runtimeType (childIdentity : ObjectIdentity),
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (normalizeForTypeIn schema
              (operationBoolVars operation)
              boolCase
              fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (withoutFieldsWithResponseName schema responseName rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (withoutFieldsWithResponseName schema responseName rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  intro hagrees hsourceVars hallow hlookup hleafFalse hnormalizedCollect
    hsourceCollect hchild hfiltered
  have hprojectedComplete :
      Execution.completeValue schema resolvers variableValues (depth - 1)
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          (normalizeForTypeIn schema
              (operationBoolVars operation)
              boolCase
              fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation) groundType
                boolCase
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))
          (resolvers.resolve lookupParent fieldName arguments
            (.object groundType identity))
        =
        Execution.completeValue schema resolvers variableValues (depth - 1)
          ((schema.fieldReturnType? lookupParent fieldName).getD fieldName)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))
          (resolvers.resolve lookupParent fieldName arguments
            (.object groundType identity)) :=
    completeValue_normalizeForType_staticScoped_eq_of_child
      schema resolvers variableValues operation (depth - 1) lookupParent
      groundType fieldName boolCase fieldDefinition selectionSet
      (staticScopedFieldsWithResponseName schema boolCase lookupParent
        groundType responseName rest)
      (resolvers.resolve lookupParent fieldName arguments
        (.object groundType identity))
      hlookup hleafFalse hchild
  exact
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_projected_case
      schema resolvers variableValues operation depth lookupParent groundType
      identity boolCase responseName fieldName arguments directives
      selectionSet rest fieldDefinition normalizedFields sourceFields
      normalizedTail sourceTail hagrees hsourceVars hallow hlookup
      hnormalizedCollect hsourceCollect hprojectedComplete hfiltered

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_static_child_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail :
      List (Name × List Execution.ExecutableField)) :
    SchemaWellFormedness.schemaWellFormed schema ->
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    leafTypeNameBool schema fieldDefinition.outputType.namedType = false ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet :=
          normalizeForTypeIn schema
            (operationBoolVars operation)
            boolCase
            fieldDefinition.outputType.namedType selectionSet
      } :: normalizedFields) :: normalizedTail ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest)
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      } :: sourceFields) :: sourceTail ->
    (∀ childDepth runtimeType (_childIdentity : ObjectIdentity),
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        ∀ scopedSelection,
          scopedSelection ∈
            staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName rest ->
          completeScopedSelectionRuntimeReady schema boolCase runtimeType
            scopedSelection) ->
    (∀ childDepth runtimeType (childIdentity : ObjectIdentity),
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType boolCase
            (selectionSet
              ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest))))
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (withoutFieldsWithResponseName schema responseName rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (withoutFieldsWithResponseName schema responseName rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  intro hschema hagrees hsourceVars hallow hlookup hleafFalse
    hnormalizedCollect hsourceCollect hscopedReady hstaticChild hfiltered
  apply
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_child_case
      schema resolvers variableValues operation depth lookupParent groundType
      identity boolCase responseName fieldName arguments directives
      selectionSet rest fieldDefinition normalizedFields sourceFields
      normalizedTail sourceTail hagrees hsourceVars hallow hlookup hleafFalse
      hnormalizedCollect hsourceCollect
  · intro childDepth runtimeType childIdentity hlt hmem
    exact
      (executeSelectionSet_normalizeForTypeIn_staticScoped_runtime
        schema resolvers variableValues
        (operationBoolVars operation) boolCase childDepth
        fieldDefinition.outputType.namedType groundType runtimeType
        childIdentity selectionSet
        (staticScopedFieldsWithResponseName schema boolCase lookupParent
          groundType responseName rest)
        hschema hleafFalse hmem
        (hscopedReady childDepth runtimeType childIdentity hlt hmem)).trans
        (hstaticChild childDepth runtimeType childIdentity hlt hmem)
  · exact hfiltered

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_outputs_child_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail :
      List (Name × List Execution.ExecutableField)) :
    SchemaWellFormedness.schemaWellFormed schema ->
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    leafTypeNameBool schema fieldDefinition.outputType.namedType = false ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet :=
          normalizeForTypeIn schema
            (operationBoolVars operation)
            boolCase
            fieldDefinition.outputType.namedType selectionSet
      } :: normalizedFields) :: normalizedTail ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest)
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      } :: sourceFields) :: sourceTail ->
    (∀ childDepth runtimeType (_childIdentity : ObjectIdentity),
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        completeScopedFieldOutputsInclude schema runtimeType
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName rest)) ->
    (∀ childDepth runtimeType childIdentity,
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType boolCase
            (selectionSet
              ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest))))
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (withoutFieldsWithResponseName schema responseName rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (withoutFieldsWithResponseName schema responseName rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  intro hschema hagrees hsourceVars hallow hlookup hleafFalse
    hnormalizedCollect hsourceCollect houtputs hstaticChild hfiltered
  apply
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_static_child_case
      schema resolvers variableValues operation depth lookupParent groundType
      identity boolCase responseName fieldName arguments directives
      selectionSet rest fieldDefinition normalizedFields sourceFields
      normalizedTail sourceTail hschema hagrees hsourceVars hallow hlookup
      hleafFalse hnormalizedCollect hsourceCollect
  · intro childDepth runtimeType _childIdentity hlt hmem
    exact
      completeScopedSelectionRuntimeReady_staticScopedFieldsWithResponseName_of_outputsInclude
        schema boolCase lookupParent groundType responseName runtimeType
        rest (houtputs childDepth runtimeType _childIdentity hlt hmem)
  · exact hstaticChild
  · exact hfiltered

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_object_child_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail :
      List (Name × List Execution.ExecutableField)) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.objectType lookupParent ->
    selectionSetLookupValid schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool lookupParent groundType = true ->
    leafTypeNameBool schema fieldDefinition.outputType.namedType = false ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet :=
          normalizeForTypeIn schema
            (operationBoolVars operation)
            boolCase
            fieldDefinition.outputType.namedType selectionSet
      } :: normalizedFields) :: normalizedTail ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest)
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      } :: sourceFields) :: sourceTail ->
    (∀ childDepth runtimeType childIdentity,
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType boolCase
            (selectionSet
              ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest))))
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (withoutFieldsWithResponseName schema responseName rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (withoutFieldsWithResponseName schema responseName rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  intro hschema hobject hlookupValid hmerge hagrees hsourceVars hallow hlookup
    hground hleafFalse hnormalizedCollect hsourceCollect hstaticChild
    hfiltered
  apply
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_outputs_child_case
      schema resolvers variableValues operation depth lookupParent groundType
      identity boolCase responseName fieldName arguments directives
      selectionSet rest fieldDefinition normalizedFields sourceFields
      normalizedTail sourceTail hschema hagrees hsourceVars hallow hlookup
      hleafFalse hnormalizedCollect hsourceCollect
  · intro childDepth runtimeType _childIdentity _hlt hmem
    exact
      completeScopedFieldOutputsInclude_staticScopedFieldsWithResponseName_object
        schema boolCase lookupParent groundType responseName runtimeType
        fieldName arguments directives selectionSet rest fieldDefinition
        hschema hobject hlookupValid hmerge hlookup hground
        (groundObjectTypesForType_mem_typeIncludesObjectBool schema
          fieldDefinition.outputType.namedType runtimeType hleafFalse hmem)
  · exact hstaticChild
  · exact hfiltered

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_group_child_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail :
      List (Name × List Execution.ExecutableField)) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.objectType lookupParent ->
    selectionSetLookupValid schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema lookupParent
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
    variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation) ->
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    directivesAllowIn boolCase directives = true ->
    schema.lookupField lookupParent fieldName = some fieldDefinition ->
    schema.typeIncludesObjectBool lookupParent groundType = true ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet :=
          normalizeForTypeIn schema
            (operationBoolVars operation)
            boolCase
            fieldDefinition.outputType.namedType selectionSet
      } :: normalizedFields) :: normalizedTail ->
    Execution.collectFields schema variableValues lookupParent
        (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest)
      =
      (responseName, {
        parentType := lookupParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      } :: sourceFields) :: sourceTail ->
    (∀ childDepth runtimeType childIdentity,
      childDepth < depth - 1 ->
      runtimeType ∈
        groundObjectTypesForType schema
          fieldDefinition.outputType.namedType ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType boolCase
            (selectionSet
              ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest))))
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType childIdentity)
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest)))) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (withoutFieldsWithResponseName schema responseName rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (withoutFieldsWithResponseName schema responseName rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        lookupParent (.object groundType identity)
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
  intro hschema hobject hlookupValid hmerge hagrees hsourceVars hallow hlookup
    hground hnormalizedCollect hsourceCollect hstaticChild hfiltered
  cases hleaf : leafTypeNameBool schema fieldDefinition.outputType.namedType
  · apply
      executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_object_child_case
        schema resolvers variableValues operation depth lookupParent groundType
        identity boolCase responseName fieldName arguments directives
        selectionSet rest fieldDefinition normalizedFields sourceFields
        normalizedTail sourceTail hschema hobject hlookupValid hmerge hagrees
        hsourceVars hallow hlookup hground hleaf hnormalizedCollect
        hsourceCollect hstaticChild hfiltered
  · apply
      executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_duplicate_group_leaf_case
        schema resolvers variableValues operation depth lookupParent groundType
        identity boolCase responseName fieldName arguments directives
        selectionSet rest fieldDefinition normalizedFields sourceFields
        normalizedTail sourceTail hagrees hsourceVars hallow hlookup hleaf
        hnormalizedCollect hsourceCollect hfiltered


end CompleteNormalization

end NormalForm

end GraphQL
