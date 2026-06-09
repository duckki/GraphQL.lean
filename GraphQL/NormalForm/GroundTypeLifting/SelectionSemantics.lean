import GraphQL.NormalForm.GroundTypeLifting.FieldHeads

/-!
Selection-set semantic preservation scaffolding for ground-type lifting.

The final proof recurses over the size of the erased scoped selection set. The
lemmas in this module establish the strict-size facts needed for inline-fragment
flattening and tail recursion.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectIdentity : Type}

private theorem selectionSet_size_append (left right : List Selection) :
    SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

private theorem size_withoutFieldsWithResponseName_le (schema : Schema)
    (responseName : Name) :
    ∀ selectionSet,
      SelectionSet.size
          (withoutFieldsWithResponseName schema responseName selectionSet)
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [withoutFieldsWithResponseName, SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_withoutFieldsWithResponseName_le schema responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [withoutFieldsWithResponseName, h, SelectionSet.size,
              Selection.size]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldsWithResponseName, hfalse, SelectionSet.size,
              Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_withoutFieldsWithResponseName_le schema responseName
              selectionSet
          have hrest :=
            size_withoutFieldsWithResponseName_le schema responseName rest
          cases typeCondition <;>
            simp [withoutFieldsWithResponseName, SelectionSet.size,
              Selection.size]
          all_goals omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem size_mergeSelectionSets_validFieldsWithResponseName_le
    (schema : Schema) (parentType responseName : Name) :
    ∀ selectionSet,
      SelectionSet.size
          (mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName
              selectionSet))
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [validFieldsWithResponseName, mergeSelectionSets,
        SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_mergeSelectionSets_validFieldsWithResponseName_le
              schema parentType responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [validFieldsWithResponseName, mergeSelectionSets, h,
              selectionSet_size_append, SelectionSet.size,
              Selection.size, Selection.subselections]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [validFieldsWithResponseName, hfalse,
              SelectionSet.size, Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_mergeSelectionSets_validFieldsWithResponseName_le
              schema parentType responseName selectionSet
          have hrest :=
            size_mergeSelectionSets_validFieldsWithResponseName_le
              schema parentType responseName rest
          cases typeCondition with
          | none =>
              simp [validFieldsWithResponseName, mergeSelectionSets_append,
                selectionSet_size_append, SelectionSet.size, Selection.size]
              omega
          | some typeCondition =>
              by_cases h :
                  schema.typesOverlapBool parentType typeCondition = true
              · simp [validFieldsWithResponseName, h, mergeSelectionSets_append,
                  selectionSet_size_append, SelectionSet.size, Selection.size]
                omega
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [validFieldsWithResponseName, hfalse, SelectionSet.size,
                  Selection.size]
                omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem eraseScopedSelectionSet_scopedSelectionSet_size
    (liftParent : Name) (selectionSet : List Selection) :
    SelectionSet.size
        (eraseScopedSelectionSet (scopedSelectionSet liftParent selectionSet))
      =
    SelectionSet.size selectionSet := by
  rw [eraseScopedSelectionSet_scopedSelectionSet]

theorem eraseScopedSelectionSet_tail_size_lt
    (scopedSelection : ScopedSelection)
    (rest : List ScopedSelection) :
    SelectionSet.size (eraseScopedSelectionSet rest)
      <
    SelectionSet.size
      (eraseScopedSelectionSet (scopedSelection :: rest)) := by
  cases scopedSelection with
  | mk liftParent selection =>
      cases selection <;>
        simp [eraseScopedSelectionSet, eraseScopedSelection,
          SelectionSet.size, Selection.size]
      all_goals omega

theorem eraseScopedSelectionSet_inlineFragment_none_flatten_size_lt
    (liftParent : Name) (selectionSet : List Selection)
    (rest : List ScopedSelection) :
    SelectionSet.size
        (eraseScopedSelectionSet
          (scopedSelectionSet liftParent selectionSet ++ rest))
      <
    SelectionSet.size
      (eraseScopedSelectionSet
        ({ liftParent := liftParent,
           selection := Selection.inlineFragment none [] selectionSet }
          :: rest)) := by
  simp [eraseScopedSelectionSet_append,
    eraseScopedSelectionSet_scopedSelectionSet, eraseScopedSelectionSet,
    eraseScopedSelection, selectionSet_size_append, SelectionSet.size,
    Selection.size]

theorem eraseScopedSelectionSet_inlineFragment_some_flatten_size_lt
    (liftParent typeCondition : Name) (selectionSet : List Selection)
    (rest : List ScopedSelection) :
    SelectionSet.size
        (eraseScopedSelectionSet
          (scopedSelectionSet typeCondition selectionSet ++ rest))
      <
    SelectionSet.size
      (eraseScopedSelectionSet
        ({ liftParent := liftParent,
           selection :=
            Selection.inlineFragment (some typeCondition) [] selectionSet }
          :: rest)) := by
  simp [eraseScopedSelectionSet_append,
    eraseScopedSelectionSet_scopedSelectionSet, eraseScopedSelectionSet,
    eraseScopedSelection, selectionSet_size_append, SelectionSet.size,
    Selection.size]

theorem eraseScopedSelectionSet_field_subselections_size_lt
    (liftParent responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (rest : List ScopedSelection) :
    SelectionSet.size selectionSet
      <
    SelectionSet.size
      (eraseScopedSelectionSet
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] selectionSet }
          :: rest)) := by
  simp [eraseScopedSelectionSet, eraseScopedSelection, SelectionSet.size,
    Selection.size]
  omega

theorem eraseScopedSelectionSet_withoutFieldsWithResponseName_size_lt_field
    (schema : Schema) (liftParent responseName fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection)
    (rest : List ScopedSelection) :
    SelectionSet.size
        (eraseScopedSelectionSet
          (scopedSelectionSetWithoutFieldsWithResponseName schema
            responseName rest))
      <
    SelectionSet.size
      (eraseScopedSelectionSet
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] selectionSet }
          :: rest)) := by
  have hle :
      SelectionSet.size
          (withoutFieldsWithResponseName schema responseName
            (eraseScopedSelectionSet rest))
        ≤
      SelectionSet.size (eraseScopedSelectionSet rest) :=
    size_withoutFieldsWithResponseName_le schema responseName
      (eraseScopedSelectionSet rest)
  have htail :
      SelectionSet.size (eraseScopedSelectionSet rest)
        <
      SelectionSet.size
        (eraseScopedSelectionSet
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments []
                selectionSet }
            :: rest)) :=
    eraseScopedSelectionSet_tail_size_lt
      { liftParent := liftParent,
        selection :=
          Selection.field responseName fieldName arguments [] selectionSet }
      rest
  rw [eraseScopedSelectionSet_withoutFieldsWithResponseName]
  exact Nat.lt_of_le_of_lt hle htail

theorem eraseScopedSelectionSet_withoutFieldsWithResponseName_size_lt_field_directives
    (schema : Schema) (liftParent responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (rest : List ScopedSelection) :
    SelectionSet.size
        (eraseScopedSelectionSet
          (scopedSelectionSetWithoutFieldsWithResponseName schema
            responseName rest))
      <
    SelectionSet.size
      (eraseScopedSelectionSet
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments directives
              selectionSet }
          :: rest)) := by
  have hle :
      SelectionSet.size
          (withoutFieldsWithResponseName schema responseName
            (eraseScopedSelectionSet rest))
        ≤
      SelectionSet.size (eraseScopedSelectionSet rest) :=
    size_withoutFieldsWithResponseName_le schema responseName
      (eraseScopedSelectionSet rest)
  have htail :
      SelectionSet.size (eraseScopedSelectionSet rest)
        <
      SelectionSet.size
        (eraseScopedSelectionSet
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
            :: rest)) :=
    eraseScopedSelectionSet_tail_size_lt
      { liftParent := liftParent,
        selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
      rest
  rw [eraseScopedSelectionSet_withoutFieldsWithResponseName]
  exact Nat.lt_of_le_of_lt hle htail

theorem eraseScopedSelectionSet_validFieldsWithResponseName_merged_size_le
    (schema : Schema) (filterParent responseName : Name)
    (scopedSelections : List ScopedSelection) :
    SelectionSet.size
        (mergeSelectionSets
          (eraseScopedSelectionSet
            (scopedSelectionSetValidFieldsWithResponseName schema filterParent
              responseName scopedSelections)))
      ≤
    SelectionSet.size (eraseScopedSelectionSet scopedSelections) := by
  rw [eraseScopedSelectionSet_validFieldsWithResponseName]
  exact size_mergeSelectionSets_validFieldsWithResponseName_le schema
    filterParent responseName (eraseScopedSelectionSet scopedSelections)

theorem eraseScopedSelectionSet_field_merged_subselections_size_lt
    (schema : Schema) (execParent liftParent responseName fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection)
    (rest : List ScopedSelection) :
    SelectionSet.size
        (selectionSet
          ++ mergeSelectionSets
            (eraseScopedSelectionSet
              (scopedSelectionSetValidFieldsWithResponseName schema
                execParent responseName rest)))
      <
    SelectionSet.size
      (eraseScopedSelectionSet
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] selectionSet }
          :: rest)) := by
  have hmatches :=
    eraseScopedSelectionSet_validFieldsWithResponseName_merged_size_le schema
      execParent responseName rest
  simp [eraseScopedSelectionSet, eraseScopedSelection, selectionSet_size_append,
    SelectionSet.size, Selection.size]
  omega

theorem eraseScopedSelectionSet_field_merged_subselections_size_lt_directives
    (schema : Schema) (execParent liftParent responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (rest : List ScopedSelection) :
    SelectionSet.size
        (selectionSet
          ++ mergeSelectionSets
            (eraseScopedSelectionSet
              (scopedSelectionSetValidFieldsWithResponseName schema
                execParent responseName rest)))
      <
    SelectionSet.size
      (eraseScopedSelectionSet
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments directives
              selectionSet }
          :: rest)) := by
  have hmatches :=
    eraseScopedSelectionSet_validFieldsWithResponseName_merged_size_le schema
      execParent responseName rest
  simp [eraseScopedSelectionSet, eraseScopedSelection, selectionSet_size_append,
    SelectionSet.size, Selection.size]
  omega

theorem scopedFieldHead_child_directiveFree
    (schema : Schema) (execParent liftParent responseName fieldName : Name)
    (arguments : List Argument) (subselections : List Selection)
    (rest : List ScopedSelection) :
    scopedSelectionSetDirectiveFree
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
      selectionSetDirectiveFree
        (subselections
          ++ mergeSelectionSets
            (eraseScopedSelectionSet
              (scopedSelectionSetValidFieldsWithResponseName schema
                execParent responseName rest))) := by
  intro hfree
  have hheadFree :
      selectionSetDirectiveFree subselections := by
    simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet,
      eraseScopedSelection, selectionDirectiveFree] using
      (selectionSetDirectiveFree_head hfree).2
  have hmatchesFree :
      selectionSetDirectiveFree
        (eraseScopedSelectionSet
          (scopedSelectionSetValidFieldsWithResponseName schema execParent
            responseName rest)) :=
    scopedSelectionSetValidFieldsWithResponseName_directiveFree schema
      execParent responseName rest (selectionSetDirectiveFree_tail hfree)
  exact selectionSetDirectiveFree_append hheadFree
    (selectionSetDirectiveFree_mergeSelectionSets hmatchesFree)

theorem scopedFieldHead_child_semanticsReady
    (schema : Schema) (execParent liftParent responseName fieldName
      childRuntimeType : Name)
    (arguments : List Argument) (subselections : List Selection)
    (rest : List ScopedSelection) (execFieldDefinition : FieldDefinition) :
    objectTypeNameBool schema execParent = true ->
    scopedSelectionSetSemanticsReady schema execParent
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    scopedSelectionSetLookupValid schema
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    scopedSelectionSetCanMerge schema execParent
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
    schema.typeIncludesObjectBool
        ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        childRuntimeType = true ->
      selectionSetSemanticsReady schema childRuntimeType
        (subselections
          ++ mergeSelectionSets
            (eraseScopedSelectionSet
              (scopedSelectionSetValidFieldsWithResponseName schema
                execParent responseName rest))) := by
  intro hobject hready _hlookup hmerge hexecLookup hchildInclude
  have hparentObject : schema.objectType execParent :=
    objectType_of_objectTypeNameBool_eq_true schema hobject
  have hrawLookup :
      selectionSetLookupValid schema execParent
        (Selection.field responseName fieldName arguments [] subselections
          :: eraseScopedSelectionSet rest) :=
    selectionSetLookupValid_of_selectionSetSemanticsReady
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest)
      hready
  have hreadyChild :=
    selectionSetSemanticsReady_fieldHead_merged_of_child_object schema
      execParent responseName fieldName childRuntimeType arguments
      subselections (eraseScopedSelectionSet rest) execFieldDefinition
      hparentObject hready hrawLookup hmerge hexecLookup
  have hreturn :
      (schema.fieldReturnType? execParent fieldName).getD fieldName
        =
      execFieldDefinition.outputType.namedType := by
    simp [Schema.fieldReturnType?, hexecLookup]
  rw [hreturn] at hchildInclude
  simpa [eraseScopedSelectionSet_validFieldsWithResponseName] using
    hreadyChild hchildInclude

theorem scopedFieldHead_child_canMerge
    (schema : Schema) (execParent liftParent responseName fieldName
      childRuntimeType : Name)
    (arguments : List Argument) (subselections : List Selection)
    (rest : List ScopedSelection) (execFieldDefinition : FieldDefinition) :
    objectTypeNameBool schema execParent = true ->
    scopedSelectionSetSemanticsReady schema execParent
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    scopedSelectionSetCanMerge schema execParent
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
      FieldMerge.fieldsInSetCanMerge schema childRuntimeType
        (subselections
          ++ mergeSelectionSets
            (eraseScopedSelectionSet
              (scopedSelectionSetValidFieldsWithResponseName schema
                execParent responseName rest))) := by
  intro hobject hready hmerge hexecLookup
  have hparentObject : schema.objectType execParent :=
    objectType_of_objectTypeNameBool_eq_true schema hobject
  have hrawLookup :
      selectionSetLookupValid schema execParent
        (Selection.field responseName fieldName arguments [] subselections
          :: eraseScopedSelectionSet rest) :=
    selectionSetLookupValid_of_selectionSetSemanticsReady
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest)
      hready
  have hmergeChild :=
    fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
      schema execParent responseName fieldName childRuntimeType arguments
      subselections (eraseScopedSelectionSet rest) execFieldDefinition
      hparentObject hrawLookup hmerge hexecLookup
  simpa [eraseScopedSelectionSet_validFieldsWithResponseName] using hmergeChild

theorem groundLiftScopedSelectionSet_executeSelectionSet_field_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (depth : Nat) (execParent liftParent runtimeType : Name)
    (identity : DataModel.ObjectPath)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection) :
    objectTypeNameBool schema execParent = true ->
    schema.typeIncludesObjectBool execParent runtimeType = true ->
    scopedSelectionSetDirectiveFree
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    scopedSelectionSetSemanticsReady schema execParent
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    scopedSelectionSetLookupValid schema
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    scopedSelectionSetCanMerge schema execParent
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    scopedSelectionSetRuntimeApplies schema runtimeType
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent (.object runtimeType identity)
      (groundLiftScopedSelectionSet schema
        (scopedSelectionSetWithoutFieldsWithResponseName schema responseName
          rest))
      =
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent (.object runtimeType identity)
      (eraseScopedSelectionSet
        (scopedSelectionSetWithoutFieldsWithResponseName schema responseName
          rest)) ->
    (∀ childDepth childRuntimeType childIdentity,
      childDepth < depth - 1 ->
      schema.typeIncludesObjectBool
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          childRuntimeType = true ->
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth childRuntimeType
          (.object childRuntimeType childIdentity)
          (groundLiftSelectionSet schema childRuntimeType
            (subselections
              ++ mergeSelectionSets
                (eraseScopedSelectionSet
                  (scopedSelectionSetValidFieldsWithResponseName schema
                    execParent responseName rest))))
        =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues childDepth childRuntimeType
          (.object childRuntimeType childIdentity)
          (subselections
            ++ mergeSelectionSets
              (eraseScopedSelectionSet
                (scopedSelectionSetValidFieldsWithResponseName schema
                  execParent responseName rest)))) ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object runtimeType identity)
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments []
                subselections }
            :: rest))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object runtimeType identity)
        (eraseScopedSelectionSet
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments []
                subselections }
            :: rest)) := by
  intro hobject hinclude hfree hready hlookup hmerge happlies htail
    hchildren
  cases depth with
  | zero =>
      simp [Execution.executeSelectionSet, executeCollectedFields_zero]
  | succ fieldDepth =>
      rcases scopedFieldHead_lookupPair_of_semanticsReady_lookupValid schema
          execParent liftParent responseName fieldName arguments
          subselections rest hready hlookup with
        ⟨execFieldDefinition, liftFieldDefinition, hexecLookup,
          hliftLookup⟩
      let liftedSelectionSet :=
        if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
          []
        else if objectTypeNameBool schema
            liftFieldDefinition.outputType.namedType then
          groundLiftSelectionSet schema
            liftFieldDefinition.outputType.namedType subselections
        else
          (groundObjectTypesForType schema
            liftFieldDefinition.outputType.namedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType subselections))
      have hliftCollectExists :=
        collectFields_field_head_exists schema variableValues execParent
          (.object runtimeType identity) responseName fieldName arguments
          liftedSelectionSet (groundLiftScopedSelectionSet schema rest)
      rcases hliftCollectExists with
        ⟨liftedFields, liftedRestGroups, hliftCollectRaw⟩
      have hsourceCollectExists :=
        collectFields_field_head_exists schema variableValues execParent
          (.object runtimeType identity) responseName fieldName arguments
          subselections (eraseScopedSelectionSet rest)
      rcases hsourceCollectExists with
        ⟨sourceFields, sourceRest, hsourceCollect⟩
      have hliftCollect :
          Execution.collectFields schema variableValues execParent
            (.object runtimeType identity)
            (groundLiftScopedSelectionSet schema
              ({ liftParent := liftParent,
                 selection :=
                  Selection.field responseName fieldName arguments []
                    subselections }
                :: rest))
          =
          (responseName,
            ({
              parentType := execParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := liftedSelectionSet
            } : Execution.ExecutableField) :: liftedFields)
            :: liftedRestGroups := by
        simpa [groundLiftScopedSelectionSet, groundLiftScopedSelection,
          groundLiftSelection, hliftLookup, liftedSelectionSet]
          using hliftCollectRaw
      have hheadApplies :
          schema.typeIncludesObjectBool liftParent runtimeType = true :=
        happlies
          { liftParent := liftParent,
            selection :=
              Selection.field responseName fieldName arguments []
                subselections }
          (by simp)
      have hheadInclude :
          executionValueObjectsInclude schema
            liftFieldDefinition.outputType.namedType
            ((store.resolvers schema).resolve execParent fieldName arguments
              (.object runtimeType identity)) :=
        scopedFieldHead_valueIncludes_on_store schema store hschema hstore
          execParent liftParent runtimeType identity fieldName arguments
          liftFieldDefinition hheadApplies hliftLookup
      have hrawLookup :
          selectionSetLookupValid schema execParent
            (Selection.field responseName fieldName arguments [] subselections
              :: eraseScopedSelectionSet rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments [] subselections
            :: eraseScopedSelectionSet rest)
          hready
      have hmatchesInclude :
          scopedFieldOutputValuesInclude schema
            ((store.resolvers schema).resolve execParent fieldName arguments
              (.object runtimeType identity))
            (scopedSelectionSetValidFieldsWithResponseName schema execParent
              responseName rest) :=
        scopedSelectionSetValidFieldsWithResponseName_valuesInclude_on_store
          schema store hschema hstore execParent runtimeType identity
          responseName fieldName arguments subselections rest hobject hinclude
          hrawLookup hmerge (scopedSelectionSetRuntimeApplies_tail happlies)
          (scopedSelectionSetLookupValid_tail hlookup)
      have htailCollected :
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues (fieldDepth + 1) (.object runtimeType identity)
            liftedRestGroups
          =
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues (fieldDepth + 1) (.object runtimeType identity)
            sourceRest := by
        simpa [liftedSelectionSet] using
          executeCollectedFields_groundLift_scoped_fieldHead_tail_eq_of_withoutFields
            schema store variableValues (fieldDepth + 1) execParent
            liftParent runtimeType identity responseName fieldName arguments
            subselections rest liftedFields sourceFields liftedRestGroups
            sourceRest liftFieldDefinition hobject hinclude hfree hliftLookup
            hliftCollect hsourceCollect htail
      simpa [eraseScopedSelectionSet, eraseScopedSelection,
        liftedSelectionSet] using
        executeSelectionSet_field_head_groundLift_scoped_sameGroup_of_valueIncludes
          schema store variableValues hschema fieldDepth execParent liftParent
          runtimeType identity responseName fieldName arguments subselections
          rest liftedFields sourceFields liftedRestGroups sourceRest
          execFieldDefinition liftFieldDefinition hobject hinclude hfree
          hexecLookup hliftLookup hliftCollect hsourceCollect hheadInclude
          hmatchesInclude
          (by
            intro childDepth childRuntimeType childIdentity hlt hchildInclude
            exact hchildren childDepth childRuntimeType childIdentity
              (by simpa using hlt) hchildInclude)
          htailCollected

theorem groundLiftScopedSelectionSet_executeSelectionSet_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema) :
    ∀ depth execParent runtimeType identity scopedSelections,
      objectTypeNameBool schema execParent = true ->
      schema.typeIncludesObjectBool execParent runtimeType = true ->
      scopedSelectionSetDirectiveFree scopedSelections ->
      scopedSelectionSetSemanticsReady schema execParent scopedSelections ->
      scopedSelectionSetLookupValid schema scopedSelections ->
      scopedSelectionSetCanMerge schema execParent scopedSelections ->
      scopedSelectionSetRuntimeApplies schema runtimeType scopedSelections ->
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth execParent (.object runtimeType identity)
          (groundLiftScopedSelectionSet schema scopedSelections)
        =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth execParent (.object runtimeType identity)
          (eraseScopedSelectionSet scopedSelections)
  | depth, execParent, runtimeType, identity, [] => by
      intro _hobject _hinclude _hfree _hready _hlookup _hmerge _happlies
      simp [groundLiftScopedSelectionSet, eraseScopedSelectionSet,
        Execution.executeSelectionSet, Execution.collectFields]
  | depth, execParent, runtimeType, identity, scopedSelection :: rest => by
      intro hobject hinclude hfree hready hlookup hmerge happlies
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field responseName fieldName arguments directives subselections =>
              have hheadFree :
                  selectionDirectiveFree
                    (Selection.field responseName fieldName arguments
                      directives subselections) := by
                exact selectionSetDirectiveFree_head hfree
              have hdirectives : directives = [] := by
                simpa [selectionDirectiveFree] using hheadFree.1
              subst directives
              apply
                groundLiftScopedSelectionSet_executeSelectionSet_field_on_store
                  schema store variableValues hschema hstore depth execParent
                  liftParent runtimeType identity responseName fieldName
                  arguments subselections rest hobject hinclude hfree hready
                  hlookup hmerge happlies
              · exact
                  groundLiftScopedSelectionSet_executeSelectionSet_on_store
                    schema store variableValues hschema hstore
                    depth execParent runtimeType identity
                    (scopedSelectionSetWithoutFieldsWithResponseName schema
                      responseName rest)
                    hobject hinclude
                    (scopedSelectionSetWithoutFieldsWithResponseName_directiveFree
                      schema responseName rest
                      (selectionSetDirectiveFree_tail hfree))
                    (scopedSelectionSetWithoutFieldsWithResponseName_semanticsReady
                      schema execParent responseName rest
                      (scopedSelectionSetSemanticsReady_tail hready))
                    (scopedSelectionSetWithoutFieldsWithResponseName_lookupValid
                      schema responseName rest
                      (scopedSelectionSetLookupValid_tail hlookup))
                    (scopedSelectionSetWithoutFieldsWithResponseName_canMerge
                      schema execParent responseName rest
                      (scopedSelectionSetCanMerge_tail schema execParent
                        { liftParent := liftParent,
                          selection :=
                            Selection.field responseName fieldName arguments []
                              subselections }
                        rest hmerge))
                    (scopedSelectionSetWithoutFieldsWithResponseName_runtimeApplies
                      schema responseName runtimeType rest
                      (scopedSelectionSetRuntimeApplies_tail happlies))
              · intro childDepth childRuntimeType childIdentity hlt
                  hchildInclude
                rcases scopedFieldHead_lookupPair_of_semanticsReady_lookupValid
                    schema execParent liftParent responseName fieldName
                    arguments subselections rest hready hlookup with
                  ⟨execFieldDefinition, _liftFieldDefinition, hexecLookup,
                    _hliftLookup⟩
                have hchildObject :
                    objectTypeNameBool schema childRuntimeType = true := by
                  exact objectTypeNameBool_eq_true_of_objectType schema
                    (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema
                      ((schema.fieldReturnType? execParent fieldName).getD
                        fieldName)
                      childRuntimeType
                      (List.contains_iff_mem.mp hchildInclude))
                let childSelectionSet :=
                  subselections
                    ++ mergeSelectionSets
                      (eraseScopedSelectionSet
                        (scopedSelectionSetValidFieldsWithResponseName schema
                          execParent responseName rest))
                have hchildFree :
                    selectionSetDirectiveFree childSelectionSet := by
                  simpa [childSelectionSet] using
                    scopedFieldHead_child_directiveFree schema execParent
                      liftParent responseName fieldName arguments subselections
                      rest hfree
                have hchildReady :
                    selectionSetSemanticsReady schema childRuntimeType
                      childSelectionSet := by
                  simpa [childSelectionSet] using
                    scopedFieldHead_child_semanticsReady schema execParent
                      liftParent responseName fieldName childRuntimeType
                      arguments subselections rest execFieldDefinition hobject
                      hready hlookup hmerge hexecLookup hchildInclude
                have hchildLookup :
                    selectionSetLookupValid schema childRuntimeType
                      childSelectionSet :=
                  selectionSetLookupValid_of_selectionSetSemanticsReady
                    childSelectionSet hchildReady
                have hchildMerge :
                    FieldMerge.fieldsInSetCanMerge schema childRuntimeType
                      childSelectionSet := by
                  simpa [childSelectionSet] using
                    scopedFieldHead_child_canMerge schema execParent liftParent
                      responseName fieldName childRuntimeType arguments
                      subselections rest execFieldDefinition hobject hready
                      hmerge hexecLookup
                have hchildScoped :=
                  groundLiftScopedSelectionSet_executeSelectionSet_on_store
                    schema store variableValues hschema hstore
                    childDepth childRuntimeType childRuntimeType childIdentity
                    (scopedSelectionSet childRuntimeType childSelectionSet)
                    hchildObject
                    (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                      hchildObject)
                    ((scopedSelectionSetDirectiveFree_scopedSelectionSet
                      childRuntimeType childSelectionSet).mpr hchildFree)
                    ((scopedSelectionSetSemanticsReady_scopedSelectionSet
                      schema childRuntimeType childRuntimeType
                      childSelectionSet).mpr hchildReady)
                    ((scopedSelectionSetLookupValid_scopedSelectionSet schema
                      childRuntimeType childSelectionSet).mpr hchildLookup)
                    ((scopedSelectionSetCanMerge_scopedSelectionSet schema
                      childRuntimeType childRuntimeType childSelectionSet).mpr
                      hchildMerge)
                    (scopedSelectionSetRuntimeApplies_scopedSelectionSet
                      schema childRuntimeType childRuntimeType childSelectionSet
                      (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                        hchildObject))
                simpa [childSelectionSet,
                  groundLiftScopedSelectionSet_scopedSelectionSet,
                  eraseScopedSelectionSet_scopedSelectionSet] using hchildScoped
          | inlineFragment typeCondition directives selectionSet =>
              have hheadFree :
                  selectionDirectiveFree
                    (Selection.inlineFragment typeCondition directives
                      selectionSet) := by
                exact selectionSetDirectiveFree_head hfree
              have hdirectives : directives = [] := by
                simpa [selectionDirectiveFree] using hheadFree.1
              subst directives
              cases typeCondition with
              | none =>
              apply executeSelectionSet_inlineFragment_none_groundLift_scoped_flatten
              exact
                groundLiftScopedSelectionSet_executeSelectionSet_on_store
                  schema store variableValues hschema hstore
                  depth execParent runtimeType identity
                  (scopedSelectionSet liftParent selectionSet ++ rest)
                  hobject hinclude
                  (scopedSelectionSetDirectiveFree_append
                    ((scopedSelectionSetDirectiveFree_scopedSelectionSet
                      liftParent selectionSet).mpr
                      (by simpa [selectionDirectiveFree] using hheadFree.2))
                    (selectionSetDirectiveFree_tail hfree))
                  (scopedSelectionSetSemanticsReady_append
                    ((scopedSelectionSetSemanticsReady_scopedSelectionSet
                      schema execParent liftParent selectionSet).mpr
                      (by
                        have hheadReady :
                            selectionSemanticsReady schema execParent
                              (Selection.inlineFragment none []
                                selectionSet) := by
                          unfold scopedSelectionSetSemanticsReady at hready
                          unfold selectionSetSemanticsReady at hready
                          exact hready _ (by simp [eraseScopedSelectionSet,
                            eraseScopedSelection])
                        simpa [selectionSemanticsReady] using hheadReady))
                    (scopedSelectionSetSemanticsReady_tail hready))
                  (scopedSelectionSetLookupValid_append
                    ((scopedSelectionSetLookupValid_scopedSelectionSet schema
                      liftParent selectionSet).mpr
                      (by
                        have hheadLookup :
                            selectionLookupValid schema liftParent
                              (Selection.inlineFragment none [] selectionSet) :=
                          hlookup
                            { liftParent := liftParent,
                              selection :=
                                Selection.inlineFragment none [] selectionSet }
                            (by simp)
                        simpa [selectionLookupValid] using hheadLookup))
                    (scopedSelectionSetLookupValid_tail hlookup))
                  (by
                    simpa [scopedSelectionSetCanMerge,
                      eraseScopedSelectionSet_append,
                      eraseScopedSelectionSet_scopedSelectionSet] using
                      fieldsInSetCanMerge_inlineFragment_none_flatten schema
                        execParent selectionSet (eraseScopedSelectionSet rest)
                        hmerge)
                  (scopedSelectionSetRuntimeApplies_append
                    (scopedSelectionSetRuntimeApplies_scopedSelectionSet schema
                      liftParent runtimeType selectionSet
                      (happlies
                        { liftParent := liftParent,
                          selection :=
                            Selection.inlineFragment none [] selectionSet }
                        (by simp)))
                    (scopedSelectionSetRuntimeApplies_tail happlies))
              | some typeCondition =>
              cases happly :
                  Execution.doesFragmentTypeApplyBool schema execParent
                    (.object runtimeType identity) typeCondition
              · apply executeSelectionSet_inlineFragment_some_groundLift_scoped_skip
                · exact happly
                · exact
                    groundLiftScopedSelectionSet_executeSelectionSet_on_store
                      schema store variableValues hschema hstore
                      depth execParent runtimeType identity rest hobject
                      hinclude (selectionSetDirectiveFree_tail hfree)
                      (scopedSelectionSetSemanticsReady_tail hready)
                      (scopedSelectionSetLookupValid_tail hlookup)
                      (scopedSelectionSetCanMerge_tail schema execParent
                        { liftParent := liftParent,
                          selection :=
                            Selection.inlineFragment (some typeCondition) []
                              selectionSet }
                        rest hmerge)
                      (scopedSelectionSetRuntimeApplies_tail happlies)
              · apply
                  executeSelectionSet_inlineFragment_some_groundLift_scoped_apply_flatten
                · exact happly
                · have htypeRuntime :
                      schema.typeIncludesObjectBool typeCondition runtimeType =
                        true := by
                    simpa [Execution.doesFragmentTypeApplyBool,
                      Execution.runtimeObjectType?] using happly
                  have hsource :
                      ∃ runtimeType' identity',
                        (Execution.Value.object runtimeType identity :
                            Execution.Value DataModel.ObjectPath)
                          = .object runtimeType' identity'
                          ∧ schema.typeIncludesObjectBool execParent
                            runtimeType' = true :=
                    ⟨runtimeType, identity, rfl, hinclude⟩
                  have hoverlap :
                      schema.typesOverlapBool execParent typeCondition =
                        true := by
                    rw [← doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
                      schema hobject hsource]
                    exact happly
                  exact
                    groundLiftScopedSelectionSet_executeSelectionSet_on_store
                      schema store variableValues hschema hstore
                      depth execParent runtimeType identity
                      (scopedSelectionSet typeCondition selectionSet ++ rest)
                      hobject hinclude
                      (scopedSelectionSetDirectiveFree_append
                        ((scopedSelectionSetDirectiveFree_scopedSelectionSet
                          typeCondition selectionSet).mpr
                          (by simpa [selectionDirectiveFree] using
                            hheadFree.2))
                        (selectionSetDirectiveFree_tail hfree))
                      (scopedSelectionSetSemanticsReady_append
                        ((scopedSelectionSetSemanticsReady_scopedSelectionSet
                          schema execParent typeCondition selectionSet).mpr
                          (by
                            have hheadReady :
                                selectionSemanticsReady schema execParent
                                  (Selection.inlineFragment
                                    (some typeCondition) [] selectionSet) := by
                              unfold scopedSelectionSetSemanticsReady at hready
                              unfold selectionSetSemanticsReady at hready
                              exact hready _ (by simp [eraseScopedSelectionSet,
                                eraseScopedSelection])
                            have hpair :
                                selectionSetLookupValid schema typeCondition
                                    selectionSet
                                  ∧
                                (schema.typesOverlapBool execParent
                                    typeCondition = true ->
                                  selectionSetSemanticsReady schema execParent
                                    selectionSet) := by
                              simpa [selectionSemanticsReady] using hheadReady
                            exact hpair.2 hoverlap))
                        (scopedSelectionSetSemanticsReady_tail hready))
                      (scopedSelectionSetLookupValid_append
                        ((scopedSelectionSetLookupValid_scopedSelectionSet schema
                          typeCondition selectionSet).mpr
                          (by
                            have hheadLookup :
                                selectionLookupValid schema liftParent
                                  (Selection.inlineFragment
                                    (some typeCondition) [] selectionSet) :=
                              hlookup
                                { liftParent := liftParent,
                                  selection :=
                                    Selection.inlineFragment
                                      (some typeCondition) [] selectionSet }
                                (by simp)
                            simpa [selectionLookupValid] using hheadLookup))
                        (scopedSelectionSetLookupValid_tail hlookup))
                      (by
                        have hselectionParentLookup :
                            selectionSetLookupValid schema execParent
                              selectionSet :=
                          selectionSetLookupValid_of_selectionSetSemanticsReady
                            selectionSet
                            (by
                              have hheadReady :
                                  selectionSemanticsReady schema execParent
                                    (Selection.inlineFragment
                                      (some typeCondition) [] selectionSet) := by
                                unfold scopedSelectionSetSemanticsReady at hready
                                unfold selectionSetSemanticsReady at hready
                                exact hready _ (by simp
                                  [eraseScopedSelectionSet,
                                    eraseScopedSelection])
                              have hpair :
                                  selectionSetLookupValid schema typeCondition
                                      selectionSet
                                    ∧
                                  (schema.typesOverlapBool execParent
                                      typeCondition = true ->
                                    selectionSetSemanticsReady schema execParent
                                      selectionSet) := by
                                simpa [selectionSemanticsReady] using hheadReady
                              exact hpair.2 hoverlap)
                        have hselectionTypeLookup :
                            selectionSetLookupValid schema typeCondition
                              selectionSet := by
                          have hheadLookup :
                              selectionLookupValid schema liftParent
                                (Selection.inlineFragment
                                  (some typeCondition) [] selectionSet) :=
                            hlookup
                              { liftParent := liftParent,
                                selection :=
                                  Selection.inlineFragment
                                    (some typeCondition) [] selectionSet }
                              (by simp)
                          simpa [selectionLookupValid] using hheadLookup
                        have htailLookup :
                            selectionSetLookupValid schema execParent
                              (eraseScopedSelectionSet rest) :=
                          selectionSetLookupValid_of_selectionSetSemanticsReady
                            (eraseScopedSelectionSet rest)
                            (scopedSelectionSetSemanticsReady_tail hready)
                        have hparentObject :
                            schema.objectType execParent :=
                          objectType_of_objectTypeNameBool_eq_true schema
                            hobject
                        simpa [scopedSelectionSetCanMerge,
                          eraseScopedSelectionSet_append,
                          eraseScopedSelectionSet_scopedSelectionSet] using
                          fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
                            schema execParent typeCondition selectionSet
                            (eraseScopedSelectionSet rest) hschema
                            hparentObject hoverlap hselectionParentLookup
                            hselectionTypeLookup htailLookup hmerge)
                      (scopedSelectionSetRuntimeApplies_append
                        (scopedSelectionSetRuntimeApplies_scopedSelectionSet
                          schema typeCondition runtimeType selectionSet
                          htypeRuntime)
                        (scopedSelectionSetRuntimeApplies_tail happlies))
termination_by _depth _execParent _runtimeType _identity scopedSelections =>
  SelectionSet.size (eraseScopedSelectionSet scopedSelections)
decreasing_by
  all_goals
    try
      exact
        eraseScopedSelectionSet_withoutFieldsWithResponseName_size_lt_field_directives
          schema liftParent responseName fieldName arguments directives
          subselections rest
    try
      simpa [eraseScopedSelectionSet_scopedSelectionSet] using
        eraseScopedSelectionSet_field_merged_subselections_size_lt_directives
          schema execParent liftParent responseName fieldName arguments
          directives subselections rest
    try
      exact
        eraseScopedSelectionSet_inlineFragment_none_flatten_size_lt liftParent
          selectionSet rest
    try
      exact
        eraseScopedSelectionSet_inlineFragment_some_flatten_size_lt liftParent
          typeCondition selectionSet rest
    try
      exact
        eraseScopedSelectionSet_tail_size_lt
          { liftParent := liftParent,
            selection :=
              Selection.inlineFragment (some typeCondition) [] selectionSet }
          rest

theorem groundLiftSelectionSet_executeSelectionSet_on_store_of_scoped
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues) :
    (∀ depth execParent runtimeType identity scopedSelections,
      objectTypeNameBool schema execParent = true ->
      schema.typeIncludesObjectBool execParent runtimeType = true ->
      scopedSelectionSetDirectiveFree scopedSelections ->
      scopedSelectionSetSemanticsReady schema execParent scopedSelections ->
      scopedSelectionSetLookupValid schema scopedSelections ->
      scopedSelectionSetCanMerge schema execParent scopedSelections ->
      scopedSelectionSetRuntimeApplies schema runtimeType scopedSelections ->
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth execParent (.object runtimeType identity)
          (groundLiftScopedSelectionSet schema scopedSelections)
        =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth execParent (.object runtimeType identity)
          (eraseScopedSelectionSet scopedSelections)) ->
      ∀ depth parentType runtimeType identity selectionSet,
        objectTypeNameBool schema parentType = true ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
        selectionSetDirectiveFree selectionSet ->
        selectionSetSemanticsReady schema parentType selectionSet ->
        FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues depth parentType (.object runtimeType identity)
            (groundLiftSelectionSet schema parentType selectionSet)
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues depth parentType (.object runtimeType identity)
            selectionSet := by
  intro hscoped depth parentType runtimeType identity selectionSet hobject
    hinclude hfree hready hmerge
  have hlookup :
      selectionSetLookupValid schema parentType selectionSet :=
    selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet hready
  have hscopedEq :=
    hscoped depth parentType runtimeType identity
      (scopedSelectionSet parentType selectionSet)
      hobject hinclude
      ((scopedSelectionSetDirectiveFree_scopedSelectionSet parentType
        selectionSet).mpr hfree)
      ((scopedSelectionSetSemanticsReady_scopedSelectionSet schema parentType
        parentType selectionSet).mpr hready)
      ((scopedSelectionSetLookupValid_scopedSelectionSet schema parentType
        selectionSet).mpr hlookup)
      ((scopedSelectionSetCanMerge_scopedSelectionSet schema parentType
        parentType selectionSet).mpr hmerge)
      (scopedSelectionSetRuntimeApplies_scopedSelectionSet schema parentType
        runtimeType selectionSet hinclude)
  simpa [groundLiftScopedSelectionSet_scopedSelectionSet,
    eraseScopedSelectionSet_scopedSelectionSet] using hscopedEq

end GroundTypeNormalization

end NormalForm

end GraphQL
