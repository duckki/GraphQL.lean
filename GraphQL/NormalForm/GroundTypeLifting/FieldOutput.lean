import GraphQL.NormalForm.GroundTypeLifting.ExecutionGroups
import GraphQL.DataModel.StoreValueInclusion

/-!
Field-output and value-inclusion lemmas for ground-type lifting proofs.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeLifting

open GroundTypeNormalization
open DataModel.Store

variable {ObjectIdentity : Type}

theorem possibleTypes_eq_nil_of_leafTypeNameBool
    (schema : Schema) {typeName : Name} :
    leafTypeNameBool schema typeName = true ->
      schema.getPossibleTypes typeName = [] := by
  intro hleaf
  unfold leafTypeNameBool at hleaf
  cases hlookup : schema.lookupType typeName with
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

theorem collectFields_groundLift_possibleTypeFragments_not_mem_eq_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (identity : ObjectIdentity)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      objectTypeNameBool schema objectType = true) ->
    runtimeType ∉ possibleTypes ->
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType selectionSet)))
      = [] := by
  intro hobjects hnotin
  induction possibleTypes with
  | nil =>
      simp [Execution.collectFields]
  | cons objectType rest ih =>
      have hobject : objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hne : objectType ≠ runtimeType := by
        intro heq
        subst objectType
        exact hnotin (by simp)
      have hrestNotin : runtimeType ∉ rest := by
        intro hmem
        exact hnotin (by simp [hmem])
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      rw [List.map_cons]
      rw [collectFields_inlineFragment_some_directiveFree_skip_eq]
      · exact ih hrestObjects hrestNotin
      · exact doesFragmentTypeApplyBool_object_other_false schema hobject hne

theorem collectFields_groundLift_possibleTypeFragments_runtime_branch_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (identity : ObjectIdentity)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType selectionSet)))
      =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (groundLiftSelectionSet schema runtimeType selectionSet) := by
  intro hobjects hnodup hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      rw [List.map_cons]
      cases hhead : objectType == runtimeType
      · have hne : objectType ≠ runtimeType := by
          intro heq
          subst objectType
          simp at hhead
        have hskip :
            Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType identity) objectType = false :=
          doesFragmentTypeApplyBool_object_other_false schema hobject hne
        rw [collectFields_inlineFragment_some_directiveFree_skip_eq]
        · have hrestMem : runtimeType ∈ rest := by
            cases List.mem_cons.mp hmem with
            | inl hmemHead =>
                exact False.elim (hne hmemHead.symm)
            | inr hmemRest => exact hmemRest
          exact ih hrestObjects hrestNodup hrestMem
        · exact hskip
      · have heq : objectType = runtimeType := beq_iff_eq.mp hhead
        subst objectType
        have hrestNotin : runtimeType ∉ rest :=
          (List.nodup_cons.mp hnodup).1
        have happly :
            Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType identity) runtimeType = true :=
          doesFragmentTypeApplyBool_object_self schema hobject
        rw [collectFields_inlineFragment_some_directiveFree_apply_flatten]
        · rw [collectFields_append]
          rw [collectFields_groundLift_possibleTypeFragments_not_mem_eq_nil
            schema variableValues runtimeType identity rest selectionSet
            hrestObjects hrestNotin]
          simp [Execution.mergeExecutableGroups_nil_right]
        · exact happly

theorem collectFields_groundLift_fieldOutput_eq_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (expectedType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) :
    objectTypeNameBool schema runtimeType = true ->
    schema.typeIncludesObjectBool expectedType runtimeType = true ->
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (if leafTypeNameBool schema expectedType then
          []
        else if objectTypeNameBool schema expectedType then
          groundLiftSelectionSet schema expectedType selectionSet
        else
          (groundObjectTypesForType schema expectedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
      =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (groundLiftSelectionSet schema runtimeType selectionSet) := by
  intro hruntimeObject hinclude
  by_cases hleaf : leafTypeNameBool schema expectedType = true
  · have hnil := possibleTypes_eq_nil_of_leafTypeNameBool schema hleaf
    have hmem : runtimeType ∈ schema.getPossibleTypes expectedType :=
      List.contains_iff_mem.mp hinclude
    rw [hnil] at hmem
    cases hmem
  · have hleafFalse : leafTypeNameBool schema expectedType = false := by
      cases hmatch : leafTypeNameBool schema expectedType
      · rfl
      · exact False.elim (hleaf hmatch)
    by_cases hobject : objectTypeNameBool schema expectedType = true
    · have hruntimeEq : runtimeType = expectedType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hobject hinclude
      subst runtimeType
      simp [hleafFalse, hobject]
    · have hobjectFalse :
          objectTypeNameBool schema expectedType = false := by
        cases hmatch : objectTypeNameBool schema expectedType
        · rfl
        · exact False.elim (hobject hmatch)
      have hmem : runtimeType ∈ schema.getPossibleTypes expectedType :=
        List.contains_iff_mem.mp hinclude
      have hobjects :
          ∀ objectType, objectType ∈ schema.getPossibleTypes expectedType ->
            objectTypeNameBool schema objectType = true := by
        intro objectType hobjectType
        exact objectTypeNameBool_eq_true_of_objectType schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema expectedType objectType hobjectType)
      simp [hleafFalse, hobjectFalse, groundObjectTypesForType]
      exact collectFields_groundLift_possibleTypeFragments_runtime_branch_eq
        schema variableValues runtimeType identity
        (schema.getPossibleTypes expectedType) selectionSet hobjects
        (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
          expectedType)
        hmem

theorem collectFields_mergeSelectionSets_groundLiftScopedSelectionSet_eq_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (runtimeType : Name) (identity : ObjectIdentity)
    (scopedSelections : List ScopedSelection) :
    objectTypeNameBool schema runtimeType = true ->
    (∀ scopedSelection, scopedSelection ∈ scopedSelections ->
      ∃ responseName fieldName arguments directives subselections
          fieldDefinition,
        scopedSelection.selection =
          Selection.field responseName fieldName arguments directives
            subselections
          ∧ schema.lookupField scopedSelection.liftParent fieldName =
            some fieldDefinition
          ∧ schema.typeIncludesObjectBool
            fieldDefinition.outputType.namedType runtimeType = true) ->
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (mergeSelectionSets
          (groundLiftScopedSelectionSet schema scopedSelections))
      =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (groundLiftSelectionSet schema runtimeType
          (mergeSelectionSets
            (eraseScopedSelectionSet scopedSelections))) := by
  intro hruntimeObject hfields
  induction scopedSelections with
  | nil =>
      simp [groundLiftScopedSelectionSet, eraseScopedSelectionSet,
        mergeSelectionSets, groundLiftSelectionSet]
  | cons scopedSelection rest ih =>
      have hhead := hfields scopedSelection (by simp)
      have hrestFields :
          ∀ scopedSelection, scopedSelection ∈ rest ->
            ∃ responseName fieldName arguments directives subselections
                fieldDefinition,
              scopedSelection.selection =
                Selection.field responseName fieldName arguments directives
                  subselections
                ∧ schema.lookupField scopedSelection.liftParent fieldName =
                  some fieldDefinition
                ∧ schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType runtimeType = true := by
        intro candidate hcandidate
        exact hfields candidate (by simp [hcandidate])
      rcases hhead with
        ⟨responseName, fieldName, arguments, directives, subselections,
          fieldDefinition, hselection, hlookup, hinclude⟩
      cases scopedSelection with
      | mk liftParent selection =>
          have hselection' :
              selection =
                Selection.field responseName fieldName arguments directives
                  subselections := by
            simpa using hselection
          subst selection
          have hheadCollect :=
            collectFields_groundLift_fieldOutput_eq_runtime schema
              variableValues hschema fieldDefinition.outputType.namedType
              runtimeType identity subselections hruntimeObject hinclude
          have hrestCollect := ih hrestFields
          simp [groundLiftScopedSelectionSet, groundLiftScopedSelection,
            groundLiftSelection, hlookup, eraseScopedSelectionSet,
            eraseScopedSelection, mergeSelectionSets, Selection.subselections]
          rw [collectFields_append]
          rw [groundLiftSelectionSet_append]
          rw [collectFields_append]
          rw [hheadCollect]
          exact congrArg
            (fun groups =>
              Execution.mergeExecutableGroups
                (Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType identity)
                  (groundLiftSelectionSet schema runtimeType subselections))
                groups)
            hrestCollect

theorem executeSelectionSet_fieldOutput_scopedMerged_eq_of_runtime_recursive
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (expectedType runtimeType : Name)
    (identity : DataModel.ObjectPath)
    (selectionSet : List Selection)
    (scopedMatches : List ScopedSelection) :
    objectTypeNameBool schema runtimeType = true ->
    schema.typeIncludesObjectBool expectedType runtimeType = true ->
    (∀ scopedSelection, scopedSelection ∈ scopedMatches ->
      ∃ responseName fieldName arguments directives subselections
          fieldDefinition,
        scopedSelection.selection =
          Selection.field responseName fieldName arguments directives
            subselections
          ∧ schema.lookupField scopedSelection.liftParent fieldName =
            some fieldDefinition
          ∧ schema.typeIncludesObjectBool
            fieldDefinition.outputType.namedType runtimeType = true) ->
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth runtimeType (.object runtimeType identity)
      (groundLiftSelectionSet schema runtimeType
        (selectionSet
          ++ mergeSelectionSets
            (eraseScopedSelectionSet scopedMatches)))
      =
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth runtimeType (.object runtimeType identity)
      (selectionSet
        ++ mergeSelectionSets
          (eraseScopedSelectionSet scopedMatches)) ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth runtimeType (.object runtimeType identity)
        ((if leafTypeNameBool schema expectedType then
          []
        else if objectTypeNameBool schema expectedType then
          groundLiftSelectionSet schema expectedType selectionSet
        else
          (groundObjectTypesForType schema expectedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
          ++ mergeSelectionSets
            (groundLiftScopedSelectionSet schema scopedMatches))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth runtimeType (.object runtimeType identity)
        (selectionSet
          ++ mergeSelectionSets
            (eraseScopedSelectionSet scopedMatches)) := by
  intro hruntimeObject hinclude hmatches hrecursive
  have hleftCollect :
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        ((if leafTypeNameBool schema expectedType then
          []
        else if objectTypeNameBool schema expectedType then
          groundLiftSelectionSet schema expectedType selectionSet
        else
          (groundObjectTypesForType schema expectedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
          ++ mergeSelectionSets
            (groundLiftScopedSelectionSet schema scopedMatches))
      =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (groundLiftSelectionSet schema runtimeType
          (selectionSet
            ++ mergeSelectionSets
              (eraseScopedSelectionSet scopedMatches))) := by
    rw [collectFields_append]
    rw [groundLiftSelectionSet_append]
    rw [collectFields_append]
    rw [collectFields_groundLift_fieldOutput_eq_runtime schema
      variableValues hschema expectedType runtimeType identity selectionSet
      hruntimeObject hinclude]
    rw [collectFields_mergeSelectionSets_groundLiftScopedSelectionSet_eq_runtime
      schema variableValues hschema runtimeType identity scopedMatches
      hruntimeObject hmatches]
  have hleftToGround :
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth runtimeType (.object runtimeType identity)
        ((if leafTypeNameBool schema expectedType then
          []
        else if objectTypeNameBool schema expectedType then
          groundLiftSelectionSet schema expectedType selectionSet
        else
          (groundObjectTypesForType schema expectedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
          ++ mergeSelectionSets
            (groundLiftScopedSelectionSet schema scopedMatches))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth runtimeType (.object runtimeType identity)
        (groundLiftSelectionSet schema runtimeType
          (selectionSet
            ++ mergeSelectionSets
              (eraseScopedSelectionSet scopedMatches))) := by
    simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hleftCollect]
  exact hleftToGround.trans hrecursive

def scopedFieldOutputValuesInclude (schema : Schema)
    (value : Execution.Value DataModel.ObjectPath)
    (scopedSelections : List ScopedSelection) : Prop :=
  ∀ scopedSelection, scopedSelection ∈ scopedSelections ->
    ∃ responseName fieldName arguments directives subselections
        fieldDefinition,
      scopedSelection.selection =
        Selection.field responseName fieldName arguments directives
          subselections
        ∧ schema.lookupField scopedSelection.liftParent fieldName =
          some fieldDefinition
        ∧ executionValueObjectsInclude schema
          fieldDefinition.outputType.namedType value

theorem scopedSelectionSetValidFieldsWithResponseName_valuesInclude_on_store
    (schema : Schema) (store : DataModel.Store)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (execParent runtimeType : Name) (identity : DataModel.ObjectPath)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection) :
    objectTypeNameBool schema execParent = true ->
    schema.typeIncludesObjectBool execParent runtimeType = true ->
    selectionSetLookupValid schema execParent
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest) ->
    FieldMerge.fieldsInSetCanMerge schema execParent
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest) ->
    scopedSelectionSetRuntimeApplies schema runtimeType rest ->
    scopedSelectionSetLookupValid schema rest ->
      scopedFieldOutputValuesInclude schema
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType identity))
        (scopedSelectionSetValidFieldsWithResponseName schema execParent
          responseName rest) := by
  intro hobject hinclude hlookupRaw hmerge happlies hlookupScoped
  intro scopedSelection hscoped
  rcases
    scopedSelectionSetValidFieldsWithResponseName_mem_field schema
      execParent responseName rest scopedSelection hscoped with
    ⟨matchedFieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hshape⟩
  have hmatchesLookup :
      scopedSelectionSetLookupValid schema
        (scopedSelectionSetValidFieldsWithResponseName schema execParent
          responseName rest) :=
    scopedSelectionSetValidFieldsWithResponseName_lookupValid schema
      execParent responseName rest hlookupScoped
  have hmatchedLookupSelection :
      selectionLookupValid schema scopedSelection.liftParent
        scopedSelection.selection :=
    hmatchesLookup scopedSelection hscoped
  have hmatchedLookupField :
      ∃ fieldDefinition,
        schema.lookupField scopedSelection.liftParent matchedFieldName =
          some fieldDefinition := by
    simpa [hshape, selectionLookupValid] using hmatchedLookupSelection
  rcases hmatchedLookupField with ⟨fieldDefinition, hmatchedLookup⟩
  have hmatchedErased :
      scopedSelection.selection ∈
        eraseScopedSelectionSet
          (scopedSelectionSetValidFieldsWithResponseName schema execParent
            responseName rest) :=
    eraseScopedSelectionSet_mem_selection hscoped
  rw [eraseScopedSelectionSet_validFieldsWithResponseName schema
    execParent responseName rest] at hmatchedErased
  rw [hshape] at hmatchedErased
  have hparentObject : schema.objectType execParent :=
    objectType_of_objectTypeNameBool_eq_true schema hobject
  have hsameField :
      matchedFieldName = fieldName :=
    validFieldsWithResponseName_matching_same_field_of_canMerge_object_lookupValid
      schema execParent responseName fieldName arguments subselections
      (eraseScopedSelectionSet rest) hparentObject hlookupRaw hmerge
      matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatchedErased
  subst matchedFieldName
  have hmatchApplies :
      schema.typeIncludesObjectBool scopedSelection.liftParent runtimeType =
        true :=
    scopedSelectionSetValidFieldsWithResponseName_runtimeApplies schema
      execParent responseName runtimeType rest hobject hinclude happlies
      scopedSelection hscoped
  have hincludeValue :
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        (store.resolve schema fieldName arguments
          (.object runtimeType identity)) :=
    resolve_objectsInclude_of_static_lookupField schema store
      scopedSelection.liftParent runtimeType identity fieldName arguments
      fieldDefinition hschema hstore hmatchApplies hmatchedLookup
  refine ⟨responseName, fieldName, matchedArguments, matchedDirectives,
    matchedSubselections, fieldDefinition, hshape, hmatchedLookup, ?_⟩
  simpa [DataModel.Store.resolvers] using hincludeValue

theorem scopedFieldHead_valueIncludes_on_store
    (schema : Schema) (store : DataModel.Store)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (execParent liftParent runtimeType : Name)
    (identity : DataModel.ObjectPath)
    (fieldName : Name) (arguments : List Argument)
    (liftFieldDefinition : FieldDefinition) :
    schema.typeIncludesObjectBool liftParent runtimeType = true ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
      executionValueObjectsInclude schema
        liftFieldDefinition.outputType.namedType
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType identity)) := by
  intro hliftInclude hliftLookup
  have hincludeValue :
      executionValueObjectsInclude schema
        liftFieldDefinition.outputType.namedType
        (store.resolve schema fieldName arguments
          (.object runtimeType identity)) :=
    resolve_objectsInclude_of_static_lookupField schema store liftParent
      runtimeType identity fieldName arguments liftFieldDefinition hschema
      hstore hliftInclude hliftLookup
  simpa [DataModel.Store.resolvers] using hincludeValue

theorem completeValue_fieldOutput_scopedMerged_eq_of_valueObjectsInclude_lt
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth actualType expectedType selectionSet scopedMatches value,
      executionValueObjectsInclude schema expectedType value ->
      scopedFieldOutputValuesInclude schema value scopedMatches ->
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool actualType runtimeType = true ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType identity)
            (groundLiftSelectionSet schema runtimeType
              (selectionSet
                ++ mergeSelectionSets
                  (eraseScopedSelectionSet scopedMatches)))
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType identity)
            (selectionSet
              ++ mergeSelectionSets
                (eraseScopedSelectionSet scopedMatches))) ->
        Execution.completeValue schema (store.resolvers schema)
          variableValues depth actualType
          [completeValueSelectionSetField actualType
            ((if leafTypeNameBool schema expectedType then
              []
            else if objectTypeNameBool schema expectedType then
              groundLiftSelectionSet schema expectedType selectionSet
            else
              (groundObjectTypesForType schema expectedType).map
                (fun objectType =>
                  Selection.inlineFragment (some objectType) []
                    (groundLiftSelectionSet schema objectType selectionSet)))
              ++ mergeSelectionSets
                (groundLiftScopedSelectionSet schema scopedMatches))]
          value
        =
        Execution.completeValue schema (store.resolvers schema)
          variableValues depth actualType
          [completeValueSelectionSetField actualType
            (selectionSet
              ++ mergeSelectionSets
                (eraseScopedSelectionSet scopedMatches))]
          value
  | 0, _actualType, _expectedType, _selectionSet, _scopedMatches, _value,
    _hheadInclude, _hmatchesInclude, _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, actualType, expectedType, selectionSet, scopedMatches, value,
    hheadInclude, hmatchesInclude, hrecursive => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType identity =>
          by_cases hactual :
              schema.typeIncludesObjectBool actualType runtimeType = true
          · have hheadRuntime :
                schema.typeIncludesObjectBool expectedType runtimeType = true := by
              simpa [executionValueObjectsInclude] using hheadInclude
            have hmatchesRuntime :
                ∀ scopedSelection, scopedSelection ∈ scopedMatches ->
                  ∃ responseName fieldName arguments directives subselections
                      fieldDefinition,
                    scopedSelection.selection =
                      Selection.field responseName fieldName arguments
                        directives subselections
                      ∧ schema.lookupField scopedSelection.liftParent
                        fieldName = some fieldDefinition
                      ∧ schema.typeIncludesObjectBool
                        fieldDefinition.outputType.namedType runtimeType =
                          true := by
              intro scopedSelection hscoped
              rcases hmatchesInclude scopedSelection hscoped with
                ⟨responseName, fieldName, arguments, directives,
                  subselections, fieldDefinition, hselection, hlookup,
                  hinclude⟩
              refine ⟨responseName, fieldName, arguments, directives,
                subselections, fieldDefinition, hselection, hlookup, ?_⟩
              simpa [executionValueObjectsInclude] using hinclude
            have hruntimeObject :
                objectTypeNameBool schema runtimeType = true := by
              exact objectTypeNameBool_eq_true_of_objectType schema
                (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  hschema actualType runtimeType
                  (List.contains_iff_mem.mp hactual))
            have hselection :=
              executeSelectionSet_fieldOutput_scopedMerged_eq_of_runtime_recursive
                schema store variableValues hschema depth expectedType
                runtimeType identity selectionSet scopedMatches
                hruntimeObject hheadRuntime hmatchesRuntime
                (hrecursive depth runtimeType identity
                  (Nat.lt_succ_self depth) hactual)
            simp [Execution.completeValue, hactual]
            simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
              Execution.collectSubfields, completeValueSelectionSetField]
              using hselection
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
                executionValueObjectsInclude schema expectedType value := by
            simpa [executionValueObjectsInclude] using hheadInclude
          have hmatchesElements :
              ∀ value, value ∈ values ->
                scopedFieldOutputValuesInclude schema value
                  scopedMatches := by
            intro value hvalue scopedSelection hscoped
            rcases hmatchesInclude scopedSelection hscoped with
              ⟨responseName, fieldName, arguments, directives,
                subselections, fieldDefinition, hselection, hlookup,
                hinclude⟩
            refine ⟨responseName, fieldName, arguments, directives,
              subselections, fieldDefinition, hselection, hlookup, ?_⟩
            have hincludeElements :
                ∀ value, value ∈ values ->
                  executionValueObjectsInclude schema
                    fieldDefinition.outputType.namedType value := by
              simpa [executionValueObjectsInclude] using hinclude
            exact hincludeElements value hvalue
          simp [Execution.completeValue]
          intro element helement
          exact
            completeValue_fieldOutput_scopedMerged_eq_of_valueObjectsInclude_lt
              schema store variableValues hschema depth actualType
              expectedType selectionSet scopedMatches element
              (hheadElements element helement)
              (hmatchesElements element helement)
              (by
                intro childDepth runtimeType identity hlt hinclude
                exact hrecursive childDepth runtimeType identity
                  (Nat.lt_trans hlt (Nat.lt_succ_self depth)) hinclude)

theorem executeSelectionSet_field_head_groundLift_scoped_sameGroup_of_valueIncludes
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (fieldDepth : Nat) (execParent liftParent runtimeType : Name)
    (identity : DataModel.ObjectPath)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection)
    (liftedFields sourceFields : List Execution.ExecutableField)
    (liftedRestGroups sourceRest : List (Name × List Execution.ExecutableField))
    (execFieldDefinition liftFieldDefinition : FieldDefinition) :
    let liftedSelectionSet :=
      if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
        []
      else if objectTypeNameBool schema liftFieldDefinition.outputType.namedType
      then
        groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
          subselections
      else
        (groundObjectTypesForType schema
          liftFieldDefinition.outputType.namedType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType subselections))
    let liftedField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := liftedSelectionSet
      }
    let sourceField : Execution.ExecutableField :=
      {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
    objectTypeNameBool schema execParent = true ->
    schema.typeIncludesObjectBool execParent runtimeType = true ->
    scopedSelectionSetDirectiveFree
      ({ liftParent := liftParent,
         selection :=
          Selection.field responseName fieldName arguments [] subselections }
        :: rest) ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    Execution.collectFields schema variableValues execParent
      (.object runtimeType identity)
      (groundLiftScopedSelectionSet schema
        ({ liftParent := liftParent,
           selection :=
            Selection.field responseName fieldName arguments [] subselections }
          :: rest))
      =
    (responseName, liftedField :: liftedFields) :: liftedRestGroups ->
    Execution.collectFields schema variableValues execParent
      (.object runtimeType identity)
      (Selection.field responseName fieldName arguments [] subselections
        :: eraseScopedSelectionSet rest)
      =
    (responseName, sourceField :: sourceFields) :: sourceRest ->
    executionValueObjectsInclude schema
      liftFieldDefinition.outputType.namedType
      ((store.resolvers schema).resolve execParent fieldName arguments
        (.object runtimeType identity)) ->
    scopedFieldOutputValuesInclude schema
      ((store.resolvers schema).resolve execParent fieldName arguments
        (.object runtimeType identity))
      (scopedSelectionSetValidFieldsWithResponseName schema execParent
        responseName rest) ->
    (∀ childDepth childRuntimeType childIdentity,
      childDepth < fieldDepth ->
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
    Execution.executeCollectedFields schema (store.resolvers schema)
      variableValues (fieldDepth + 1) (.object runtimeType identity)
      liftedRestGroups
      =
    Execution.executeCollectedFields schema (store.resolvers schema)
      variableValues (fieldDepth + 1) (.object runtimeType identity)
      sourceRest ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues (fieldDepth + 1) execParent
        (.object runtimeType identity)
        (groundLiftScopedSelectionSet schema
          ({ liftParent := liftParent,
             selection :=
              Selection.field responseName fieldName arguments []
                subselections }
            :: rest))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues (fieldDepth + 1) execParent
        (.object runtimeType identity)
        (Selection.field responseName fieldName arguments [] subselections
          :: eraseScopedSelectionSet rest) := by
  intro liftedSelectionSet liftedField sourceField hobject hinclude hfree
    hexecLookup hliftLookup hliftCollect hsourceCollect hheadInclude
    hmatchesInclude hrecursive htail
  apply executeSelectionSet_field_head_groundLift_scoped_sameGroup_of_completeValue
    schema store variableValues fieldDepth execParent liftParent runtimeType
    identity responseName fieldName arguments subselections rest liftedFields
    sourceFields liftedRestGroups sourceRest execFieldDefinition
    liftFieldDefinition hobject hinclude hfree hexecLookup hliftLookup
    hliftCollect hsourceCollect
  · have hsource :
        ∃ runtimeType' identity',
          (Execution.Value.object runtimeType identity :
              Execution.Value DataModel.ObjectPath)
            = .object runtimeType' identity'
            ∧ schema.typeIncludesObjectBool execParent runtimeType' = true :=
      ⟨runtimeType, identity, rfl, hinclude⟩
    have hsource :
        ∃ runtimeType' identity',
          (Execution.Value.object runtimeType identity :
              Execution.Value DataModel.ObjectPath)
            = .object runtimeType' identity'
            ∧ schema.typeIncludesObjectBool execParent runtimeType' = true :=
      hsource
    have hsourceFree :
        selectionSetDirectiveFree
          (Selection.field responseName fieldName arguments []
            subselections :: eraseScopedSelectionSet rest) := by
      simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet,
        eraseScopedSelection] using hfree
    have hliftProjection :=
      mergedFieldSelectionSet_groundLift_scoped_field_head_eq_validFields
        schema variableValues execParent liftParent
        (.object runtimeType identity) responseName fieldName arguments
        subselections rest liftedFields liftedRestGroups liftFieldDefinition
        hobject hsource hfree hliftLookup hliftCollect
    have hsourceProjection :=
      mergedFieldSelectionSet_field_head_eq_validFieldsWithResponseName
        schema variableValues execParent (.object runtimeType identity)
        responseName fieldName arguments subselections
        (eraseScopedSelectionSet rest) sourceFields sourceRest hobject hsource
        hsourceFree hsourceCollect
    have hcomplete :=
      completeValue_fieldOutput_scopedMerged_eq_of_valueObjectsInclude_lt
        schema store variableValues hschema fieldDepth
        ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        liftFieldDefinition.outputType.namedType subselections
        (scopedSelectionSetValidFieldsWithResponseName schema execParent
          responseName rest)
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType identity))
        hheadInclude hmatchesInclude hrecursive
    have hleft :
        Execution.completeValue schema (store.resolvers schema) variableValues
          fieldDepth
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          (liftedField :: liftedFields)
          ((store.resolvers schema).resolve execParent fieldName arguments
            (.object runtimeType identity))
        =
        Execution.completeValue schema (store.resolvers schema) variableValues
          fieldDepth
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          [completeValueSelectionSetField
            ((schema.fieldReturnType? execParent fieldName).getD fieldName)
            (liftedSelectionSet
              ++ mergeSelectionSets
                (groundLiftScopedSelectionSet schema
                  (scopedSelectionSetValidFieldsWithResponseName schema
                    execParent responseName rest)))]
          ((store.resolvers schema).resolve execParent fieldName arguments
            (.object runtimeType identity)) := by
      apply completeValue_eq_of_mergedFieldSelectionSet_eq schema
        (store.resolvers schema) variableValues fieldDepth
        ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        (liftedField :: liftedFields)
        [completeValueSelectionSetField
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          (liftedSelectionSet
            ++ mergeSelectionSets
              (groundLiftScopedSelectionSet schema
                (scopedSelectionSetValidFieldsWithResponseName schema
                  execParent responseName rest)))]
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType identity))
      simpa [Execution.mergedFieldSelectionSet, completeValueSelectionSetField,
        liftedField, liftedSelectionSet] using hliftProjection
    have hright :
        Execution.completeValue schema (store.resolvers schema) variableValues
          fieldDepth
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          (sourceField :: sourceFields)
          ((store.resolvers schema).resolve execParent fieldName arguments
            (.object runtimeType identity))
        =
        Execution.completeValue schema (store.resolvers schema) variableValues
          fieldDepth
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          [completeValueSelectionSetField
            ((schema.fieldReturnType? execParent fieldName).getD fieldName)
            (subselections
              ++ mergeSelectionSets
                (eraseScopedSelectionSet
                  (scopedSelectionSetValidFieldsWithResponseName schema
                    execParent responseName rest)))]
          ((store.resolvers schema).resolve execParent fieldName arguments
            (.object runtimeType identity)) := by
      apply completeValue_eq_of_mergedFieldSelectionSet_eq schema
        (store.resolvers schema) variableValues fieldDepth
        ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        (sourceField :: sourceFields)
        [completeValueSelectionSetField
          ((schema.fieldReturnType? execParent fieldName).getD fieldName)
          (subselections
            ++ mergeSelectionSets
              (eraseScopedSelectionSet
                (scopedSelectionSetValidFieldsWithResponseName schema
                  execParent responseName rest)))]
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType identity))
      simpa [Execution.mergedFieldSelectionSet, completeValueSelectionSetField,
        sourceField, eraseScopedSelectionSet_validFieldsWithResponseName schema
          execParent responseName rest] using hsourceProjection
    exact hleft.trans (hcomplete.trans hright.symm)
  · exact htail

end GroundTypeLifting

end NormalForm

end GraphQL
