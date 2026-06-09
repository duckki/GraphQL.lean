import GraphQL.NormalForm.CompleteNormalization.RuntimeTypes

/-!
BoolCase-threaded child selection-set execution facts for complete normalization.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem completeScopedSelectionRuntimeReady_staticScopedFieldsWithResponseName_of_outputsInclude
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName runtimeType : Name)
    (selectionSet : List Selection) :
    completeScopedFieldOutputsInclude schema runtimeType
      (staticScopedFieldsWithResponseName schema boolCase lookupParent
        groundType responseName selectionSet) ->
    ∀ scopedSelection,
      scopedSelection ∈
          staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet ->
        completeScopedSelectionRuntimeReady schema boolCase runtimeType
          scopedSelection := by
  intro houtputs scopedSelection hmem
  rcases houtputs scopedSelection hmem with
    ⟨fieldResponseName, fieldName, arguments, directives, subselections,
      fieldDefinition, hselection, hlookup, hinclude⟩
  rw [completeScopedSelectionRuntimeReady, hselection]
  constructor
  · exact
      staticScopedFieldsWithResponseName_mem_field_allowed schema boolCase
        lookupParent groundType responseName selectionSet scopedSelection
        fieldResponseName fieldName arguments directives subselections hmem
        hselection
  · refine ⟨fieldDefinition, hlookup, ?_, ?_⟩
    · cases hleaf :
        leafTypeNameBool schema fieldDefinition.outputType.namedType
      · rfl
      · have hfalse :=
          typeIncludesObjectBool_false_of_leafTypeNameBool schema
            fieldDefinition.outputType.namedType runtimeType hleaf
        rw [hinclude] at hfalse
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
              rw [hinclude] at hfalse
              cases hfalse)
          hinclude

theorem completeValue_eq_of_leafTypeNameBool
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (returnType : Name) (left right : List Selection) :
    ∀ depth value,
      leafTypeNameBool schema returnType = true ->
        Execution.completeValue schema resolvers variableValues depth
            returnType left value
          =
        Execution.completeValue schema resolvers variableValues depth
          returnType right value
  | 0, value, _hleaf => by
      simp [Execution.completeValue]
  | depth + 1, .null, _hleaf => by
      simp [Execution.completeValue]
  | depth + 1, .scalar value, _hleaf => by
      simp [Execution.completeValue]
  | depth + 1, .object runtimeType identity, hleaf => by
      have hincludesFalse :
          schema.typeIncludesObjectBool returnType runtimeType = false :=
        typeIncludesObjectBool_false_of_leafTypeNameBool schema returnType
          runtimeType hleaf
      simp [Execution.completeValue, hincludesFalse]
  | depth + 1, .list values, hleaf => by
      induction values with
      | nil =>
          simp [Execution.completeValue]
      | cons value rest ih =>
          simp [Execution.completeValue,
            completeValue_eq_of_leafTypeNameBool schema resolvers
              variableValues returnType left right depth value hleaf]
          intro value hvalue
          exact completeValue_eq_of_leafTypeNameBool schema resolvers
            variableValues returnType left right depth value hleaf

theorem collectFields_normalizeForTypeIn_object_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (returnType : Name) (source : Execution.Value ObjectIdentity)
    (selectionSet : List Selection) :
    objectTypeNameBool schema returnType = true ->
      Execution.collectFields schema variableValues returnType source
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet)
        =
      Execution.collectFields schema variableValues returnType source
        (staticCollectForGround schema variables returnType
          returnType boolCase selectionSet) := by
  intro hobject
  have hleafFalse :
      leafTypeNameBool schema returnType = false :=
    leafTypeNameBool_false_of_objectTypeNameBool_true schema hobject
  simp [normalizeForTypeIn, hleafFalse,
    hobject]

theorem collectFields_possibleTypeStaticCollectWithCase_not_mem_eq_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
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
              (staticCollectForGround schema variables objectType
                objectType boolCase selectionSet)))
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
      rw [GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq]
      · exact ih hrestObjects hrestNotin
      · exact GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
          schema hobject hne

theorem collectFields_possibleTypeStaticCollectWithCase_runtime_branch
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
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
              (staticCollectForGround schema variables objectType
                objectType boolCase selectionSet)))
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase selectionSet) := by
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
      have hrestNodup : rest.Nodup := by
        exact hnodup.tail
      rw [List.map_cons]
      cases hhead : objectType == runtimeType
      · have hne : objectType ≠ runtimeType := by
          intro heq
          subst objectType
          simp at hhead
        have hskip :
            Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType identity) objectType = false :=
          GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
            schema hobject hne
        rw [GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
          schema variableValues runtimeType objectType
          (.object runtimeType identity)
          (staticCollectForGround schema variables objectType
            objectType boolCase selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (staticCollectForGround schema variables
                  objectType objectType boolCase selectionSet)))
          hskip]
        have hrestMem : runtimeType ∈ rest := by
          cases List.mem_cons.mp hmem with
          | inl hmemHead =>
              exact False.elim (hne hmemHead.symm)
          | inr hmemRest => exact hmemRest
        exact ih hrestObjects hrestNodup hrestMem
      · have heq : objectType = runtimeType :=
          beq_iff_eq.mp hhead
        subst objectType
        have hrestNotin : runtimeType ∉ rest := by
          exact (List.nodup_cons.mp hnodup).1
        have happly :
            Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType identity) runtimeType = true :=
          GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
            schema hobject
        rw [GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_apply_flatten
          schema variableValues runtimeType runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema variables runtimeType
            runtimeType boolCase selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (staticCollectForGround schema variables
                  objectType objectType boolCase selectionSet)))
          happly]
        have hrestCollect :
            Execution.collectFields schema variableValues runtimeType
                (.object runtimeType identity)
                (rest.map
                  (fun objectType =>
                    Selection.inlineFragment (some objectType) []
                      (staticCollectForGround schema variables
                        objectType objectType boolCase selectionSet)))
              =
            [] :=
          collectFields_possibleTypeStaticCollectWithCase_not_mem_eq_nil
            schema variableValues variables boolCase runtimeType identity rest
            selectionSet hrestObjects hrestNotin
        rw [collectFields_append_right_nil schema variableValues runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema variables runtimeType
            runtimeType boolCase selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (staticCollectForGround schema variables
                  objectType objectType boolCase selectionSet)))
          hrestCollect]

theorem collectFields_normalizeForTypeIn_abstract_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) :
    leafTypeNameBool schema returnType = false ->
    objectTypeNameBool schema returnType = false ->
    (∀ objectType, objectType ∈ groundObjectTypesForType schema returnType ->
      objectTypeNameBool schema objectType = true) ->
    (groundObjectTypesForType schema returnType).Nodup ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet)
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase selectionSet) := by
  intro hleafFalse hobjectFalse hobjects hnodup hmem
  simp [normalizeForTypeIn, hleafFalse,
    hobjectFalse]
  exact collectFields_possibleTypeStaticCollectWithCase_runtime_branch
    schema variableValues variables boolCase runtimeType identity
    (groundObjectTypesForType schema returnType) selectionSet hobjects hnodup
    hmem

theorem collectFields_normalizeForTypeIn_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) :
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    (∀ objectType, objectType ∈ groundObjectTypesForType schema returnType ->
      objectTypeNameBool schema objectType = true) ->
    (groundObjectTypesForType schema returnType).Nodup ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet)
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase selectionSet) := by
  intro hleafFalse hmem hobjects hnodup
  cases hobject : objectTypeNameBool schema returnType with
  | false =>
      exact
        collectFields_normalizeForTypeIn_abstract_runtime
          schema variableValues variables boolCase returnType runtimeType
          identity selectionSet hleafFalse hobject hobjects hnodup hmem
  | true =>
      have hruntimeEq : runtimeType = returnType := by
        unfold groundObjectTypesForType at hmem
        simp [hobject] at hmem
        exact hmem
      subst runtimeType
      exact
        collectFields_normalizeForTypeIn_object_runtime
          schema variableValues variables boolCase returnType
          (.object returnType identity) selectionSet hobject

theorem collectFields_normalizeForTypeIn_runtime_of_schemaWellFormed
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet)
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase selectionSet) := by
  intro hschema hleafFalse hmem
  exact
    collectFields_normalizeForTypeIn_runtime
      schema variableValues variables boolCase returnType runtimeType
      identity selectionSet hleafFalse hmem
      (groundObjectTypesForType_objects schema hschema returnType)
      (groundObjectTypesForType_nodup schema hschema returnType)

theorem executeSelectionSet_normalizeForTypeIn_runtime_of_schemaWellFormed
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (depth : Nat)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
      Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase selectionSet) := by
  intro hschema hleafFalse hmem
  apply executeSelectionSet_eq_of_collectFields_eq
  exact
    collectFields_normalizeForTypeIn_runtime_of_schemaWellFormed
      schema variableValues variables boolCase returnType runtimeType identity
      selectionSet hschema hleafFalse hmem

theorem collectFields_normalizeForTypeIn_append_runtime_of_schemaWellFormed
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (left right : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType (left ++ right))
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (normalizeForTypeIn schema variables
            boolCase returnType left
          ++ normalizeForTypeIn schema
            variables boolCase returnType right) := by
  intro hschema hleafFalse hmem
  have hwhole :=
    collectFields_normalizeForTypeIn_runtime_of_schemaWellFormed
      schema variableValues variables boolCase returnType runtimeType
      identity (left ++ right) hschema hleafFalse hmem
  have hleft :=
    collectFields_normalizeForTypeIn_runtime_of_schemaWellFormed
      schema variableValues variables boolCase returnType runtimeType
      identity left hschema hleafFalse hmem
  have hright :=
    collectFields_normalizeForTypeIn_runtime_of_schemaWellFormed
      schema variableValues variables boolCase returnType runtimeType
      identity right hschema hleafFalse hmem
  calc
    Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (normalizeForTypeIn schema variables
          boolCase returnType (left ++ right))
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase (left ++ right)) := hwhole
    _ =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
            runtimeType boolCase left
          ++ staticCollectForGround schema variables runtimeType
            runtimeType boolCase right) := by
        rw [staticCollectForGround_append]
    _ =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema variables runtimeType
            runtimeType boolCase left))
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema variables runtimeType
            runtimeType boolCase right)) := by
        rw [GroundTypeNormalization.collectFields_append]
    _ =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType left))
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType right)) := by
        rw [← hleft, ← hright]
    _ =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (normalizeForTypeIn schema variables
            boolCase returnType left
          ++ normalizeForTypeIn schema
            variables boolCase returnType right) := by
        rw [GroundTypeNormalization.collectFields_append]

theorem executeSelectionSet_normalizeForTypeIn_append_runtime_of_schemaWellFormed
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (depth : Nat)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (left right : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
      Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType (left ++ right))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (normalizeForTypeIn schema variables
            boolCase returnType left
          ++ normalizeForTypeIn schema
            variables boolCase returnType right) := by
  intro hschema hleafFalse hmem
  apply executeSelectionSet_eq_of_collectFields_eq
  exact
    collectFields_normalizeForTypeIn_append_runtime_of_schemaWellFormed
      schema variableValues variables boolCase returnType runtimeType
      identity left right hschema hleafFalse hmem

theorem collectFields_merge_staticCollectCompleteScopedSelectionSet_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (groundType runtimeType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase) :
    SchemaWellFormedness.schemaWellFormed schema ->
      ∀ scopedMatches,
        (∀ scopedSelection, scopedSelection ∈ scopedMatches ->
          completeScopedSelectionRuntimeReady schema boolCase runtimeType
            scopedSelection) ->
          Execution.collectFields schema variableValues runtimeType
              (.object runtimeType identity)
              (mergeSelectionSets
                (staticCollectCompleteScopedSelectionSet schema variables
                  groundType boolCase scopedMatches))
            =
          Execution.collectFields schema variableValues runtimeType
            (.object runtimeType identity)
            (staticCollectForGround schema variables runtimeType
              runtimeType boolCase
              (mergeSelectionSets
                (eraseCompleteScopedSelectionSet scopedMatches))) := by
  intro hschema scopedMatches
  induction scopedMatches with
  | nil =>
      intro _hready
      simp [staticCollectCompleteScopedSelectionSet,
        eraseCompleteScopedSelectionSet, mergeSelectionSets,
        staticCollectForGround]
  | cons scopedSelection rest ih =>
      intro hready
      have hrestReady :
          ∀ scopedSelection, scopedSelection ∈ rest ->
            completeScopedSelectionRuntimeReady schema boolCase runtimeType
              scopedSelection := by
        intro candidate hcandidate
        exact hready candidate (by simp [hcandidate])
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field responseName fieldName arguments directives selectionSet =>
              have hheadReady :
                  completeScopedSelectionRuntimeReady schema boolCase
                    runtimeType
                    (CompleteScopedSelection.mk lookupParent
                      (Selection.field responseName fieldName arguments
                        directives selectionSet)) :=
                hready
                  (CompleteScopedSelection.mk lookupParent
                    (Selection.field responseName fieldName arguments
                      directives selectionSet))
                  (by simp)
              simp [completeScopedSelectionRuntimeReady] at hheadReady
              rcases hheadReady with
                ⟨hallow, fieldDefinition, hlookup, hleafFalse, hmem⟩
              have hheadCollect :=
                collectFields_normalizeForTypeIn_runtime_of_schemaWellFormed
                  schema variableValues variables boolCase
                  fieldDefinition.outputType.namedType runtimeType identity
                  selectionSet hschema hleafFalse hmem
              have htailCollect := ih hrestReady
              calc
                Execution.collectFields schema variableValues runtimeType
                    (.object runtimeType identity)
                    (mergeSelectionSets
                      (staticCollectCompleteScopedSelectionSet schema variables
                        groundType boolCase
                        (CompleteScopedSelection.mk lookupParent
                          (Selection.field responseName fieldName arguments
                            directives selectionSet) :: rest)))
                    =
                  Execution.collectFields schema variableValues runtimeType
                    (.object runtimeType identity)
                    (normalizeForTypeIn schema
                        variables boolCase
                        fieldDefinition.outputType.namedType selectionSet
                      ++
                      mergeSelectionSets
                        (staticCollectCompleteScopedSelectionSet schema
                          variables groundType boolCase rest)) := by
                    simp [staticCollectCompleteScopedSelectionSet,
                      staticCollectCompleteScopedSelection,
                      staticCollectForGround, hallow, hlookup,
                      mergeSelectionSets, Selection.subselections]
                _ =
                  Execution.mergeExecutableGroups
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType identity)
                      (normalizeForTypeIn schema
                        variables boolCase
                        fieldDefinition.outputType.namedType selectionSet))
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType identity)
                      (mergeSelectionSets
                        (staticCollectCompleteScopedSelectionSet schema
                          variables groundType boolCase rest))) := by
                    rw [GroundTypeNormalization.collectFields_append]
                _ =
                  Execution.mergeExecutableGroups
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType identity)
                      (staticCollectForGround schema variables
                        runtimeType runtimeType boolCase selectionSet))
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType identity)
                      (staticCollectForGround schema variables
                        runtimeType runtimeType boolCase
                        (mergeSelectionSets
                          (eraseCompleteScopedSelectionSet rest)))) := by
                    rw [hheadCollect, htailCollect]
                _ =
                  Execution.collectFields schema variableValues runtimeType
                    (.object runtimeType identity)
                    (staticCollectForGround schema variables
                      runtimeType runtimeType boolCase
                      (selectionSet ++
                        mergeSelectionSets
                          (eraseCompleteScopedSelectionSet rest))) := by
                    rw [← GroundTypeNormalization.collectFields_append]
                    rw [staticCollectForGround_append]
                _ =
                  Execution.collectFields schema variableValues runtimeType
                    (.object runtimeType identity)
                    (staticCollectForGround schema variables
                      runtimeType runtimeType boolCase
                      (mergeSelectionSets
                        (eraseCompleteScopedSelectionSet
                          (CompleteScopedSelection.mk lookupParent
                            (Selection.field responseName fieldName arguments
                              directives selectionSet) :: rest)))) := by
                    simp [eraseCompleteScopedSelectionSet,
                      eraseCompleteScopedSelection, mergeSelectionSets,
                      Selection.subselections]
          | inlineFragment typeCondition directives selectionSet =>
              have hheadReady :
                  completeScopedSelectionRuntimeReady schema boolCase
                    runtimeType
                    (CompleteScopedSelection.mk lookupParent
                      (Selection.inlineFragment typeCondition directives
                        selectionSet)) :=
                hready
                  (CompleteScopedSelection.mk lookupParent
                    (Selection.inlineFragment typeCondition directives
                      selectionSet))
                  (by simp)
              simp [completeScopedSelectionRuntimeReady] at hheadReady

theorem executeSelectionSet_merge_staticCollectCompleteScopedSelectionSet_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (depth : Nat)
    (groundType runtimeType : Name) (identity : ObjectIdentity)
    (boolCase : BoolCase)
    (scopedMatches : List CompleteScopedSelection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    (∀ scopedSelection, scopedSelection ∈ scopedMatches ->
      completeScopedSelectionRuntimeReady schema boolCase runtimeType
        scopedSelection) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (.object runtimeType identity)
          (mergeSelectionSets
            (staticCollectCompleteScopedSelectionSet schema variables
              groundType boolCase scopedMatches))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase
          (mergeSelectionSets
            (eraseCompleteScopedSelectionSet scopedMatches))) := by
  intro hschema hready
  apply executeSelectionSet_eq_of_collectFields_eq
  exact
    collectFields_merge_staticCollectCompleteScopedSelectionSet_runtime
      schema variableValues variables groundType runtimeType identity
      boolCase hschema scopedMatches hready

theorem collectFields_normalizeForTypeIn_staticScoped_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (returnType groundType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (scopedMatches : List CompleteScopedSelection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    (∀ scopedSelection, scopedSelection ∈ scopedMatches ->
      completeScopedSelectionRuntimeReady schema boolCase runtimeType
        scopedSelection) ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
              boolCase returnType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema variables
                groundType boolCase scopedMatches))
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches))) := by
  intro hschema hleafFalse hmem hready
  have hhead :=
    collectFields_normalizeForTypeIn_runtime_of_schemaWellFormed
      schema variableValues variables boolCase returnType runtimeType
      identity selectionSet hschema hleafFalse hmem
  have htail :=
    collectFields_merge_staticCollectCompleteScopedSelectionSet_runtime
      schema variableValues variables groundType runtimeType identity
      boolCase hschema scopedMatches hready
  calc
    Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (normalizeForTypeIn schema variables
            boolCase returnType selectionSet
          ++ mergeSelectionSets
            (staticCollectCompleteScopedSelectionSet schema variables
              groundType boolCase scopedMatches))
        =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForTypeIn schema variables
            boolCase returnType selectionSet))
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (mergeSelectionSets
            (staticCollectCompleteScopedSelectionSet schema variables
              groundType boolCase scopedMatches))) := by
        rw [GroundTypeNormalization.collectFields_append]
    _ =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema variables runtimeType
            runtimeType boolCase selectionSet))
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema variables runtimeType
            runtimeType boolCase
            (mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches)))) := by
        rw [hhead, htail]
    _ =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
            runtimeType boolCase selectionSet
          ++ staticCollectForGround schema variables runtimeType
            runtimeType boolCase
            (mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches))) := by
        rw [GroundTypeNormalization.collectFields_append]
    _ =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches))) := by
        rw [staticCollectForGround_append]

theorem executeSelectionSet_normalizeForTypeIn_staticScoped_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (depth : Nat)
    (returnType groundType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (scopedMatches : List CompleteScopedSelection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    (∀ scopedSelection, scopedSelection ∈ scopedMatches ->
      completeScopedSelectionRuntimeReady schema boolCase runtimeType
        scopedSelection) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (.object runtimeType identity)
          (normalizeForTypeIn schema variables
              boolCase returnType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema variables
                groundType boolCase scopedMatches))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches))) := by
  intro hschema hleafFalse hmem hready
  apply executeSelectionSet_eq_of_collectFields_eq
  exact
    collectFields_normalizeForTypeIn_staticScoped_runtime
      schema variableValues variables boolCase returnType groundType
      runtimeType identity selectionSet scopedMatches hschema hleafFalse hmem
      hready

theorem completeValue_normalizeForTypeIn_staticScoped_eq_of_staticCollect_child
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (boolCase : BoolCase)
    (depth : Nat) (returnType groundType : Name)
    (selectionSet : List Selection)
    (scopedMatches : List CompleteScopedSelection)
    (value : Execution.Value ObjectIdentity) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    (∀ childDepth runtimeType (_identity : ObjectIdentity),
      childDepth < depth ->
      runtimeType ∈ groundObjectTypesForType schema returnType ->
        ∀ scopedSelection, scopedSelection ∈ scopedMatches ->
          completeScopedSelectionRuntimeReady schema boolCase runtimeType
            scopedSelection) ->
    (∀ childDepth runtimeType (identity : ObjectIdentity),
      childDepth < depth ->
      runtimeType ∈ groundObjectTypesForType schema returnType ->
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
      Execution.completeValue schema resolvers variableValues depth returnType
          (normalizeForTypeIn schema variables
              boolCase returnType selectionSet
            ++ mergeSelectionSets
              (staticCollectCompleteScopedSelectionSet schema variables
                groundType boolCase scopedMatches))
          value
        =
      Execution.completeValue schema resolvers variableValues depth returnType
        (selectionSet
          ++ mergeSelectionSets
            (eraseCompleteScopedSelectionSet scopedMatches))
        value := by
  intro hschema hleafFalse hscopedReady hchild
  apply GroundTypeNormalization.completeValue_eq_of_child_object_lt_includes
    schema resolvers variableValues
  intro childDepth runtimeType identity hlt hinclude
  have hmem :
      runtimeType ∈ groundObjectTypesForType schema returnType :=
    typeIncludesObjectBool_mem_groundObjectTypesForType schema returnType
      runtimeType hleafFalse hinclude
  calc
    Execution.executeSelectionSet schema resolvers variableValues childDepth
        runtimeType (.object runtimeType identity)
        (normalizeForTypeIn schema variables
            boolCase returnType selectionSet
          ++ mergeSelectionSets
            (staticCollectCompleteScopedSelectionSet schema variables
              groundType boolCase scopedMatches))
      =
    Execution.executeSelectionSet schema resolvers variableValues childDepth
        runtimeType (.object runtimeType identity)
        (staticCollectForGround schema variables runtimeType
          runtimeType boolCase
          (selectionSet
            ++ mergeSelectionSets
              (eraseCompleteScopedSelectionSet scopedMatches))) := by
        exact
          executeSelectionSet_normalizeForTypeIn_staticScoped_runtime
            schema resolvers variableValues variables boolCase childDepth
            returnType groundType runtimeType identity selectionSet
            scopedMatches hschema hleafFalse hmem
            (hscopedReady childDepth runtimeType identity hlt hmem)
    _ =
    Execution.executeSelectionSet schema resolvers variableValues childDepth
        runtimeType (.object runtimeType identity)
        (selectionSet
          ++ mergeSelectionSets
            (eraseCompleteScopedSelectionSet scopedMatches)) :=
        hchild childDepth runtimeType identity hlt hmem


end CompleteNormalization

end NormalForm

end GraphQL
