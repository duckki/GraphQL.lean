import GraphQL.NormalForm.CompleteNormalization.ChildCompletion

/-!
Root selection-set semantics and public correctness theorems for complete normalization.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem collectFields_normalizeForType_object_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
    (returnType : Name) (source : Execution.Value ObjectIdentity)
    (runtimeCase : BoolCase)
    (selectionSet : List Selection) :
    objectTypeNameBool schema returnType = true ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.collectFields schema variableValues returnType source
          (normalizeForType schema
            (operationBoolVars operation) returnType
            selectionSet)
        =
      Execution.collectFields schema variableValues returnType source
        (staticCollectForGround schema
          (operationBoolVars operation) returnType returnType
          runtimeCase selectionSet) := by
  intro hobject hruntime hagrees
  have hleafFalse :
      leafTypeNameBool schema returnType = false :=
    leafTypeNameBool_false_of_objectTypeNameBool_true schema hobject
  unfold normalizeForType
  simp [hleafFalse]
  exact
    (collectFields_flatten_boolCaseWrappers_runtime schema variableValues
      operation returnType source runtimeCase
      (fun boolCase =>
        normalizeForTypeIn schema
          (operationBoolVars operation) boolCase returnType
          selectionSet) hruntime hagrees).trans
      (collectFields_normalizeForTypeIn_object_runtime
        schema variableValues (operationBoolVars operation)
        runtimeCase returnType source selectionSet hobject)

theorem collectFields_possibleTypeCaseBranches_not_mem_eq_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
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
              (boolCaseBranchesForGround schema objectType
                (operationBoolVars operation)
                selectionSet)))
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

theorem collectFields_possibleTypeCaseBranches_runtime_branch
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
    (runtimeType : Name) (identity : ObjectIdentity)
    (runtimeCase : BoolCase)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (boolCaseBranchesForGround schema objectType
                (operationBoolVars operation)
                selectionSet)))
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) runtimeType
          runtimeType runtimeCase selectionSet) := by
  intro hobjects hnodup hmem hruntime hagrees
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
          (boolCaseBranchesForGround schema objectType
            (operationBoolVars operation) selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (boolCaseBranchesForGround schema objectType
                  (operationBoolVars operation)
                  selectionSet)))
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
          (boolCaseBranchesForGround schema runtimeType
            (operationBoolVars operation) selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (boolCaseBranchesForGround schema objectType
                  (operationBoolVars operation)
                  selectionSet)))
          happly]
        rw [collectFields_append_right_nil schema variableValues runtimeType
          (.object runtimeType identity)
          (boolCaseBranchesForGround schema runtimeType
            (operationBoolVars operation) selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (boolCaseBranchesForGround schema objectType
                  (operationBoolVars operation)
                  selectionSet)))]
        · exact collectFields_boolCaseBranchesForGround_runtime schema
            variableValues operation runtimeType (.object runtimeType identity)
            runtimeCase selectionSet hruntime hagrees
        · exact collectFields_possibleTypeCaseBranches_not_mem_eq_nil
            schema variableValues operation runtimeType identity rest
            selectionSet hrestObjects hrestNotin

theorem collectFields_normalizeForType_abstract_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (runtimeCase : BoolCase)
    (selectionSet : List Selection) :
    leafTypeNameBool schema returnType = false ->
    objectTypeNameBool schema returnType = false ->
    (∀ objectType, objectType ∈ groundObjectTypesForType schema returnType ->
      objectTypeNameBool schema objectType = true) ->
    (groundObjectTypesForType schema returnType).Nodup ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType
            selectionSet)
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) runtimeType
          runtimeType runtimeCase selectionSet) := by
  intro hleafFalse hobjectFalse hobjects hnodup hmem hruntime hagrees
  unfold normalizeForType
  simp [hleafFalse]
  exact
    (collectFields_flatten_boolCaseWrappers_runtime schema variableValues
      operation runtimeType (.object runtimeType identity) runtimeCase
      (fun boolCase =>
        normalizeForTypeIn schema
          (operationBoolVars operation) boolCase returnType
          selectionSet) hruntime hagrees).trans
      (collectFields_normalizeForTypeIn_abstract_runtime
        schema variableValues (operationBoolVars operation)
        runtimeCase returnType runtimeType identity selectionSet
        hleafFalse hobjectFalse hobjects hnodup hmem)

theorem collectFields_normalizeForType_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (runtimeCase : BoolCase)
    (selectionSet : List Selection) :
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    (∀ objectType, objectType ∈ groundObjectTypesForType schema returnType ->
      objectTypeNameBool schema objectType = true) ->
    (groundObjectTypesForType schema returnType).Nodup ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType
            selectionSet)
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) runtimeType
          runtimeType runtimeCase selectionSet) := by
  intro hleafFalse hmem hobjects hnodup hruntime hagrees
  cases hobject : objectTypeNameBool schema returnType with
  | false =>
      exact collectFields_normalizeForType_abstract_runtime
        schema variableValues operation returnType runtimeType identity
        runtimeCase selectionSet hleafFalse hobject hobjects hnodup hmem
        hruntime hagrees
  | true =>
      have hruntimeEq : runtimeType = returnType := by
        unfold groundObjectTypesForType at hmem
        simp [hobject] at hmem
        exact hmem
      subst runtimeType
      exact collectFields_normalizeForType_object_runtime
        schema variableValues operation returnType (.object returnType identity)
        runtimeCase selectionSet hobject hruntime hagrees

theorem collectFields_normalizeForType_runtime_of_schemaWellFormed
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (runtimeCase : BoolCase)
    (selectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType
            selectionSet)
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) runtimeType
          runtimeType runtimeCase selectionSet) := by
  intro hschema hleafFalse hmem hruntime hagrees
  exact collectFields_normalizeForType_runtime schema
    variableValues operation returnType runtimeType identity runtimeCase
    selectionSet hleafFalse hmem
    (groundObjectTypesForType_objects schema hschema returnType)
    (groundObjectTypesForType_nodup schema hschema returnType)
    hruntime hagrees

theorem executeSelectionSet_normalizeForType_runtime_of_schemaWellFormed
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (runtimeCase : BoolCase)
    (selectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType
            selectionSet)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) runtimeType
          runtimeType runtimeCase selectionSet) := by
  intro hschema hleafFalse hmem hruntime hagrees
  apply executeSelectionSet_eq_of_collectFields_eq
  exact
    collectFields_normalizeForType_runtime_of_schemaWellFormed
      schema variableValues operation returnType runtimeType identity
      runtimeCase selectionSet hschema hleafFalse hmem hruntime hagrees

theorem collectFields_normalizeForType_append_runtime_of_schemaWellFormed
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (runtimeCase : BoolCase)
    (left right : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType
            (left ++ right))
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (normalizeForType schema
            (operationBoolVars operation) returnType left
          ++ normalizeForType schema
            (operationBoolVars operation) returnType right) := by
  intro hschema hleafFalse hmem hruntime hagrees
  have hwhole :=
    collectFields_normalizeForType_runtime_of_schemaWellFormed
      schema variableValues operation returnType runtimeType identity
      runtimeCase (left ++ right) hschema hleafFalse hmem hruntime
      hagrees
  have hleft :=
    collectFields_normalizeForType_runtime_of_schemaWellFormed
      schema variableValues operation returnType runtimeType identity
      runtimeCase left hschema hleafFalse hmem hruntime hagrees
  have hright :=
    collectFields_normalizeForType_runtime_of_schemaWellFormed
      schema variableValues operation returnType runtimeType identity
      runtimeCase right hschema hleafFalse hmem hruntime hagrees
  calc
    Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (normalizeForType schema
          (operationBoolVars operation) returnType
          (left ++ right))
        =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema
          (operationBoolVars operation) runtimeType
          runtimeType runtimeCase (left ++ right)) := hwhole
    _ =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType runtimeCase left
          ++ staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType runtimeCase right) := by
        rw [staticCollectForGround_append]
    _ =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType runtimeCase left))
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (staticCollectForGround schema
            (operationBoolVars operation) runtimeType
            runtimeType runtimeCase right)) := by
        rw [GroundTypeNormalization.collectFields_append]
    _ =
      Execution.mergeExecutableGroups
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType left))
        (Execution.collectFields schema variableValues runtimeType
          (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType right)) := by
        rw [← hleft, ← hright]
    _ =
      Execution.collectFields schema variableValues runtimeType
        (.object runtimeType identity)
        (normalizeForType schema
            (operationBoolVars operation) returnType left
          ++ normalizeForType schema
            (operationBoolVars operation) returnType right) := by
        rw [GroundTypeNormalization.collectFields_append]

theorem executeSelectionSet_normalizeForType_append_runtime_of_schemaWellFormed
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (returnType runtimeType : Name) (identity : ObjectIdentity)
    (runtimeCase : BoolCase)
    (left right : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    leafTypeNameBool schema returnType = false ->
    runtimeType ∈ groundObjectTypesForType schema returnType ->
    runtimeCase ∈
      allBoolCases (operationBoolVars operation) ->
    variableValuesAgreeWithCase variableValues runtimeCase
      (operationBoolVars operation) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (.object runtimeType identity)
          (normalizeForType schema
            (operationBoolVars operation) returnType
            (left ++ right))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (normalizeForType schema
            (operationBoolVars operation) returnType left
          ++ normalizeForType schema
            (operationBoolVars operation) returnType right) := by
  intro hschema hleafFalse hmem hruntime hagrees
  apply executeSelectionSet_eq_of_collectFields_eq
  exact
    collectFields_normalizeForType_append_runtime_of_schemaWellFormed
      schema variableValues operation returnType runtimeType identity
      runtimeCase left right hschema hleafFalse hmem hruntime hagrees

theorem executeSelectionSet_completeNormalizeOperation_root_static
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      ∀ (ObjectIdentity : Type)
        (resolvers : Execution.Resolvers ObjectIdentity)
        (variableValues : Execution.VariableValues)
        (depth : Nat) (source : Execution.Value ObjectIdentity),
        operationBoolVarsComplete operation variableValues ->
        Execution.rootSourceAppliesBool schema operation source = true ->
          ∃ runtimeCase,
            runtimeCase ∈
              allBoolCases (operationBoolVars operation)
              ∧ variableValuesAgreeWithCase variableValues
                  runtimeCase
                  (operationBoolVars operation)
              ∧ Execution.executeSelectionSet schema resolvers variableValues
                    depth operation.rootType source
                    (completeNormalizeOperation schema operation).selectionSet
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  depth operation.rootType source
                  (staticCollectForGround schema
                    (operationBoolVars operation)
                    operation.rootType operation.rootType runtimeCase
                    operation.selectionSet) := by
  intro hschema hvalid ObjectIdentity resolvers variableValues depth source
    hcomplete hroot
  rcases
      operationBoolVarsComplete_caseForVariableValues
        variableValues operation hcomplete with
    ⟨runtimeCase, hruntimeCase, hagrees⟩
  rcases
      GroundTypeNormalization.rootSourceAppliesBool_true_object schema
        operation source hroot with
    ⟨runtimeType, identity, hsource, hinclude⟩
  have hrootObject : schema.objectType operation.rootType := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema operation.rootType = true :=
    GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType schema
      hrootObject
  have hleafFalse :
      leafTypeNameBool schema operation.rootType = false :=
    leafTypeNameBool_false_of_objectTypeNameBool_true schema hobject
  have hruntimeEq : runtimeType = operation.rootType :=
    GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
      schema hobject hinclude
  subst source
  subst runtimeType
  have hmem :
      operation.rootType ∈
        groundObjectTypesForType schema operation.rootType :=
    typeIncludesObjectBool_mem_groundObjectTypesForType schema
      operation.rootType operation.rootType hleafFalse
      (GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
        schema hobject)
  refine ⟨runtimeCase, hruntimeCase, hagrees, ?_⟩
  simpa [completeNormalizeOperation]
    using
      executeSelectionSet_normalizeForType_runtime_of_schemaWellFormed
        schema resolvers variableValues operation depth operation.rootType
        operation.rootType identity runtimeCase operation.selectionSet
        hschema hleafFalse hmem hruntimeCase hagrees

theorem completeNormalizationSemanticsPreserved_of_staticCollection
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    (∀ (ObjectIdentity : Type)
      (resolvers : Execution.Resolvers ObjectIdentity)
      variableValues depth (source : Execution.Value ObjectIdentity)
      runtimeCase,
      operationBoolVarsComplete operation variableValues ->
      Execution.rootSourceAppliesBool schema operation source = true ->
      runtimeCase ∈
        allBoolCases (operationBoolVars operation) ->
      variableValuesAgreeWithCase variableValues runtimeCase
        (operationBoolVars operation) ->
        Execution.executeSelectionSet schema resolvers variableValues depth
            operation.rootType source
            (staticCollectForGround schema
              (operationBoolVars operation)
              operation.rootType operation.rootType runtimeCase
              operation.selectionSet)
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet) ->
      completeNormalizationSemanticsPreserved schema operation := by
  intro hschema hvalid hstatic
  apply completeNormalizationSemanticsPreserved_of_selectionSet schema operation
  intro ObjectIdentity resolvers variableValues depth source hcomplete hroot
  rcases
      executeSelectionSet_completeNormalizeOperation_root_static schema
        operation hschema hvalid ObjectIdentity resolvers variableValues depth
        source hcomplete hroot with
    ⟨runtimeCase, hruntimeCase, hagrees, hnormalizedStatic⟩
  have hstaticSource :
      Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (staticCollectForGround schema
            (operationBoolVars operation)
            operation.rootType operation.rootType runtimeCase
            operation.selectionSet)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet :=
    hstatic ObjectIdentity resolvers variableValues depth source
      runtimeCase hcomplete hroot hruntimeCase hagrees
  exact (hnormalizedStatic.trans hstaticSource).symm

theorem completeNormalizationSemanticsPreserved_of_resolverFieldValuesInclude
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    (∀ (ObjectIdentity : Type)
      (resolvers : Execution.Resolvers ObjectIdentity),
      completeScopedResolverFieldValuesInclude schema resolvers) ->
      completeNormalizationSemanticsPreserved schema operation := by
  intro hschema hvalid hresolverIncludes
  apply completeNormalizationSemanticsPreserved_of_staticCollection schema
    operation hschema hvalid
  intro ObjectIdentity resolvers variableValues depth source runtimeCase
    _hcomplete hroot _hruntimeCase hagrees
  rcases
      GroundTypeNormalization.rootSourceAppliesBool_true_object schema
        operation source hroot with
    ⟨runtimeType, identity, hsource, hinclude⟩
  have hrootObject : schema.objectType operation.rootType := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema operation.rootType = true :=
    GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType schema
      hrootObject
  have hruntimeEq : runtimeType = operation.rootType :=
    GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
      schema hobject hinclude
  subst runtimeType
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema
        operation.rootType operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object
      schema operation.variableDefinitions operation.rootType hschema
      hrootObject operation.selectionSet hselectionValid
  have hlookup :
      selectionSetLookupValid schema
        operation.rootType operation.selectionSet :=
    selectionSetLookupValid_of_selectionSetSemanticsReady
      operation.selectionSet hready
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hground :
      completeScopedSelectionSetGroundApplies schema operation.rootType
        (completeScopedSelectionSet operation.rootType operation.selectionSet) := by
    intro scopedSelection hmem
    have hparent := completeScopedSelectionSet_lookupParent_eq hmem
    rw [hparent]
    exact
      GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
        schema hobject
  rw [hsource]
  simpa [
    staticCollectCompleteScopedSelectionSet_completeScopedSelectionSet,
    eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_value_includes
      schema resolvers variableValues operation hschema
      (hresolverIncludes ObjectIdentity resolvers) depth operation.rootType
      operation.rootType identity runtimeCase
      (completeScopedSelectionSet operation.rootType operation.selectionSet)
      hrootObject
      (GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
        schema hobject)
      ((completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
        schema operation.rootType operation.rootType
        operation.selectionSet).mpr hready)
      ((completeScopedSelectionSetLookupValid_completeScopedSelectionSet schema
        operation.rootType operation.selectionSet).mpr hlookup)
      ((completeScopedSelectionSetCanMerge_completeScopedSelectionSet schema
        operation.rootType operation.rootType operation.selectionSet).mpr
        hmerge)
      hground hagrees
      (by
        intro varName hmem
        simpa [eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
          using hmem)

theorem completeNormalizationCorrect_of_staticCollection
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    (∀ (ObjectIdentity : Type)
      (resolvers : Execution.Resolvers ObjectIdentity)
      variableValues depth (source : Execution.Value ObjectIdentity)
      runtimeCase,
      operationBoolVarsComplete operation variableValues ->
      Execution.rootSourceAppliesBool schema operation source = true ->
      runtimeCase ∈
        allBoolCases (operationBoolVars operation) ->
      variableValuesAgreeWithCase variableValues runtimeCase
        (operationBoolVars operation) ->
        Execution.executeSelectionSet schema resolvers variableValues depth
            operation.rootType source
            (staticCollectForGround schema
              (operationBoolVars operation)
              operation.rootType operation.rootType runtimeCase
              operation.selectionSet)
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet) ->
      completeNormalizationCorrect schema operation := by
  intro hschema hvalid hstatic
  exact completeNormalizationCorrect_of_semanticsPreserved schema operation
    (completeNormalizationSemanticsPreserved_of_staticCollection schema
      operation hschema hvalid hstatic)

theorem completeNormalizationCorrect_of_staticCollectionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    (∀ (store : DataModel.Store) variableValues depth runtimeCase,
      store.wellTyped schema ->
      operationBoolVarsComplete operation variableValues ->
      Execution.rootSourceAppliesBool schema operation store.rootExecutionValue =
        true ->
      runtimeCase ∈
        allBoolCases (operationBoolVars operation) ->
      variableValuesAgreeWithCase variableValues runtimeCase
        (operationBoolVars operation) ->
        Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues depth operation.rootType store.rootExecutionValue
            (staticCollectForGround schema
              (operationBoolVars operation)
              operation.rootType operation.rootType runtimeCase
              operation.selectionSet)
          =
        Execution.executeSelectionSet schema (store.resolvers schema)
          variableValues depth operation.rootType store.rootExecutionValue
          operation.selectionSet) ->
      completeNormalizationCorrect schema operation := by
  intro hschema hvalid hstatic store variableValues depth hstore hcomplete
  unfold DataModel.executeOperationAtDepth
  rw [Execution.executeQueryAtDepth]
  cases hroot : Execution.rootSourceAppliesBool schema operation
      store.rootExecutionValue with
  | false =>
      have hnormalizedRoot :
          Execution.rootSourceAppliesBool schema
              (completeNormalizeOperation schema operation)
              store.rootExecutionValue = false := by
        simpa [completeNormalizeOperation_rootSourceAppliesBool] using hroot
      rw [Execution.executeQueryAtDepth]
      simp [hnormalizedRoot]
  | true =>
      rw [Execution.executeQueryAtDepth]
      have hnormalizedRoot :
          Execution.rootSourceAppliesBool schema
              (completeNormalizeOperation schema operation)
              store.rootExecutionValue = true := by
        simpa [completeNormalizeOperation_rootSourceAppliesBool] using hroot
      rcases
        executeSelectionSet_completeNormalizeOperation_root_static schema
          operation hschema hvalid DataModel.ObjectPath (store.resolvers schema)
          variableValues depth store.rootExecutionValue hcomplete hroot with
        ⟨runtimeCase, hruntimeCase, hagrees,
          hnormalizedStatic⟩
      have hstaticSource :
          Execution.executeSelectionSet schema (store.resolvers schema)
              variableValues depth operation.rootType store.rootExecutionValue
              (staticCollectForGround schema
                (operationBoolVars operation)
                operation.rootType operation.rootType runtimeCase
                operation.selectionSet)
            =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues depth operation.rootType store.rootExecutionValue
            operation.selectionSet :=
        hstatic store variableValues depth runtimeCase hstore hcomplete
          hroot hruntimeCase hagrees
      simp [hnormalizedRoot]
      exact (hnormalizedStatic.trans hstaticSource).symm

theorem completeNormalizationCorrect_of_scopedStaticCollectionOnData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    (∀ (store : DataModel.Store) variableValues depth
      execParent groundType identity boolCase scopedSelections,
      store.wellTyped schema ->
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
          (eraseCompleteScopedSelectionSet scopedSelections)) ->
      completeNormalizationCorrect schema operation := by
  intro hschema hvalid hscoped
  apply completeNormalizationCorrect_of_staticCollectionOnData schema operation
    hschema hvalid
  intro store variableValues depth runtimeCase hstore hcomplete hroot
    hruntimeCase hagrees
  rcases
      GroundTypeNormalization.rootSourceAppliesBool_true_object schema
        operation store.rootExecutionValue hroot with
    ⟨runtimeType, identity, hsource, hinclude⟩
  have hrootObject : schema.objectType operation.rootType := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema operation.rootType = true :=
    GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType schema
      hrootObject
  have hruntimeEq : runtimeType = operation.rootType :=
    GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
      schema hobject hinclude
  subst runtimeType
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions operation.rootType hschema hrootObject
      operation.selectionSet hselectionValid
  have hlookup :
      selectionSetLookupValid schema
        operation.rootType operation.selectionSet :=
    selectionSetLookupValid_of_selectionSetSemanticsReady
      operation.selectionSet hready
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hground :
      completeScopedSelectionSetGroundApplies schema operation.rootType
        (completeScopedSelectionSet operation.rootType
          operation.selectionSet) := by
    intro scopedSelection hmem
    have hparent :=
      completeScopedSelectionSet_lookupParent_eq hmem
    rw [hparent]
    exact
      GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
        schema hobject
  rw [hsource]
  simpa [
    staticCollectCompleteScopedSelectionSet_completeScopedSelectionSet,
    eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
    hscoped store variableValues depth operation.rootType operation.rootType
      identity runtimeCase
      (completeScopedSelectionSet operation.rootType operation.selectionSet)
      hstore hrootObject
      (GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
        schema hobject)
      ((completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
        schema operation.rootType operation.rootType
        operation.selectionSet).mpr hready)
      ((completeScopedSelectionSetLookupValid_completeScopedSelectionSet schema
        operation.rootType operation.selectionSet).mpr hlookup)
      ((completeScopedSelectionSetCanMerge_completeScopedSelectionSet schema
        operation.rootType operation.rootType operation.selectionSet).mpr hmerge)
      hground hagrees
      (by
        intro varName hmem
        simpa [eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
          using hmem)

theorem completeNormalizationCorrect_onData
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
      completeNormalizationCorrect schema operation := by
  intro hschema hvalid
  apply completeNormalizationCorrect_of_scopedStaticCollectionOnData schema
    operation hschema hvalid
  intro store variableValues depth execParent groundType identity boolCase
    scopedSelections hstore hobject hground hready hlookup hmerge happlies
    hagrees hsourceVars
  exact
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_on_store
      schema store variableValues operation hschema hstore depth execParent
      groundType identity boolCase scopedSelections hobject hground hready
      hlookup hmerge happlies hagrees hsourceVars


end CompleteNormalization

end NormalForm

end GraphQL
