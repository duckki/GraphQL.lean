import GraphQL.NormalForm.GroundTypeLifting.FieldOutput

/-!
Field-head semantic preservation lemmas for ground-type lifting.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeLifting

variable {ObjectRef : Type}

open GroundTypeNormalization
open DataModel.Store

theorem executeSelectionSet_append_groundLift_possibleTypeFragments_not_mem
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : Option ObjectRef := none)
    (possibleTypes : List Name)
    (selectionSet suffix : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      objectTypeNameBool schema objectType = true) ->
    runtimeType ∉ possibleTypes ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType ref)
      (suffix ++
        possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType selectionSet)))
    =
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType ref) suffix := by
  intro hobjects hnotin
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
  rw [collectFields_append]
  have hnil :
      Execution.collectFields schema variableValues runtimeType
        (Execution.ResolverValue.object runtimeType ref)
        (possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType selectionSet))) = [] := by
    simpa [] using
      collectFields_groundLift_possibleTypeFragments_not_mem_eq_nil schema
        variableValues runtimeType (ref := ref) possibleTypes selectionSet hobjects
        hnotin
  rw [hnil]
  simp [Execution.mergeExecutableGroups_nil_right]

theorem executeSelectionSet_groundLift_possibleTypeFragments_runtime_branch
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : Option ObjectRef := none)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType ref)
      (groundLiftSelectionSet schema runtimeType selectionSet)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType ref) selectionSet ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType ref)
      (possibleTypes.map
        (fun objectType =>
          Selection.inlineFragment (some objectType) []
            (groundLiftSelectionSet schema objectType selectionSet)))
    =
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType ref) selectionSet := by
  intro hobjects hnodup hmem hrecursive
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
              (.object runtimeType ref) objectType = false :=
          doesFragmentTypeApplyBool_object_other_false schema
            (ref := ref) hobject hne
        rw [executeSelectionSet_inlineFragment_some_directiveFree_skip
          schema resolvers variableValues depth runtimeType objectType
          (.object runtimeType ref)
          (groundLiftSelectionSet schema objectType selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
          (by simpa [] using hskip)]
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
              (.object runtimeType ref) runtimeType = true :=
          doesFragmentTypeApplyBool_object_self schema (ref := ref) hobject
        rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
          schema resolvers variableValues depth runtimeType runtimeType
          (.object runtimeType ref)
          (groundLiftSelectionSet schema runtimeType selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
          (by simpa [] using happly)]
        rw [executeSelectionSet_append_groundLift_possibleTypeFragments_not_mem
          schema resolvers variableValues depth runtimeType (ref := ref) rest
          selectionSet (groundLiftSelectionSet schema runtimeType selectionSet)
          hrestObjects hrestNotin]
        exact hrecursive

theorem completeValue_groundLift_possibleTypeFragments_eq_of_child_object_lt
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth childType selectionSet value,
      (∀ childDepth runtimeType ref,
        childDepth < depth ->
          runtimeType ∈ schema.getPossibleTypes childType ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              (groundLiftSelectionSet schema runtimeType selectionSet)
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              selectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          childType
          ((schema.getPossibleTypes childType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
          value
          =
        Execution.completeValue schema resolvers variableValues depth
          childType selectionSet value
  | 0, _childType, _selectionSet, _value, _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, childType, selectionSet, value, hrecursive => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType ref =>
          by_cases hinclude :
              schema.typeIncludesObjectBool childType runtimeType = true
          · have hmem :
                runtimeType ∈ schema.getPossibleTypes childType := by
              exact List.contains_iff_mem.mp hinclude
            have hobjects :
                ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
                  objectTypeNameBool schema objectType = true := by
              intro objectType hobjectType
              exact objectTypeNameBool_eq_true_of_objectType schema
                (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  hschema childType objectType hobjectType)
            have hbranch :=
              executeSelectionSet_groundLift_possibleTypeFragments_runtime_branch
                schema resolvers variableValues depth runtimeType (ref := ref)
                (schema.getPossibleTypes childType) selectionSet hobjects
                (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
                  hschema childType)
                hmem
                (hrecursive depth runtimeType ref
                  (Nat.lt_succ_self depth) hmem)
            simp [Execution.completeValue, hinclude]
            exact congrArg
              (Execution.catchBubbleAsNull Execution.ResponseValue.object)
              (by
                simpa [Execution.executeSelectionSet,
                  Execution.executeRootSelectionSet,
                  collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using hbranch)
          · have hfalse :
                schema.typeIncludesObjectBool childType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool childType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
        | list values =>
            simp [Execution.completeValue]

theorem completeValue_groundLiftSelectionSet_eq_of_object_child_lt
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) :
    ∀ depth childType selectionSet value,
      objectTypeNameBool schema childType = true ->
      (∀ childDepth runtimeType ref,
        childDepth < depth ->
          schema.typeIncludesObjectBool childType runtimeType = true ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              (groundLiftSelectionSet schema runtimeType selectionSet)
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              selectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          childType (groundLiftSelectionSet schema childType selectionSet)
          value
          =
        Execution.completeValue schema resolvers variableValues depth
          childType selectionSet value
  | 0, _childType, _selectionSet, _value, _hobject, _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, childType, selectionSet, value, hobject, hrecursive => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType ref =>
          by_cases hinclude :
              schema.typeIncludesObjectBool childType runtimeType = true
          · have hrecursiveBranch :=
              hrecursive depth runtimeType ref (Nat.lt_succ_self depth)
                hinclude
            have hruntime : runtimeType = childType :=
              typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
                hobject hinclude
            subst runtimeType
            simp [Execution.completeValue, hinclude]
            exact congrArg
              (Execution.catchBubbleAsNull Execution.ResponseValue.object)
              (by
                simpa [Execution.executeSelectionSet,
                  Execution.executeRootSelectionSet,
                  collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using hrecursiveBranch)
          · have hfalse :
                schema.typeIncludesObjectBool childType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool childType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
        | list values =>
            simp [Execution.completeValue]

theorem completeValue_groundLift_possibleTypeFragments_eq_of_subtype_lt
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth actualType branchType selectionSet value,
      (∀ runtimeType,
        schema.typeIncludesObjectBool actualType runtimeType = true ->
          runtimeType ∈ schema.getPossibleTypes branchType) ->
      (∀ childDepth runtimeType ref,
        childDepth < depth ->
          runtimeType ∈ schema.getPossibleTypes branchType ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              (groundLiftSelectionSet schema runtimeType selectionSet)
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              selectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          actualType
          ((schema.getPossibleTypes branchType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet)))
          value
          =
        Execution.completeValue schema resolvers variableValues depth
          actualType selectionSet value
  | 0, _actualType, _branchType, _selectionSet, _value, _hsubtype,
    _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, actualType, branchType, selectionSet, value, hsubtype,
    hrecursive => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType ref =>
          by_cases hinclude :
              schema.typeIncludesObjectBool actualType runtimeType = true
          · have hmem :
                runtimeType ∈ schema.getPossibleTypes branchType :=
              hsubtype runtimeType hinclude
            have hobjects :
                ∀ objectType, objectType ∈ schema.getPossibleTypes branchType ->
                  objectTypeNameBool schema objectType = true := by
              intro objectType hobjectType
              exact objectTypeNameBool_eq_true_of_objectType schema
                (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  hschema branchType objectType hobjectType)
            have hbranch :=
              executeSelectionSet_groundLift_possibleTypeFragments_runtime_branch
                schema resolvers variableValues depth runtimeType (ref := ref)
                (schema.getPossibleTypes branchType) selectionSet hobjects
                (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
                  hschema branchType)
                hmem
                (hrecursive depth runtimeType ref
                  (Nat.lt_succ_self depth) hmem)
            simp [Execution.completeValue, hinclude]
            exact congrArg
              (Execution.catchBubbleAsNull Execution.ResponseValue.object)
              (by
                simpa [Execution.executeSelectionSet,
                  Execution.executeRootSelectionSet,
                  collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using hbranch)
          · have hfalse :
                schema.typeIncludesObjectBool actualType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool actualType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
        | list values =>
            simp [Execution.completeValue]

theorem completeValue_groundLiftSelectionSet_eq_of_object_subtype_lt
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) :
    ∀ depth actualType liftType selectionSet value,
      objectTypeNameBool schema liftType = true ->
      (∀ runtimeType,
        schema.typeIncludesObjectBool actualType runtimeType = true ->
          schema.typeIncludesObjectBool liftType runtimeType = true) ->
      (∀ childDepth runtimeType ref,
        childDepth < depth ->
          schema.typeIncludesObjectBool liftType runtimeType = true ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              (groundLiftSelectionSet schema runtimeType selectionSet)
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              selectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          actualType (groundLiftSelectionSet schema liftType selectionSet)
          value
          =
        Execution.completeValue schema resolvers variableValues depth
          actualType selectionSet value
  | 0, _actualType, _liftType, _selectionSet, _value, _hliftObject,
    _hsubtype, _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, actualType, liftType, selectionSet, value, hliftObject,
    hsubtype, hrecursive => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType ref =>
          by_cases hinclude :
              schema.typeIncludesObjectBool actualType runtimeType = true
          · have hliftInclude :
                schema.typeIncludesObjectBool liftType runtimeType = true :=
              hsubtype runtimeType hinclude
            have hruntime : runtimeType = liftType :=
              typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
                hliftObject hliftInclude
            subst runtimeType
            simp [Execution.completeValue, hinclude]
            exact congrArg
              (Execution.catchBubbleAsNull Execution.ResponseValue.object)
              (by
                simpa [Execution.executeSelectionSet,
                  Execution.executeRootSelectionSet,
                  collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using hrecursive depth liftType ref
                    (Nat.lt_succ_self depth) hliftInclude)
          · have hfalse :
                schema.typeIncludesObjectBool actualType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool actualType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
        | list values =>
            simp [Execution.completeValue]

theorem completeValue_groundLiftFieldSelectionSet_eq_of_subtype_lt
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth actualType expectedType selectionSet value,
      (∀ runtimeType,
        schema.typeIncludesObjectBool actualType runtimeType = true ->
          schema.typeIncludesObjectBool expectedType runtimeType = true) ->
      (∀ childDepth runtimeType ref,
        childDepth < depth ->
          schema.typeIncludesObjectBool expectedType runtimeType = true ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              (groundLiftSelectionSet schema runtimeType selectionSet)
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              selectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          actualType
          (if leafTypeNameBool schema expectedType then
            []
          else if objectTypeNameBool schema expectedType then
            groundLiftSelectionSet schema expectedType selectionSet
          else
            (groundObjectTypesForType schema expectedType).map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (groundLiftSelectionSet schema objectType selectionSet)))
          value
          =
        Execution.completeValue schema resolvers variableValues depth
          actualType selectionSet value := by
  intro depth actualType expectedType selectionSet value hsubtype hrecursive
  by_cases hleaf : leafTypeNameBool schema expectedType = true
  · simp [hleaf]
    apply completeValue_eq_of_child_object_lt_includes schema resolvers
      variableValues depth actualType [] selectionSet value
    intro childDepth runtimeType ref _hlt hactual
    have hexpected :
        schema.typeIncludesObjectBool expectedType runtimeType = true :=
      hsubtype runtimeType hactual
    have hnil := possibleTypes_eq_nil_of_leafTypeNameBool schema hleaf
    have hmem : runtimeType ∈ schema.getPossibleTypes expectedType :=
      List.contains_iff_mem.mp hexpected
    rw [hnil] at hmem
    cases hmem
  · have hleafFalse :
        leafTypeNameBool schema expectedType = false := by
      cases hmatch : leafTypeNameBool schema expectedType
      · rfl
      · exact False.elim (hleaf hmatch)
    by_cases hobject : objectTypeNameBool schema expectedType = true
    · simp [hleafFalse, hobject]
      exact completeValue_groundLiftSelectionSet_eq_of_object_subtype_lt
        schema resolvers variableValues depth actualType expectedType
        selectionSet value hobject hsubtype hrecursive
    · have hobjectFalse :
          objectTypeNameBool schema expectedType = false := by
        cases hmatch : objectTypeNameBool schema expectedType
        · rfl
        · exact False.elim (hobject hmatch)
      simp [hleafFalse, hobjectFalse, groundObjectTypesForType]
      apply completeValue_groundLift_possibleTypeFragments_eq_of_subtype_lt
        schema resolvers variableValues hschema depth actualType expectedType
        selectionSet value
      · intro runtimeType hactual
        exact List.contains_iff_mem.mp (hsubtype runtimeType hactual)
      · intro childDepth runtimeType ref hlt hmem
        exact hrecursive childDepth runtimeType ref hlt
          (List.contains_iff_mem.mpr hmem)

theorem completeValue_groundLiftFieldSelectionSet_eq_of_valueObjectsInclude_lt
    (schema : Schema) (resolvers : Execution.Resolvers DataModel.ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth actualType expectedType selectionSet
        (value : Execution.ResolverValue DataModel.ObjectRef),
      executionValueObjectsInclude schema expectedType value ->
      (∀ childDepth runtimeType ref,
        childDepth < depth ->
          schema.typeIncludesObjectBool expectedType runtimeType = true ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              (groundLiftSelectionSet schema runtimeType selectionSet)
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              selectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          actualType
          (if leafTypeNameBool schema expectedType then
            []
          else if objectTypeNameBool schema expectedType then
            groundLiftSelectionSet schema expectedType selectionSet
          else
            (groundObjectTypesForType schema expectedType).map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (groundLiftSelectionSet schema objectType selectionSet)))
          value
          =
        Execution.completeValue schema resolvers variableValues depth
          actualType selectionSet value
  | 0, _actualType, _expectedType, _selectionSet, _value, _hinclude,
    _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, actualType, expectedType, selectionSet, value, hinclude,
    hrecursive => by
      induction actualType generalizing value with
      | named actualType =>
          cases value with
          | null =>
              simp [Execution.completeValue]
          | scalar value =>
              simp [Execution.completeValue]
          | object runtimeType ref =>
              by_cases hactual :
                  schema.typeIncludesObjectBool actualType runtimeType = true
              · have hexpected :
                    schema.typeIncludesObjectBool expectedType runtimeType = true := by
                  simpa [executionValueObjectsInclude] using hinclude
                by_cases hleaf : leafTypeNameBool schema expectedType = true
                · have hnil := possibleTypes_eq_nil_of_leafTypeNameBool schema
                    hleaf
                  have hmem :
                      runtimeType ∈ schema.getPossibleTypes expectedType :=
                    List.contains_iff_mem.mp hexpected
                  rw [hnil] at hmem
                  cases hmem
                · have hleafFalse :
                      leafTypeNameBool schema expectedType = false := by
                    cases hmatch : leafTypeNameBool schema expectedType
                    · rfl
                    · exact False.elim (hleaf hmatch)
                  by_cases hobject :
                      objectTypeNameBool schema expectedType = true
                  · have hruntime : runtimeType = expectedType :=
                      typeIncludesObjectBool_eq_of_objectTypeNameBool_true
                        schema hobject hexpected
                    subst runtimeType
                    simp [Execution.completeValue, hactual, hleafFalse, hobject]
                    exact congrArg
                      (Execution.catchBubbleAsNull Execution.ResponseValue.object)
                      (by
                        simpa [Execution.executeSelectionSet,
                          Execution.executeRootSelectionSet,
                          collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                          using hrecursive depth expectedType ref
                            (Nat.lt_succ_self depth) hexpected)
                  · have hobjectFalse :
                        objectTypeNameBool schema expectedType = false := by
                      cases hmatch : objectTypeNameBool schema expectedType
                      · rfl
                      · exact False.elim (hobject hmatch)
                    have hmem :
                        runtimeType ∈ schema.getPossibleTypes expectedType :=
                      List.contains_iff_mem.mp hexpected
                    have hobjects :
                        ∀ objectType,
                          objectType ∈ schema.getPossibleTypes expectedType ->
                            objectTypeNameBool schema objectType = true := by
                      intro objectType hobjectType
                      exact objectTypeNameBool_eq_true_of_objectType schema
                        (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                          hschema expectedType objectType hobjectType)
                    have hbranch :=
                      executeSelectionSet_groundLift_possibleTypeFragments_runtime_branch
                        schema resolvers variableValues depth runtimeType (ref := ref)
                        (schema.getPossibleTypes expectedType) selectionSet hobjects
                        (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
                          hschema expectedType)
                        hmem
                        (hrecursive depth runtimeType ref
                          (Nat.lt_succ_self depth) hexpected)
                    simp [Execution.completeValue, hactual, hleafFalse,
                      hobjectFalse, groundObjectTypesForType]
                    exact congrArg
                      (Execution.catchBubbleAsNull Execution.ResponseValue.object)
                      (by
                        simpa [Execution.executeSelectionSet,
                          Execution.executeRootSelectionSet,
                          collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                          using hbranch)
              · have hactualFalse :
                    schema.typeIncludesObjectBool actualType runtimeType = false := by
                  cases hmatch :
                      schema.typeIncludesObjectBool actualType runtimeType
                  · rfl
                  · exact False.elim (hactual hmatch)
                simp [Execution.completeValue, hactualFalse]
          | list values =>
              simp [Execution.completeValue]
      | list itemType _ih =>
          cases value with
          | list values =>
              have hinclude' :
                  ∀ value, value ∈ values ->
                    executionValueObjectsInclude schema expectedType value := by
                intro value hvalue
                have hincludeValues :
                    ∀ value,
                      value ∈ values ->
                        executionValueObjectsInclude schema expectedType value := by
                  simpa [executionValueObjectsInclude] using hinclude
                exact hincludeValues value hvalue
              exact completeValue_list_eq_of_forall schema resolvers variableValues
                depth itemType
                (if leafTypeNameBool schema expectedType then
                  []
                else if objectTypeNameBool schema expectedType then
                  groundLiftSelectionSet schema expectedType selectionSet
                else
                  (groundObjectTypesForType schema expectedType).map
                    (fun objectType =>
                      Selection.inlineFragment (some objectType) []
                        (groundLiftSelectionSet schema objectType selectionSet)))
                selectionSet values
                (by
                  intro element helement
                  exact
                    completeValue_groundLiftFieldSelectionSet_eq_of_valueObjectsInclude_lt
                      schema resolvers variableValues hschema depth itemType
                      expectedType selectionSet element (hinclude' element helement)
                      (by
                        intro childDepth runtimeType ref hlt hexpected
                        exact hrecursive childDepth runtimeType ref
                          (Nat.lt_trans hlt (Nat.lt_succ_self depth))
                          hexpected))
          | null => simp [Execution.completeValue]
          | scalar value => simp [Execution.completeValue]
          | object runtimeType ref => simp [Execution.completeValue]
      | nonNull inner ih =>
          have hinner :
              Execution.completeValue schema resolvers variableValues
                  (depth + 1) inner
                  (if leafTypeNameBool schema expectedType then
                    []
                  else if objectTypeNameBool schema expectedType then
                    groundLiftSelectionSet schema expectedType selectionSet
                  else
                    (groundObjectTypesForType schema expectedType).map
                      (fun objectType =>
                        Selection.inlineFragment (some objectType) []
                          (groundLiftSelectionSet schema objectType selectionSet)))
                  value =
                Execution.completeValue schema resolvers variableValues
                  (depth + 1) inner selectionSet value :=
            ih value hinclude
          simpa [Execution.completeValue] using congrArg
            Execution.nonNullCompletion hinner

theorem executeField_singleton_groundLift_eq_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (depth : Nat) (parentType runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition) :
    schema.typeIncludesObjectBool parentType runtimeType = true ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
    (∀ childDepth runtimeType ref,
      childDepth < depth ->
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          runtimeType = true ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref)
            (groundLiftSelectionSet schema runtimeType selectionSet)
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref) selectionSet) ->
      Execution.executeField schema (store.resolvers schema) variableValues
        (depth + 1) (.object runtimeType) responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet :=
            if leafTypeNameBool schema fieldDefinition.outputType.namedType then
              []
            else if objectTypeNameBool schema
                fieldDefinition.outputType.namedType then
              groundLiftSelectionSet schema
                fieldDefinition.outputType.namedType selectionSet
            else
              (groundObjectTypesForType schema
                fieldDefinition.outputType.namedType).map
                (fun objectType =>
                  Selection.inlineFragment (some objectType) []
                    (groundLiftSelectionSet schema objectType selectionSet))
        }]
      =
      Execution.executeField schema (store.resolvers schema) variableValues
        (depth + 1) (.object runtimeType) responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }] := by
  intro hinclude hlookup hrecursive
  let sourceField : Execution.ExecutableField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      selectionSet := selectionSet
    }
  let liftedSelectionSet :=
    if leafTypeNameBool schema fieldDefinition.outputType.namedType then
      []
    else if objectTypeNameBool schema fieldDefinition.outputType.namedType then
      groundLiftSelectionSet schema fieldDefinition.outputType.namedType
        selectionSet
    else
      (groundObjectTypesForType schema
        fieldDefinition.outputType.namedType).map
        (fun objectType =>
          Selection.inlineFragment (some objectType) []
            (groundLiftSelectionSet schema objectType selectionSet))
  let liftedFields : List Execution.ExecutableField :=
    if leafTypeNameBool schema fieldDefinition.outputType.namedType then
      []
    else if objectTypeNameBool schema fieldDefinition.outputType.namedType then
      (groundLiftSelectionSet schema fieldDefinition.outputType.namedType
        selectionSet).map Execution.selectionExecutableField
    else
      (groundObjectTypesForType schema
        fieldDefinition.outputType.namedType).map
        (fun objectType =>
          Execution.selectionExecutableField
            (Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType selectionSet)))
  have hreturn :
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        =
      fieldDefinition.outputType.namedType := by
    simp [Schema.fieldReturnType?, hlookup]
  have hincludeResolved :
      executionValueObjectsInclude schema fieldDefinition.outputType.namedType
        ((store.resolvers schema).resolve parentType fieldName arguments
          (.object runtimeType)) := by
    simpa [DataModel.Store.resolvers] using
      resolve_objectsInclude_of_static_lookupField schema store parentType
        runtimeType fieldName arguments fieldDefinition hschema hstore
        hinclude hlookup
  have hcomplete :
      Execution.completeValue schema (store.resolvers schema) variableValues
        depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        liftedFields
        ((store.resolvers schema).resolve parentType fieldName arguments
          (.object runtimeType))
      =
      Execution.completeValue schema (store.resolvers schema) variableValues
        depth ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        selectionSet
        ((store.resolvers schema).resolve parentType fieldName arguments
          (.object runtimeType)) := by
    rw [hreturn]
    simpa [liftedFields] using
      completeValue_groundLiftFieldSelectionSet_eq_of_valueObjectsInclude_lt
        schema (store.resolvers schema) variableValues hschema depth
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType selectionSet
        ((store.resolvers schema).resolve parentType fieldName arguments
          (.object runtimeType))
        hincludeResolved hrecursive
  simpa [sourceField, liftedSelectionSet] using
    executeField_singleton_eq_group_of_completeValue schema
      (store.resolvers schema) variableValues depth
      (.object runtimeType) responseName sourceField []
      liftedSelectionSet
      (by
        rw [hlookup]
        cases hresolved :
            (store.resolvers schema).resolve parentType fieldName arguments
              (.object runtimeType) with
        | none =>
            simp []
        | some value =>
            simp []
            have hincludeValue :
                executionValueObjectsInclude schema
                  fieldDefinition.outputType.namedType value := by
              simpa [hresolved] using hincludeResolved
            have hcompleteValue :
                Execution.completeValue schema (store.resolvers schema)
                    variableValues depth fieldDefinition.outputType liftedFields
                    value =
                  Execution.completeValue schema (store.resolvers schema)
                    variableValues depth fieldDefinition.outputType selectionSet
                    value := by
              simpa [liftedFields] using
                completeValue_groundLiftFieldSelectionSet_eq_of_valueObjectsInclude_lt
                  schema (store.resolvers schema) variableValues hschema depth
                  fieldDefinition.outputType
                  fieldDefinition.outputType.namedType selectionSet value
                  hincludeValue hrecursive
            have hleft :=
              completeValue_eq_of_mergedFieldSelectionSet_eq schema
                (store.resolvers schema) variableValues depth
                fieldDefinition.outputType
                [{ sourceField with selectionSet := liftedSelectionSet }]
                liftedFields value
                (by
                  simp [Execution.mergedFieldSelectionSet, liftedFields,
                    liftedSelectionSet])
            have hright :=
              completeValue_singleton_selectionSet_eq schema
                (store.resolvers schema) variableValues depth
                fieldDefinition.outputType sourceField selectionSet value
            exact hleft.trans (hcompleteValue.trans hright.symm))

theorem executeField_singleton_groundLift_scoped_eq_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (depth : Nat) (execParent liftParent runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection)
    (execFieldDefinition liftFieldDefinition : FieldDefinition) :
    schema.typeIncludesObjectBool liftParent runtimeType = true ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    (∀ childDepth runtimeType ref,
      childDepth < depth ->
        schema.typeIncludesObjectBool liftFieldDefinition.outputType.namedType
          runtimeType = true ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref)
            (groundLiftSelectionSet schema runtimeType selectionSet)
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref) selectionSet) ->
      Execution.executeField schema (store.resolvers schema) variableValues
        (depth + 1) (.object runtimeType) responseName
        [{
          parentType := execParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet :=
            if leafTypeNameBool schema liftFieldDefinition.outputType.namedType
            then
              []
            else if objectTypeNameBool schema
                liftFieldDefinition.outputType.namedType then
              groundLiftSelectionSet schema
                liftFieldDefinition.outputType.namedType selectionSet
            else
              (groundObjectTypesForType schema
                liftFieldDefinition.outputType.namedType).map
                (fun objectType =>
                  Selection.inlineFragment (some objectType) []
                    (groundLiftSelectionSet schema objectType selectionSet))
        }]
      =
      Execution.executeField schema (store.resolvers schema) variableValues
        (depth + 1) (.object runtimeType) responseName
        [{
          parentType := execParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }] := by
  intro hliftInclude hexecLookup hliftLookup hrecursive
  let sourceField : Execution.ExecutableField :=
    {
      parentType := execParent,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      selectionSet := selectionSet
    }
  let liftedSelectionSet :=
    if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
      []
    else if objectTypeNameBool schema
        liftFieldDefinition.outputType.namedType then
      groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
        selectionSet
    else
      (groundObjectTypesForType schema
        liftFieldDefinition.outputType.namedType).map
        (fun objectType =>
          Selection.inlineFragment (some objectType) []
            (groundLiftSelectionSet schema objectType selectionSet))
  let liftedFields : List Execution.ExecutableField :=
    if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
      []
    else if objectTypeNameBool schema
        liftFieldDefinition.outputType.namedType then
      (groundLiftSelectionSet schema liftFieldDefinition.outputType.namedType
        selectionSet).map Execution.selectionExecutableField
    else
      (groundObjectTypesForType schema
        liftFieldDefinition.outputType.namedType).map
        (fun objectType =>
          Execution.selectionExecutableField
            (Selection.inlineFragment (some objectType) []
              (groundLiftSelectionSet schema objectType selectionSet)))
  have hreturn :
      ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        =
      execFieldDefinition.outputType.namedType := by
    simp [Schema.fieldReturnType?, hexecLookup]
  have hincludeResolved :
      executionValueObjectsInclude schema
        liftFieldDefinition.outputType.namedType
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType)) := by
    rw [resolvers_parentType_insensitive schema store execParent
      liftParent fieldName arguments (.object runtimeType)]
    simpa [DataModel.Store.resolvers] using
      resolve_objectsInclude_of_static_lookupField schema store liftParent
        runtimeType fieldName arguments liftFieldDefinition hschema
        hstore hliftInclude hliftLookup
  have hcomplete :
      Execution.completeValue schema (store.resolvers schema) variableValues
        depth ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        liftedFields
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType))
      =
      Execution.completeValue schema (store.resolvers schema) variableValues
        depth ((schema.fieldReturnType? execParent fieldName).getD fieldName)
        selectionSet
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType)) := by
    rw [hreturn]
    simpa [liftedFields] using
      completeValue_groundLiftFieldSelectionSet_eq_of_valueObjectsInclude_lt
        schema (store.resolvers schema) variableValues hschema depth
        execFieldDefinition.outputType.namedType
        liftFieldDefinition.outputType.namedType selectionSet
        ((store.resolvers schema).resolve execParent fieldName arguments
          (.object runtimeType))
        hincludeResolved hrecursive
  simpa [sourceField, liftedSelectionSet] using
    executeField_singleton_eq_group_of_completeValue schema
      (store.resolvers schema) variableValues depth
      (.object runtimeType) responseName sourceField []
      liftedSelectionSet
      (by
        rw [hexecLookup]
        cases hresolved :
            (store.resolvers schema).resolve execParent fieldName arguments
              (.object runtimeType) with
        | none =>
            simp []
        | some value =>
            simp []
            have hincludeValue :
                executionValueObjectsInclude schema
                  liftFieldDefinition.outputType.namedType value := by
              simpa [hresolved] using hincludeResolved
            have hcompleteValue :
                Execution.completeValue schema (store.resolvers schema)
                    variableValues depth execFieldDefinition.outputType
                    liftedFields value =
                  Execution.completeValue schema (store.resolvers schema)
                    variableValues depth execFieldDefinition.outputType
                    selectionSet value := by
              simpa [liftedFields] using
                completeValue_groundLiftFieldSelectionSet_eq_of_valueObjectsInclude_lt
                  schema (store.resolvers schema) variableValues hschema depth
                  execFieldDefinition.outputType
                  liftFieldDefinition.outputType.namedType selectionSet value
                  hincludeValue hrecursive
            have hleft :=
              completeValue_eq_of_mergedFieldSelectionSet_eq schema
                (store.resolvers schema) variableValues depth
                execFieldDefinition.outputType
                [{ sourceField with selectionSet := liftedSelectionSet }]
                liftedFields value
                (by
                  simp [Execution.mergedFieldSelectionSet, liftedFields,
                    liftedSelectionSet])
            have hright :=
              completeValue_singleton_selectionSet_eq schema
                (store.resolvers schema) variableValues depth
                execFieldDefinition.outputType sourceField selectionSet value
            exact hleft.trans (hcompleteValue.trans hright.symm))

theorem executeSelectionSet_field_head_groundLift_noDuplicate_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (depth : Nat) (parentType runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet liftedRest rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    schema.typeIncludesObjectBool parentType runtimeType = true ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
    responseName ∉
      (Execution.collectFields schema variableValues parentType
        (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
        liftedRest).map Prod.fst ->
    responseName ∉
      (Execution.collectFields schema variableValues parentType
        (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
        rest).map Prod.fst ->
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth parentType (.object runtimeType)
      liftedRest
      =
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth parentType (.object runtimeType) rest ->
    (∀ childDepth runtimeType ref,
      childDepth < depth - 1 ->
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          runtimeType = true ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref)
            (groundLiftSelectionSet schema runtimeType selectionSet)
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref) selectionSet) ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType)
        (Selection.field responseName fieldName arguments []
          (if leafTypeNameBool schema fieldDefinition.outputType.namedType then
            []
          else if objectTypeNameBool schema
              fieldDefinition.outputType.namedType then
            groundLiftSelectionSet schema
              fieldDefinition.outputType.namedType selectionSet
          else
            (groundObjectTypesForType schema
              fieldDefinition.outputType.namedType).map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (groundLiftSelectionSet schema objectType selectionSet)))
          :: liftedRest)
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth parentType (.object runtimeType)
        (Selection.field responseName fieldName arguments [] selectionSet
          :: rest) := by
  intro hinclude hlookup hnotinLift hnotinOriginal htail hrecursive
  cases depth with
  | zero =>
      let liftedSelectionSet :=
        if leafTypeNameBool schema fieldDefinition.outputType.namedType then
          []
        else if objectTypeNameBool schema fieldDefinition.outputType.namedType
        then
          groundLiftSelectionSet schema fieldDefinition.outputType.namedType
            selectionSet
        else
          (groundObjectTypesForType schema
            fieldDefinition.outputType.namedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet))
      let liftedField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := liftedSelectionSet
        }
      let originalField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }
      have hliftCollect :
          Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
          (responseName, [liftedField])
            :: Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest := by
        simpa [liftedField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments liftedSelectionSet liftedRest
            hnotinLift
      have horiginalCollect :
          Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
          =
          (responseName, [originalField])
            :: Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest := by
        simpa [originalField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments selectionSet rest
            hnotinOriginal
      simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
      rw [show
        Execution.collectFields schema variableValues parentType
          (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
          (Selection.field responseName fieldName arguments []
            (if leafTypeNameBool schema fieldDefinition.outputType.namedType then
              []
            else if objectTypeNameBool schema fieldDefinition.outputType.namedType
              then
                groundLiftSelectionSet schema
                  fieldDefinition.outputType.namedType selectionSet
              else
                (groundObjectTypesForType schema
                  fieldDefinition.outputType.namedType).map
                  (fun objectType =>
                    Selection.inlineFragment (some objectType) []
                      (groundLiftSelectionSet schema objectType selectionSet)))
            :: liftedRest)
        =
        (responseName, [liftedField])
          :: Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            liftedRest
        from by
          simpa [liftedSelectionSet] using hliftCollect]
      rw [horiginalCollect]
      have htailCollected :
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues 0
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest)
          =
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues 0
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest) := by
        simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
          using htail
      simp [Execution.executeCollectedFields, Execution.executeField,
        Execution.Result.combine, htailCollected]
  | succ fieldDepth =>
      let liftedSelectionSet :=
        if leafTypeNameBool schema fieldDefinition.outputType.namedType then
          []
        else if objectTypeNameBool schema fieldDefinition.outputType.namedType
        then
          groundLiftSelectionSet schema fieldDefinition.outputType.namedType
            selectionSet
        else
          (groundObjectTypesForType schema
            fieldDefinition.outputType.namedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet))
      let liftedField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := liftedSelectionSet
        }
      let originalField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }
      have hliftCollect :
          Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
          (responseName, [liftedField])
            :: Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest := by
        simpa [liftedField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments liftedSelectionSet liftedRest
            hnotinLift
      have horiginalCollect :
          Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
          =
          (responseName, [originalField])
            :: Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest := by
        simpa [originalField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments selectionSet rest
            hnotinOriginal
      have hhead :
          Execution.executeField schema (store.resolvers schema) variableValues
            (fieldDepth + 1) (.object runtimeType) responseName
            [liftedField]
          =
          Execution.executeField schema (store.resolvers schema) variableValues
            (fieldDepth + 1) (.object runtimeType) responseName
            [originalField] := by
        simpa [liftedField, originalField, liftedSelectionSet] using
          executeField_singleton_groundLift_eq_on_store schema store
            variableValues hschema hstore fieldDepth parentType runtimeType
            responseName fieldName arguments selectionSet
            fieldDefinition hinclude hlookup
            (by
              intro childDepth runtimeType ref hlt hchildInclude
              exact hrecursive childDepth runtimeType ref
                (Nat.lt_of_lt_of_le hlt (Nat.sub_le fieldDepth 0))
                hchildInclude)
      have htailCollected :
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues (fieldDepth + 1) (.object runtimeType)
            (Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest)
          =
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues (fieldDepth + 1) (.object runtimeType)
            (Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest) := by
        simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
          ]
          using htail
      change
        Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues (fieldDepth + 1) parentType
            (.object runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
        Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues (fieldDepth + 1) parentType
            (.object runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
      simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
      rw [
        show Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
          (responseName, [liftedField])
            :: Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest by
          simpa [] using hliftCollect,
        show Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
          =
          (responseName, [originalField])
            :: Execution.collectFields schema variableValues parentType
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest by
          simpa [] using horiginalCollect]
      simpa [] using
        executeCollectedFields_cons_eq_of_parts schema
          (store.resolvers schema) variableValues (fieldDepth + 1)
          (.object runtimeType) (responseName, [liftedField])
          (responseName, [originalField])
          (Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            liftedRest)
          (Execution.collectFields schema variableValues parentType
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            rest)
          hhead htailCollected

theorem executeSelectionSet_field_head_groundLift_scoped_noDuplicate_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (depth : Nat) (execParent liftParent runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet liftedRest rest : List Selection)
    (execFieldDefinition liftFieldDefinition : FieldDefinition) :
    schema.typeIncludesObjectBool liftParent runtimeType = true ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    responseName ∉
      (Execution.collectFields schema variableValues execParent
        (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
        liftedRest).map Prod.fst ->
    responseName ∉
      (Execution.collectFields schema variableValues execParent
        (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
        rest).map Prod.fst ->
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent (.object runtimeType)
      liftedRest
      =
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent (.object runtimeType) rest ->
    (∀ childDepth runtimeType ref,
      childDepth < depth - 1 ->
        schema.typeIncludesObjectBool liftFieldDefinition.outputType.namedType
          runtimeType = true ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref)
            (groundLiftSelectionSet schema runtimeType selectionSet)
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref) selectionSet) ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object runtimeType)
        (Selection.field responseName fieldName arguments []
          (if leafTypeNameBool schema liftFieldDefinition.outputType.namedType
          then
            []
          else if objectTypeNameBool schema
              liftFieldDefinition.outputType.namedType then
            groundLiftSelectionSet schema
              liftFieldDefinition.outputType.namedType selectionSet
          else
            (groundObjectTypesForType schema
              liftFieldDefinition.outputType.namedType).map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (groundLiftSelectionSet schema objectType selectionSet)))
          :: liftedRest)
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object runtimeType)
        (Selection.field responseName fieldName arguments [] selectionSet
          :: rest) := by
  intro hliftInclude hexecLookup hliftLookup hnotinLift hnotinOriginal
    htail hrecursive
  cases depth with
  | zero =>
      let liftedSelectionSet :=
        if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
          []
        else if objectTypeNameBool schema
            liftFieldDefinition.outputType.namedType then
          groundLiftSelectionSet schema
            liftFieldDefinition.outputType.namedType selectionSet
        else
          (groundObjectTypesForType schema
            liftFieldDefinition.outputType.namedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet))
      let liftedField : Execution.ExecutableField :=
        {
          parentType := execParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := liftedSelectionSet
        }
      let originalField : Execution.ExecutableField :=
        {
          parentType := execParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }
      have hliftCollect :
          Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
          (responseName, [liftedField])
            :: Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest := by
        simpa [liftedField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments liftedSelectionSet liftedRest
            hnotinLift
      have horiginalCollect :
          Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
          =
          (responseName, [originalField])
            :: Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest := by
        simpa [originalField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments selectionSet rest
            hnotinOriginal
      simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
      rw [show
        Execution.collectFields schema variableValues execParent
          (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
          (Selection.field responseName fieldName arguments []
            (if leafTypeNameBool schema liftFieldDefinition.outputType.namedType
            then
              []
            else if objectTypeNameBool schema
                liftFieldDefinition.outputType.namedType then
              groundLiftSelectionSet schema
                liftFieldDefinition.outputType.namedType selectionSet
            else
              (groundObjectTypesForType schema
                liftFieldDefinition.outputType.namedType).map
                (fun objectType =>
                  Selection.inlineFragment (some objectType) []
                    (groundLiftSelectionSet schema objectType selectionSet)))
            :: liftedRest)
        =
        (responseName, [liftedField])
          :: Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            liftedRest
        from by
          simpa [liftedSelectionSet] using hliftCollect]
      rw [horiginalCollect]
      have htailCollected :
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues 0
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest)
          =
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues 0
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest) := by
        simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
          using htail
      simp [Execution.executeCollectedFields, Execution.executeField,
        Execution.Result.combine, htailCollected]
  | succ fieldDepth =>
      let liftedSelectionSet :=
        if leafTypeNameBool schema liftFieldDefinition.outputType.namedType then
          []
        else if objectTypeNameBool schema
            liftFieldDefinition.outputType.namedType then
          groundLiftSelectionSet schema
            liftFieldDefinition.outputType.namedType selectionSet
        else
          (groundObjectTypesForType schema
            liftFieldDefinition.outputType.namedType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (groundLiftSelectionSet schema objectType selectionSet))
      let liftedField : Execution.ExecutableField :=
        {
          parentType := execParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := liftedSelectionSet
        }
      let originalField : Execution.ExecutableField :=
        {
          parentType := execParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }
      have hliftCollect :
          Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
          (responseName, [liftedField])
            :: Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest := by
        simpa [liftedField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments liftedSelectionSet liftedRest
            hnotinLift
      have horiginalCollect :
          Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
          =
          (responseName, [originalField])
            :: Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest := by
        simpa [originalField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            responseName fieldName arguments selectionSet rest
            hnotinOriginal
      have hhead :
          Execution.executeField schema (store.resolvers schema) variableValues
            (fieldDepth + 1) (.object runtimeType) responseName
            [liftedField]
          =
          Execution.executeField schema (store.resolvers schema) variableValues
            (fieldDepth + 1) (.object runtimeType) responseName
            [originalField] := by
        simpa [liftedField, originalField, liftedSelectionSet] using
          executeField_singleton_groundLift_scoped_eq_on_store schema store
            variableValues hschema hstore fieldDepth execParent liftParent
            runtimeType responseName fieldName arguments selectionSet
            execFieldDefinition liftFieldDefinition hliftInclude hexecLookup
            hliftLookup
            (by
              intro childDepth runtimeType ref hlt hchildInclude
              exact hrecursive childDepth runtimeType ref
                (by simpa using hlt) hchildInclude)
      have htailCollected :
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues (fieldDepth + 1) (.object runtimeType)
            (Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest)
          =
          Execution.executeCollectedFields schema (store.resolvers schema)
            variableValues (fieldDepth + 1) (.object runtimeType)
            (Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest) := by
        simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
          ]
          using htail
      change
        Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues (fieldDepth + 1) execParent
            (.object runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
        Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues (fieldDepth + 1) execParent
            (.object runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
      simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
      rw [
        show Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              liftedSelectionSet :: liftedRest)
          =
          (responseName, [liftedField])
            :: Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              liftedRest by
          simpa [] using hliftCollect,
        show Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest)
          =
          (responseName, [originalField])
            :: Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
              rest by
          simpa [] using horiginalCollect]
      simpa [] using
        executeCollectedFields_cons_eq_of_parts schema
          (store.resolvers schema) variableValues (fieldDepth + 1)
          (.object runtimeType) (responseName, [liftedField])
          (responseName, [originalField])
          (Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            liftedRest)
          (Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
            rest)
          hhead htailCollected

theorem executeSelectionSet_field_head_groundLift_scoped_responseNameFree_on_store
    (schema : Schema) (store : DataModel.Store)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hstore : store.wellTyped schema)
    (depth : Nat) (execParent liftParent runtimeType : Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet rest : List Selection)
    (execFieldDefinition liftFieldDefinition : FieldDefinition) :
    objectTypeNameBool schema execParent = true ->
    schema.typeIncludesObjectBool execParent runtimeType = true ->
    schema.typeIncludesObjectBool liftParent runtimeType = true ->
    schema.lookupField execParent fieldName = some execFieldDefinition ->
    schema.lookupField liftParent fieldName = some liftFieldDefinition ->
    selectionSetDirectiveFree rest ->
    selectionSetResponseNameFree schema execParent responseName rest ->
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent (.object runtimeType)
      (groundLiftSelectionSet schema liftParent rest)
      =
    Execution.executeSelectionSet schema (store.resolvers schema)
      variableValues depth execParent (.object runtimeType) rest ->
    (∀ childDepth runtimeType ref,
      childDepth < depth - 1 ->
        schema.typeIncludesObjectBool liftFieldDefinition.outputType.namedType
          runtimeType = true ->
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref)
            (groundLiftSelectionSet schema runtimeType selectionSet)
          =
          Execution.executeSelectionSet schema (store.resolvers schema)
            variableValues childDepth runtimeType
            (.object runtimeType ref) selectionSet) ->
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object runtimeType)
        (groundLiftSelectionSet schema liftParent
          (Selection.field responseName fieldName arguments [] selectionSet
            :: rest))
      =
      Execution.executeSelectionSet schema (store.resolvers schema)
        variableValues depth execParent (.object runtimeType)
        (Selection.field responseName fieldName arguments [] selectionSet
          :: rest) := by
  intro hexecObject hexecInclude hliftInclude hexecLookup hliftLookup
    hrestFree hrestResponseFree htail hrecursive
  have hsourceValue :
      ∃ runtimeType' ref,
        Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType =
          .object runtimeType' ref
          ∧ schema.typeIncludesObjectBool execParent runtimeType' = true :=
    ⟨runtimeType, (none : Option DataModel.ObjectRef), rfl, hexecInclude⟩
  have hnotinOriginal :
      responseName ∉
        (Execution.collectFields schema variableValues execParent
          (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
          rest).map Prod.fst :=
    collectFields_responseName_not_mem_of_responseNameFree schema
      variableValues execParent
      (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
      responseName
      hexecObject hsourceValue rest hrestFree hrestResponseFree
  have hliftRestFree :
      selectionSetDirectiveFree
        (groundLiftSelectionSet schema liftParent rest) :=
    groundLiftSelectionSet_directiveFree schema liftParent rest hrestFree
  have hliftResponseFree :
      selectionSetResponseNameFree schema execParent responseName
        (groundLiftSelectionSet schema liftParent rest) :=
    groundLiftSelectionSet_responseNameFree schema execParent responseName
      liftParent rest hrestResponseFree
  have hnotinLift :
      responseName ∉
        (Execution.collectFields schema variableValues execParent
          (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
          (groundLiftSelectionSet schema liftParent rest)).map Prod.fst :=
    collectFields_responseName_not_mem_of_responseNameFree schema
      variableValues execParent
      (Execution.ResolverValue.object (ObjectRef := DataModel.ObjectRef) runtimeType)
      responseName
      hexecObject hsourceValue (groundLiftSelectionSet schema liftParent rest)
      hliftRestFree hliftResponseFree
  simpa [groundLiftSelectionSet, groundLiftSelection, hliftLookup] using
    executeSelectionSet_field_head_groundLift_scoped_noDuplicate_on_store
      schema store variableValues hschema hstore depth execParent liftParent
      runtimeType responseName fieldName arguments selectionSet
      (groundLiftSelectionSet schema liftParent rest) rest
      execFieldDefinition liftFieldDefinition hliftInclude hexecLookup
      hliftLookup hnotinLift hnotinOriginal htail hrecursive

end GroundTypeLifting

end NormalForm

end GraphQL
