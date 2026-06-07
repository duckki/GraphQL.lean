import GraphQL.NormalForm.GroundTypeNormalization.InlineFragmentSemantics

/-!
Abstract return grounding semantics for ground-type normalization.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectIdentity : Type}

theorem collectFields_possibleTypeFragments_not_mem_eq_nil
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
              (normalizeSelectionSet schema objectType selectionSet)))
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

theorem executeSelectionSet_append_possibleTypeFragments_not_mem
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (identity : ObjectIdentity)
    (possibleTypes : List Name)
    (selectionSet suffix : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      objectTypeNameBool schema objectType = true) ->
    runtimeType ∉ possibleTypes ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (suffix ++
          possibleTypes.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType selectionSet)))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity) suffix := by
  intro hobjects hnotin
  simp [Execution.executeSelectionSet]
  rw [collectFields_append]
  rw [collectFields_possibleTypeFragments_not_mem_eq_nil schema
    variableValues runtimeType identity possibleTypes selectionSet hobjects
    hnotin]
  simp [Execution.mergeExecutableGroups_nil_right]

theorem executeSelectionSet_possibleTypeFragments_runtime_branch
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (identity : ObjectIdentity)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType identity)
      (normalizeSelectionSet schema runtimeType selectionSet)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      runtimeType (.object runtimeType identity) selectionSet ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity)
        (possibleTypes.map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (normalizeSelectionSet schema objectType selectionSet)))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (.object runtimeType identity) selectionSet := by
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
              (.object runtimeType identity) objectType = false :=
          doesFragmentTypeApplyBool_object_other_false schema hobject hne
        rw [executeSelectionSet_inlineFragment_some_directiveFree_skip
          schema resolvers variableValues depth runtimeType objectType
          (.object runtimeType identity)
          (normalizeSelectionSet schema objectType selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType selectionSet)))
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
          doesFragmentTypeApplyBool_object_self schema hobject
        rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
          schema resolvers variableValues depth runtimeType runtimeType
          (.object runtimeType identity)
          (normalizeSelectionSet schema runtimeType selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType selectionSet)))
          happly]
        rw [executeSelectionSet_append_possibleTypeFragments_not_mem schema
          resolvers variableValues depth runtimeType identity rest
          selectionSet (normalizeSelectionSet schema runtimeType selectionSet)
          hrestObjects hrestNotin]
        exact hrecursive

theorem completeValue_possibleTypeFragments_eq_of_child_object_lt
    (schema : Schema) (resolvers : Execution.Resolvers ObjectIdentity)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth childType selectionSet value,
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          runtimeType ∈ schema.getPossibleTypes childType ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              (normalizeSelectionSet schema runtimeType selectionSet)
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              selectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          childType
          ((schema.getPossibleTypes childType).map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType selectionSet)))
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
      | object runtimeType identity =>
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
              executeSelectionSet_possibleTypeFragments_runtime_branch
                schema resolvers variableValues depth runtimeType identity
                (schema.getPossibleTypes childType) selectionSet hobjects
                (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
                  hschema childType)
                hmem
                (hrecursive depth runtimeType identity
                  (Nat.lt_succ_self depth) hmem)
            simp [Execution.completeValue, hinclude]
            exact hbranch
          · have hfalse :
                schema.typeIncludesObjectBool childType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool childType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
      | list values =>
          simp [Execution.completeValue]
          intro element helement
          exact completeValue_possibleTypeFragments_eq_of_child_object_lt
            schema resolvers variableValues hschema depth childType
            selectionSet element
            (by
              intro childDepth runtimeType identity hlt hmem
              exact hrecursive childDepth runtimeType identity
                (Nat.lt_trans hlt (Nat.lt_succ_self depth)) hmem)



end GroundTypeNormalization

end NormalForm

end GraphQL
