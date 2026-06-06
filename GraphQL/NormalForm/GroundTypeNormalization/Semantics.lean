import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection

/-!
Semantic bridge lemmas for directive-free ground-type normalization.

The remaining hard proof is selection-set preservation for `normalizeSelectionSet`.
This module isolates the operation-level and store-backed lifts from that local
selection-set obligation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem executeSelectionSet_inlineFragment_some_directiveFree_skip
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition =
      false ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source rest := by
  intro hskip
  simp [Execution.executeSelectionSet,
    collectFields_inlineFragment_some_directiveFree_skip_eq schema
      variableValues parentType typeCondition source selectionSet rest hskip]

theorem executeSelectionSet_inlineFragment_none_directiveFree_flatten
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (Selection.inlineFragment none [] selectionSet :: rest)
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (selectionSet ++ rest) := by
  simp [Execution.executeSelectionSet,
    collectFields_inlineFragment_none_directiveFree_flatten]

theorem executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.doesFragmentTypeApplyBool schema parentType source typeCondition =
      true ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source (selectionSet ++ rest) := by
  intro happly
  simp [Execution.executeSelectionSet,
    collectFields_inlineFragment_some_directiveFree_apply_flatten, happly]

theorem lookupType_name_eq (schema : Schema) {typeName : Name}
    {typeDefinition : TypeDefinition} :
    schema.lookupType typeName = some typeDefinition ->
      typeDefinition.name = typeName := by
  intro hlookup
  have hmatch := List.find?_some hlookup
  simpa [Schema.lookupType] using hmatch

theorem typeIncludesObjectBool_eq_of_objectTypeNameBool_true
    (schema : Schema) {typeName runtimeType : Name} :
    objectTypeNameBool schema typeName = true ->
      schema.typeIncludesObjectBool typeName runtimeType = true ->
        runtimeType = typeName := by
  intro hobject hinclude
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = typeName :=
            lookupType_name_eq schema hlookup
          simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
            hlookup, hname] at hinclude
          exact hinclude
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_true_of_typesOverlapBool_true_of_object_source
    (schema : Schema) {parentType typeCondition : Name}
    {source : Execution.Value} :
    objectTypeNameBool schema parentType = true ->
      (∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
        schema.typesOverlapBool parentType typeCondition = true ->
          Execution.doesFragmentTypeApplyBool schema parentType source
            typeCondition = true := by
  intro hobject hsource hoverlap
  rcases hsource with ⟨runtimeType, identity, hsourceEq, hparent⟩
  subst source
  have hruntime :
      runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hparent
  subst runtimeType
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType parentType with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = parentType :=
            lookupType_name_eq schema hlookup
          unfold Schema.typesOverlapBool at hoverlap
          simp [Schema.getPossibleTypes, hlookup, hname] at hoverlap
          simpa [Execution.doesFragmentTypeApplyBool,
            Execution.runtimeObjectType?] using hoverlap
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_false_of_typesOverlapBool_false
    (schema : Schema) {parentType typeCondition runtimeType : Name}
    {identity : Nat} :
    schema.typeIncludesObjectBool parentType runtimeType = true ->
      schema.typesOverlapBool parentType typeCondition = false ->
        Execution.doesFragmentTypeApplyBool schema parentType
          (.object runtimeType identity) typeCondition = false := by
  intro hparent hoverlap
  unfold Execution.doesFragmentTypeApplyBool
  cases hcondition :
      schema.typeIncludesObjectBool typeCondition runtimeType
  · simp [Execution.runtimeObjectType?, hcondition]
  · have hparentMem :
        runtimeType ∈ schema.getPossibleTypes parentType := by
      exact List.contains_iff_mem.mp hparent
    have hoverlapTrue :
        schema.typesOverlapBool parentType typeCondition = true := by
      unfold Schema.typesOverlapBool
      exact List.any_eq_true.mpr
        ⟨runtimeType, hparentMem, hcondition⟩
    rw [hoverlap] at hoverlapTrue
    contradiction

theorem rootSourceAppliesBool_true_object
    (schema : Schema) (operation : Operation) (source : Execution.Value) :
    Execution.rootSourceAppliesBool schema operation source = true ->
      ∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool operation.rootType runtimeType = true := by
  intro hroot
  cases source with
  | null =>
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?] at hroot
  | scalar value =>
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?] at hroot
  | object runtimeType identity =>
      exact ⟨runtimeType, identity, rfl, hroot⟩
  | list values =>
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?] at hroot

theorem doesFragmentTypeApplyBool_false_of_typesOverlapBool_false_of_source
    (schema : Schema) {parentType typeCondition : Name}
    {source : Execution.Value} :
    (∃ runtimeType identity,
      source = .object runtimeType identity
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
      schema.typesOverlapBool parentType typeCondition = false ->
        Execution.doesFragmentTypeApplyBool schema parentType source
          typeCondition = false := by
  intro hsource hoverlap
  rcases hsource with ⟨runtimeType, identity, hsourceEq, hparent⟩
  subst source
  exact doesFragmentTypeApplyBool_false_of_typesOverlapBool_false schema
    hparent hoverlap

theorem objectTypeNameBool_eq_true_of_objectType
    (schema : Schema) {typeName : Name} :
    schema.objectType typeName ->
      objectTypeNameBool schema typeName = true := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  simp [objectTypeNameBool, hlookup]

theorem typeIncludesObjectBool_self_of_objectTypeNameBool
    (schema : Schema) {typeName : Name} :
    objectTypeNameBool schema typeName = true ->
      schema.typeIncludesObjectBool typeName typeName = true := by
  intro hobject
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = typeName :=
            lookupType_name_eq schema hlookup
          simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
            hlookup, hname]
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_object_self
    (schema : Schema) {runtimeType : Name} {identity : Nat} :
    objectTypeNameBool schema runtimeType = true ->
      Execution.doesFragmentTypeApplyBool schema runtimeType
        (.object runtimeType identity) runtimeType = true := by
  intro hobject
  simp [Execution.doesFragmentTypeApplyBool, Execution.runtimeObjectType?,
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject]

theorem doesFragmentTypeApplyBool_object_other_false
    (schema : Schema) {runtimeType objectType : Name} {identity : Nat} :
    objectTypeNameBool schema objectType = true ->
      objectType ≠ runtimeType ->
        Execution.doesFragmentTypeApplyBool schema runtimeType
          (.object runtimeType identity) objectType = false := by
  intro hobject hne
  unfold Execution.doesFragmentTypeApplyBool
  cases hinclude :
      schema.typeIncludesObjectBool objectType runtimeType
  · simp [Execution.runtimeObjectType?, hinclude]
  · have heq :
        runtimeType = objectType :=
      typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
        hinclude
    exact False.elim (hne heq.symm)

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_noOverlap_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    (∃ runtimeType identity,
      source = .object runtimeType identity
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
      schema.typesOverlapBool parentType typeCondition = false ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType rest)
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source rest ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
  intro hsource hoverlap hrest
  have happly :
      Execution.doesFragmentTypeApplyBool schema parentType source
        typeCondition = false :=
    doesFragmentTypeApplyBool_false_of_typesOverlapBool_false_of_source
      schema hsource hoverlap
  simp [normalizeSelectionSet, hoverlap]
  rw [hrest]
  exact (executeSelectionSet_inlineFragment_some_directiveFree_skip schema
    resolvers variableValues depth parentType typeCondition source
    selectionSet rest happly).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_none_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (normalizeSelectionSet schema parentType (selectionSet ++ rest))
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source (selectionSet ++ rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (normalizeSelectionSet schema parentType
          (Selection.inlineFragment none [] selectionSet :: rest))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment none [] selectionSet :: rest) := by
  intro happend
  simp [normalizeSelectionSet]
  rw [happend]
  exact (executeSelectionSet_inlineFragment_none_directiveFree_flatten schema
    resolvers variableValues depth parentType source selectionSet rest).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_apply_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    schema.typesOverlapBool parentType typeCondition = true ->
      Execution.doesFragmentTypeApplyBool schema parentType source
        typeCondition = true ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType (selectionSet ++ rest))
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source (selectionSet ++ rest) ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
  intro hoverlap happly happend
  simp [normalizeSelectionSet, hoverlap]
  rw [happend]
  exact (executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
    schema resolvers variableValues depth parentType typeCondition source
    selectionSet rest happly).symm

theorem normalizeSelectionSet_executeSelectionSet_inlineFragment_some_overlap_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.Value)
    (selectionSet rest : List Selection) :
    objectTypeNameBool schema parentType = true ->
      (∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
        schema.typesOverlapBool parentType typeCondition = true ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType (selectionSet ++ rest))
            =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source (selectionSet ++ rest) ->
            Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (normalizeSelectionSet schema parentType
                (Selection.inlineFragment (some typeCondition) [] selectionSet
                  :: rest))
              =
            Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest) := by
  intro hobject hsource hoverlap happend
  exact normalizeSelectionSet_executeSelectionSet_inlineFragment_some_apply_case
    schema resolvers variableValues depth parentType typeCondition source
    selectionSet rest hoverlap
    (doesFragmentTypeApplyBool_true_of_typesOverlapBool_true_of_object_source
      schema hobject hsource hoverlap)
    happend

theorem collectFields_possibleTypeFragments_not_mem_eq_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (identity : Nat)
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
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (identity : Nat)
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
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (identity : Nat)
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
    (schema : Schema) (resolvers : Execution.Resolvers)
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

theorem normalizeSelectionSet_executeSelectionSet_field_lookup_none_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition)
    (depth : Nat) (parentType responseName fieldName : Name)
    (arguments : List Argument) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] selectionSet
        :: rest) ->
      schema.lookupField parentType fieldName = none ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest))
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (Selection.field responseName fieldName arguments []
            selectionSet :: rest) := by
  intro hvalid hlookup
  exact False.elim
    (Validation.selectionSetValid_field_head_lookup_none_false
      hvalid hlookup)

theorem normalizeSelectionSet_executeSelectionSet_field_lookup_none_lookupValid_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType responseName fieldName : Name)
    (arguments : List Argument) (source : Execution.Value)
    (selectionSet rest : List Selection) :
    selectionSetLookupValid schema parentType
      (Selection.field responseName fieldName arguments [] selectionSet
        :: rest) ->
      schema.lookupField parentType fieldName = none ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType
            (Selection.field responseName fieldName arguments []
              selectionSet :: rest))
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (Selection.field responseName fieldName arguments []
            selectionSet :: rest) := by
  intro hvalid hlookup
  exact False.elim
    (selectionSetLookupValid_field_head_lookup_none_false hvalid hlookup)

theorem executeField_singleton_eq_group_of_completeValue
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value) (responseName : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField)
    (normalizedSelectionSet : List Selection) :
    let resolved :=
      resolvers.resolve field.parentType field.fieldName field.arguments
        source
    let childType :=
      (schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName
    Execution.completeValue schema resolvers variableValues depth childType
      normalizedSelectionSet resolved
      =
    Execution.completeValue schema resolvers variableValues depth childType
      (Execution.mergedFieldSelectionSet (field :: fields)) resolved ->
      Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName
        [{ field with selectionSet := normalizedSelectionSet }]
        =
      Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName (field :: fields) := by
  intro resolved childType hcomplete
  simp [Execution.executeField, resolved, childType,
    Execution.mergedFieldSelectionSet, hcomplete]

theorem completeValue_list_eq_of_forall
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (values : List Execution.Value) :
    (∀ value, value ∈ values ->
      Execution.completeValue schema resolvers variableValues depth parentType
        leftSelectionSet value
        =
      Execution.completeValue schema resolvers variableValues depth parentType
        rightSelectionSet value) ->
      Execution.completeValue schema resolvers variableValues (depth + 1)
        parentType leftSelectionSet (.list values)
        =
      Execution.completeValue schema resolvers variableValues (depth + 1)
        parentType rightSelectionSet (.list values) := by
  intro hvalues
  simp [Execution.completeValue]
  intro value hvalue
  exact hvalues value hvalue

theorem completeValue_eq_of_child_object_lt
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) :
    ∀ depth parentType leftSelectionSet rightSelectionSet value,
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            leftSelectionSet
            =
          Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            rightSelectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          parentType leftSelectionSet value
          =
        Execution.completeValue schema resolvers variableValues depth
          parentType rightSelectionSet value
  | 0, _parentType, _leftSelectionSet, _rightSelectionSet, _value,
      _hobject => by
      simp [Execution.completeValue]
  | depth + 1, parentType, leftSelectionSet, rightSelectionSet, value,
      hobject => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType identity =>
          by_cases hinclude :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · simp [Execution.completeValue, hinclude]
            exact hobject depth runtimeType identity (Nat.lt_succ_self depth)
          · have hfalse :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool parentType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
      | list values =>
          exact completeValue_list_eq_of_forall schema resolvers
            variableValues depth parentType leftSelectionSet
            rightSelectionSet values
            (by
              intro element helement
              exact completeValue_eq_of_child_object_lt schema resolvers
                variableValues depth parentType leftSelectionSet
                rightSelectionSet element
                (by
                  intro childDepth runtimeType identity hlt
                  exact hobject childDepth runtimeType identity
                    (Nat.lt_trans hlt (Nat.lt_succ_self depth))))

theorem completeValue_eq_of_child_object_lt_includes
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) :
    ∀ depth parentType leftSelectionSet rightSelectionSet value,
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          schema.typeIncludesObjectBool parentType runtimeType = true ->
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              leftSelectionSet
              =
            Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              rightSelectionSet) ->
        Execution.completeValue schema resolvers variableValues depth
          parentType leftSelectionSet value
          =
        Execution.completeValue schema resolvers variableValues depth
          parentType rightSelectionSet value
  | 0, _parentType, _leftSelectionSet, _rightSelectionSet, _value,
      _hobject => by
      simp [Execution.completeValue]
  | depth + 1, parentType, leftSelectionSet, rightSelectionSet, value,
      hobject => by
      cases value with
      | null =>
          simp [Execution.completeValue]
      | scalar value =>
          simp [Execution.completeValue]
      | object runtimeType identity =>
          by_cases hinclude :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · simp [Execution.completeValue, hinclude]
            exact hobject depth runtimeType identity (Nat.lt_succ_self depth)
              hinclude
          · have hfalse :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool parentType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
      | list values =>
          exact completeValue_list_eq_of_forall schema resolvers
            variableValues depth parentType leftSelectionSet
            rightSelectionSet values
            (by
              intro element helement
              exact completeValue_eq_of_child_object_lt_includes schema
                resolvers variableValues depth parentType leftSelectionSet
                rightSelectionSet element
                (by
                  intro childDepth runtimeType identity hlt hinclude
                  exact hobject childDepth runtimeType identity
                    (Nat.lt_trans hlt (Nat.lt_succ_self depth)) hinclude))

theorem executeField_singleton_eq_group_of_child_object_lt
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value) (responseName : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField)
    (normalizedSelectionSet : List Selection) :
    (∀ childDepth runtimeType identity,
      childDepth < depth ->
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          normalizedSelectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          (Execution.mergedFieldSelectionSet (field :: fields))) ->
      Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName
        [{ field with selectionSet := normalizedSelectionSet }]
        =
      Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName (field :: fields) := by
  intro hcomplete
  apply executeField_singleton_eq_group_of_completeValue
    schema resolvers variableValues depth source responseName field fields
    normalizedSelectionSet
  exact completeValue_eq_of_child_object_lt schema resolvers variableValues
    depth
    ((schema.fieldReturnType? field.parentType field.fieldName).getD
      field.fieldName)
    normalizedSelectionSet
    (Execution.mergedFieldSelectionSet (field :: fields))
    (resolvers.resolve field.parentType field.fieldName field.arguments
      source)
    hcomplete

theorem executeCollectedFields_cons_eq_of_parts
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value)
    (normalizedGroup sourceGroup :
      Name × List Execution.ExecutableField)
    (normalizedRest sourceRest :
      List (Name × List Execution.ExecutableField)) :
    Execution.executeField schema resolvers variableValues depth source
      normalizedGroup.fst normalizedGroup.snd
      =
    Execution.executeField schema resolvers variableValues depth source
      sourceGroup.fst sourceGroup.snd ->
    Execution.executeCollectedFields schema resolvers variableValues depth
      source normalizedRest
      =
    Execution.executeCollectedFields schema resolvers variableValues depth
      source sourceRest ->
    Execution.executeCollectedFields schema resolvers variableValues depth
      source (normalizedGroup :: normalizedRest)
      =
    Execution.executeCollectedFields schema resolvers variableValues depth
      source (sourceGroup :: sourceRest) := by
  intro hhead htail
  cases normalizedGroup with
  | mk normalizedResponseName normalizedFields =>
      cases sourceGroup with
      | mk sourceResponseName sourceFields =>
          simp [Execution.executeCollectedFields]
          rw [hhead, htail]

theorem executeCollectedFields_zero
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) (source : Execution.Value) :
    ∀ groups,
      Execution.executeCollectedFields schema resolvers variableValues 0 source
        groups
        = []
  | [] => by
      simp [Execution.executeCollectedFields]
  | (_responseName, fields) :: rest => by
      cases fields <;>
        simp [Execution.executeCollectedFields, Execution.executeField,
          executeCollectedFields_zero schema resolvers variableValues source
            rest]

theorem executeSelectionSet_field_head_eq_of_completeValue
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections normalizedSubselections normalizedRest rest :
      List Selection)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField)) :
    let sourceField : Execution.ExecutableField :=
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
    let childType :=
      (schema.fieldReturnType? sourceField.parentType
        sourceField.fieldName).getD sourceField.fieldName
    let resolved :=
      resolvers.resolve sourceField.parentType sourceField.fieldName
        sourceField.arguments source
    responseName ∉
      (Execution.collectFields schema variableValues parentType source
        normalizedRest).map Prod.fst ->
    Execution.collectFields schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      =
    (responseName, sourceField :: sourceFields) :: sourceRest ->
    Execution.completeValue schema resolvers variableValues (depth - 1)
      childType normalizedSubselections resolved
      =
    Execution.completeValue schema resolvers variableValues (depth - 1)
      childType (Execution.mergedFieldSelectionSet
        (sourceField :: sourceFields)) resolved ->
    Execution.executeCollectedFields schema resolvers variableValues depth
      source
      (Execution.collectFields schema variableValues parentType source
        normalizedRest)
      =
    Execution.executeCollectedFields schema resolvers variableValues depth
      source sourceRest ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.field responseName fieldName arguments []
          normalizedSubselections :: normalizedRest)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
  intro sourceField childType resolved hnotin hsourceCollect
    hcomplete htail
  cases depth with
  | zero =>
      simp [Execution.executeSelectionSet,
        executeCollectedFields_zero schema resolvers variableValues source]
  | succ fieldDepth =>
      let normalizedField : Execution.ExecutableField :=
        { sourceField with selectionSet := normalizedSubselections }
      have hnormalizedCollect :
          Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments []
              normalizedSubselections :: normalizedRest)
          =
          (responseName, [normalizedField])
            :: Execution.collectFields schema variableValues parentType source
              normalizedRest := by
        simpa [sourceField, normalizedField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType source responseName fieldName
            arguments normalizedSubselections normalizedRest hnotin
      have hhead :
          Execution.executeField schema resolvers variableValues
            (fieldDepth + 1) source responseName [normalizedField]
          =
          Execution.executeField schema resolvers variableValues
            (fieldDepth + 1) source responseName
            (sourceField :: sourceFields) := by
        simpa [sourceField, normalizedField, childType, resolved] using
          executeField_singleton_eq_group_of_completeValue
            schema resolvers variableValues fieldDepth source responseName
            sourceField sourceFields normalizedSubselections hcomplete
      simp [Execution.executeSelectionSet, hnormalizedCollect,
        hsourceCollect]
      exact executeCollectedFields_cons_eq_of_parts schema resolvers
        variableValues (fieldDepth + 1) source
        (responseName, [normalizedField])
        (responseName, sourceField :: sourceFields)
        (Execution.collectFields schema variableValues parentType source
          normalizedRest)
        sourceRest hhead htail

theorem normalizeSelectionSet_executeSelectionSet_field_head_of_completeValue
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest normalizedSubselections : List Selection)
    (fieldDefinition : FieldDefinition)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField)) :
    let sourceField : Execution.ExecutableField :=
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
    let matching :=
      validFieldsWithResponseName schema parentType responseName rest
    let mergedSubselections :=
      subselections ++ mergeSelectionSets matching
    let returnType := fieldDefinition.outputType.namedType
    let normalizedRest :=
      normalizeSelectionSet schema parentType
        (withoutFieldsWithResponseName schema responseName rest)
    let computedSubselections :=
      if objectTypeNameBool schema returnType then
        normalizeSelectionSet schema returnType mergedSubselections
      else
        (schema.getPossibleTypes returnType).map
          (fun objectType =>
            Selection.inlineFragment (some objectType) []
              (normalizeSelectionSet schema objectType mergedSubselections))
    schema.lookupField parentType fieldName = some fieldDefinition ->
    normalizedSubselections = computedSubselections ->
    responseName ∉
      (Execution.collectFields schema variableValues parentType source
        normalizedRest).map Prod.fst ->
    Execution.collectFields schema variableValues parentType source
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      =
    (responseName, sourceField :: sourceFields) :: sourceRest ->
    Execution.completeValue schema resolvers variableValues (depth - 1)
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      normalizedSubselections
      (resolvers.resolve parentType fieldName arguments source)
      =
    Execution.completeValue schema resolvers variableValues (depth - 1)
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      (Execution.mergedFieldSelectionSet (sourceField :: sourceFields))
      (resolvers.resolve parentType fieldName arguments source) ->
    Execution.executeCollectedFields schema resolvers variableValues depth
      source
      (Execution.collectFields schema variableValues parentType source
        normalizedRest)
      =
    Execution.executeCollectedFields schema resolvers variableValues depth
      source sourceRest ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (normalizeSelectionSet schema parentType
          (Selection.field responseName fieldName arguments [] subselections
            :: rest))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
  intro sourceField matching mergedSubselections returnType normalizedRest
    computedSubselections hlookup hsubsections hnotin hsourceCollect
    hcomplete htail
  have hnormalized :
      normalizeSelectionSet schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest)
      =
      Selection.field responseName fieldName arguments [] normalizedSubselections
        :: normalizedRest := by
    simp [normalizeSelectionSet, hlookup, matching, mergedSubselections,
      returnType, normalizedRest, computedSubselections, hsubsections]
  rw [hnormalized]
  exact executeSelectionSet_field_head_eq_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments subselections normalizedSubselections normalizedRest
    rest sourceFields sourceRest hnotin hsourceCollect
    (by simpa [sourceField] using hcomplete)
    htail

theorem normalizeSelectionSet_executeSelectionSet_field_head_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest normalizedSubselections : List Selection)
    (fieldDefinition : FieldDefinition) :
    objectTypeNameBool schema parentType = true ->
      (∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
        selectionSetDirectiveFree
          (Selection.field responseName fieldName arguments [] subselections
            :: rest) ->
        schema.lookupField parentType fieldName = some fieldDefinition ->
        normalizedSubselections =
          (let matching :=
            validFieldsWithResponseName schema parentType responseName rest
          let mergedSubselections :=
            subselections ++ mergeSelectionSets matching
          let returnType := fieldDefinition.outputType.namedType
          if objectTypeNameBool schema returnType then
            normalizeSelectionSet schema returnType mergedSubselections
          else
            (schema.getPossibleTypes returnType).map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (normalizeSelectionSet schema objectType
                    mergedSubselections))) ->
        (∀ childDepth runtimeType identity,
          childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? parentType fieldName).getD fieldName)
              runtimeType = true ->
              Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                normalizedSubselections
                =
              Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (subselections
                  ++ mergeSelectionSets
                    (validFieldsWithResponseName schema parentType responseName
                      rest))) ->
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (normalizeSelectionSet schema parentType
            (withoutFieldsWithResponseName schema responseName rest))
          =
        Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (withoutFieldsWithResponseName schema responseName rest) ->
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.field responseName fieldName arguments []
                subselections :: rest))
          =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.field responseName fieldName arguments []
              subselections :: rest) := by
  intro hobject hsource hfree hlookup hsubsections hchild htail
  rcases collectFields_field_head_exists schema variableValues parentType
      source responseName fieldName arguments subselections rest with
    ⟨sourceFields, sourceRest, hsourceCollect⟩
  let sourceField : Execution.ExecutableField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      selectionSet := subselections
    }
  let normalizedRest :=
    normalizeSelectionSet schema parentType
      (withoutFieldsWithResponseName schema responseName rest)
  have hnotin :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source
          normalizedRest).map Prod.fst := by
    unfold normalizedRest
    exact collectFields_responseName_not_mem_of_responseNameFree schema
      variableValues parentType source responseName hobject hsource
      (normalizeSelectionSet schema parentType
        (withoutFieldsWithResponseName schema responseName rest))
      (normalizeSelectionSet_directiveFree schema parentType
        (withoutFieldsWithResponseName schema responseName rest)
        (withoutFieldsWithResponseName_directiveFree schema responseName rest
          (selectionSetDirectiveFree_tail hfree)))
      (normalizeSelectionSet_responseNameFree schema parentType responseName
        (withoutFieldsWithResponseName schema responseName rest)
        (withoutFieldsWithResponseName_responseNameFree schema parentType
          responseName rest))
  have hsourceRest :
      Execution.collectFields schema variableValues parentType source
        (withoutFieldsWithResponseName schema responseName rest)
      =
      sourceRest := by
    exact collectFields_withoutFieldsWithResponseName_fieldHead_rest_eq_sourceRest
      schema variableValues parentType source responseName fieldName arguments
      subselections rest sourceFields sourceRest hobject hsource hfree
      (by simpa [sourceField] using hsourceCollect)
  have htailCollected :
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues parentType source
          normalizedRest)
      =
      Execution.executeCollectedFields schema resolvers variableValues depth
        source sourceRest := by
    simpa [Execution.executeSelectionSet, normalizedRest, hsourceRest]
      using htail
  apply normalizeSelectionSet_executeSelectionSet_field_head_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments subselections rest normalizedSubselections
    fieldDefinition sourceFields sourceRest
  · exact hlookup
  · exact hsubsections
  · exact hnotin
  · simpa [sourceField] using hsourceCollect
  · apply completeValue_eq_of_child_object_lt_includes schema resolvers
      variableValues
      (depth - 1)
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
      normalizedSubselections
      (Execution.mergedFieldSelectionSet (sourceField :: sourceFields))
      (resolvers.resolve parentType fieldName arguments source)
    intro childDepth runtimeType identity hlt hinclude
    have hmerged :
        Execution.mergedFieldSelectionSet (sourceField :: sourceFields)
          =
        subselections
          ++ mergeSelectionSets
            (validFieldsWithResponseName schema parentType responseName rest) := by
      have hprojection :=
        collectFields_validFieldsWithResponseName_responseSelection schema
          variableValues parentType source responseName
          (Selection.field responseName fieldName arguments [] subselections
            :: rest)
          hobject hsource hfree
      simp [collectedResponseSelectionSet, hsourceCollect,
        validFieldsWithResponseName, mergeSelectionSets,
        Selection.subselections] at hprojection
      simpa [sourceField] using hprojection
    rw [hmerged]
    exact hchild childDepth runtimeType identity (Nat.lt_of_lt_of_le hlt
      (Nat.sub_le depth 1)) hinclude
  · exact htailCollected

theorem normalizeSelectionSet_executeSelectionSet_field_head_case_of_recursive
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (parentType : Name) (source : Execution.Value)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) :
    objectTypeNameBool schema parentType = true ->
      (∃ runtimeType identity,
        source = .object runtimeType identity
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
    selectionSetDirectiveFree
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    Validation.selectionSetValid schema variableDefinitions parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    selectionSetSemanticsReady schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections
        :: rest) ->
    schema.lookupField parentType fieldName = some fieldDefinition ->
    (let mergedSubselections :=
      subselections
        ++ mergeSelectionSets
          (validFieldsWithResponseName schema parentType responseName rest)
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
        selectionSetDirectiveFree mergedSubselections ->
        selectionSetLookupValid schema runtimeType mergedSubselections ->
        selectionSetSemanticsReady schema runtimeType mergedSubselections ->
        FieldMerge.fieldsInSetCanMerge schema runtimeType mergedSubselections ->
          Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (normalizeSelectionSet schema runtimeType mergedSubselections)
          =
          Execution.executeSelectionSet schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            mergedSubselections) ->
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (normalizeSelectionSet schema parentType
        (withoutFieldsWithResponseName schema responseName rest))
      =
    Execution.executeSelectionSet schema resolvers variableValues depth
      parentType source
      (withoutFieldsWithResponseName schema responseName rest) ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (normalizeSelectionSet schema parentType
          (Selection.field responseName fieldName arguments []
            subselections :: rest))
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.field responseName fieldName arguments []
          subselections :: rest) := by
  intro hobject hsource hfree hvalid hready hmerge hlookup hrecursive htail
  let matching := validFieldsWithResponseName schema parentType responseName rest
  let mergedSubselections := subselections ++ mergeSelectionSets matching
  let returnType := fieldDefinition.outputType.namedType
  have hparentObject :
      schema.objectType parentType :=
    objectType_of_objectTypeNameBool_eq_true schema hobject
  have hmergedFree :
      selectionSetDirectiveFree mergedSubselections := by
    simpa [mergedSubselections, matching] using
      selectionSetDirectiveFree_fieldHead_merged schema parentType responseName
        fieldName arguments subselections rest hfree
  have hreturnEq :
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        =
      returnType := by
    simp [Schema.fieldReturnType?, hlookup, returnType]
  have hlookupValid :
      selectionSetLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) :=
    selectionSetLookupValid_of_selectionSetValid
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hvalid
  apply normalizeSelectionSet_executeSelectionSet_field_head_case
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments subselections rest
    (if objectTypeNameBool schema returnType then
      normalizeSelectionSet schema returnType mergedSubselections
    else
      (schema.getPossibleTypes returnType).map
        (fun objectType =>
          Selection.inlineFragment (some objectType) []
            (normalizeSelectionSet schema objectType mergedSubselections)))
    fieldDefinition
  · exact hobject
  · exact hsource
  · exact hfree
  · exact hlookup
  · simp [matching, mergedSubselections, returnType]
  · intro childDepth runtimeType identity hlt hinclude
    have hincludeReturn :
        schema.typeIncludesObjectBool returnType runtimeType = true := by
      simpa [hreturnEq] using hinclude
    have hmergedLookup :
        selectionSetLookupValid schema runtimeType mergedSubselections := by
      simpa [mergedSubselections, matching] using
        selectionSetLookupValid_fieldHead_merged_of_child_object schema
          variableDefinitions parentType responseName fieldName runtimeType
          arguments subselections rest fieldDefinition hschema hparentObject
          hvalid hmerge hlookup hincludeReturn
    have hmergedReady :
        selectionSetSemanticsReady schema runtimeType mergedSubselections := by
      simpa [mergedSubselections, matching] using
        selectionSetSemanticsReady_fieldHead_merged_of_child_object schema
          parentType responseName fieldName runtimeType arguments
          subselections rest fieldDefinition hparentObject hready
          hlookupValid hmerge hlookup hincludeReturn
    have hmergedCanMerge :
        FieldMerge.fieldsInSetCanMerge schema runtimeType
          mergedSubselections := by
      simpa [mergedSubselections, matching] using
        fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object schema
          variableDefinitions parentType responseName fieldName runtimeType
          arguments subselections rest fieldDefinition hparentObject hvalid
          hmerge hlookup
    by_cases hreturnObject : objectTypeNameBool schema returnType = true
    · have hruntimeEq : runtimeType = returnType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hreturnObject hincludeReturn
      subst runtimeType
      simp [hreturnObject]
      exact hrecursive childDepth returnType identity hlt hmergedFree
        hmergedLookup hmergedReady hmergedCanMerge
    · have hreturnObjectFalse :
          objectTypeNameBool schema returnType = false := by
        cases hmatch : objectTypeNameBool schema returnType
        · rfl
        · contradiction
      have hpossible :
          runtimeType ∈ schema.getPossibleTypes returnType :=
        List.contains_iff_mem.mp hincludeReturn
      have hobjects :
          ∀ objectType, objectType ∈ schema.getPossibleTypes returnType ->
            objectTypeNameBool schema objectType = true := by
        intro objectType hobjectType
        exact objectTypeNameBool_eq_true_of_objectType schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema returnType objectType hobjectType)
      simp [hreturnObjectFalse]
      exact executeSelectionSet_possibleTypeFragments_runtime_branch schema
        resolvers variableValues childDepth runtimeType identity
        (schema.getPossibleTypes returnType) mergedSubselections hobjects
        (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
          returnType)
        hpossible
        (hrecursive childDepth runtimeType identity hlt hmergedFree
          hmergedLookup hmergedReady hmergedCanMerge)
  · exact htail

theorem normalizeOperation_executeQuery
    (schema : Schema) (operation : Operation) :
    (∀ resolvers variableValues source,
      Execution.rootSourceAppliesBool schema operation source = true ->
        Execution.executeSelectionSet schema resolvers variableValues
          (Execution.executeQueryDepthBound operation)
          operation.rootType source operation.selectionSet
          =
        Execution.executeSelectionSet schema resolvers variableValues
          (Execution.executeQueryDepthBound
            (normalizeOperation schema operation))
          operation.rootType source
          (normalizeOperation schema operation).selectionSet) ->
      groundTypeNormalFormSemanticsPreserved schema operation := by
  exact groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet schema
    operation

theorem groundTypeNormalFormSemanticsPreservation_of_selectionSet
    (schema : Schema) (operation : Operation) :
    (SchemaWellFormedness.schemaWellFormed schema ->
      Validation.operationDefinitionValid schema operation ->
        operationDirectiveFree operation ->
          ∀ resolvers variableValues source,
            Execution.rootSourceAppliesBool schema operation source = true ->
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound operation)
                operation.rootType source operation.selectionSet
                =
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound
                  (normalizeOperation schema operation))
                operation.rootType source
                (normalizeOperation schema operation).selectionSet) ->
      NormalForm.groundTypeNormalFormSemanticsPreservation schema operation := by
  intro hselection hschema hvalid hfree
  exact normalizeOperation_executeQuery schema operation
    (hselection hschema hvalid hfree)

theorem groundNormalFormCorrect_of_selectionSet
    (schema : Schema) (operation : Operation) :
    (SchemaWellFormedness.schemaWellFormed schema ->
      Validation.operationDefinitionValid schema operation ->
        operationDirectiveFree operation ->
          ∀ resolvers variableValues source,
            Execution.rootSourceAppliesBool schema operation source = true ->
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound operation)
                operation.rootType source operation.selectionSet
                =
              Execution.executeSelectionSet schema resolvers variableValues
                (Execution.executeQueryDepthBound
                  (normalizeOperation schema operation))
                operation.rootType source
                (normalizeOperation schema operation).selectionSet) ->
      SchemaWellFormedness.schemaWellFormed schema ->
        Validation.operationDefinitionValid schema operation ->
          operationDirectiveFree operation ->
            NormalForm.groundNormalFormCorrect schema operation := by
  intro hselection hschema hvalid hfree
  exact groundNormalFormCorrect_of_semanticsPreservation schema operation
    (groundTypeNormalFormSemanticsPreservation_of_selectionSet schema operation
      hselection)
    hschema hvalid hfree

end GroundTypeNormalization

end NormalForm

end GraphQL
