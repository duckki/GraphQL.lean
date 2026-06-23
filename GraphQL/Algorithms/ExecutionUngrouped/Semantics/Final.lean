import GraphQL.Algorithms.ExecutionUngrouped.Semantics.GeneratedFields

/-!
Final semantic-preservation theorems for ungrouped execution.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

variable {ObjectRef : Type}

theorem collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_responseNamesNodup
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
      CollectedSelectionSetGroupsSingleton schema variableValues parentType
        source selectionSet := by
  intro hall hfree hnodup responseName fields hgroup
  have hnonempty :=
    collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  cases fields with
  | nil =>
      exact False.elim (hnonempty responseName [] hgroup rfl)
  | cons field fieldsTail =>
      have htail : fieldsTail = [] :=
        (FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
            schema variableValues parentType source selectionSet hall hfree hnodup
            hgroup
            (prefixTail := ([] : List Execution.ExecutableField))
            (by
              intro candidate hmem
              simp at hmem)).1
      subst fieldsTail
      simp

theorem collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_normal
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetNormal schema selectionSet ->
      CollectedSelectionSetGroupsSingleton schema variableValues parentType
        source selectionSet := by
  intro hall hfree hnormal
  have hnonRedundant : NormalForm.selectionSetNonRedundant selectionSet :=
    hnormal.2
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant
  rcases hnonRedundant with ⟨hnodup, _hfragmentNodup, _hchildren⟩
  exact
    collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_responseNamesNodup
      schema variableValues parentType source selectionSet hall hfree
      hnodup

theorem collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
        (Execution.ResolverValue.object childRuntime ref) childSelectionSet := by
  intro hschema hinclude hgenerated responseName fields hgroup
  have hnonempty :=
    collectFields_fieldsNonempty schema variableValues childRuntime
      (Execution.ResolverValue.object childRuntime ref) childSelectionSet
  cases fields with
  | nil =>
      exact False.elim (hnonempty responseName [] hgroup rfl)
  | cons field fieldsTail =>
      have htail : fieldsTail = [] :=
        (collectFields_generatedNormalizedFieldChild_prefix_empty schema
          variableValues childType childRuntime ref childSelectionSet hschema
          hinclude hgenerated hgroup
          (prefixTail := ([] : List Execution.ExecutableField))
            (by
              intro candidate hmem
              simp at hmem)).1
      subst fieldsTail
      simp

theorem executionSelectionSetLookupValid_normalizeSelectionSet
    (schema : Schema) :
    ∀ parentType selectionSet,
      executionSelectionSetLookupValid schema parentType
        (NormalForm.normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using
    NormalForm.normalizeSelectionSet.induct schema with
  | case1 parentType =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      simp [NormalForm.normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have hrestLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType
                  (NormalForm.withoutFieldsWithResponseName schema responseName rest) ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using hrest
      exact
        hrestLookup selection
          (by simpa [NormalForm.normalizeSelectionSet, hlookup] using hmem)
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      simp [NormalForm.normalizeSelectionSet, hlookup,
        NormalForm.normalizedField] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponse, hfield, harguments, hdirectives,
          hchild⟩
        unfold executionSelectionLookupValid
        exact ⟨fieldDefinition, hlookup⟩
      · have hrestLookup :
            ∀ selection,
              selection ∈
                  NormalForm.normalizeSelectionSet schema parentType
                    (NormalForm.withoutFieldsWithResponseName schema responseName rest) ->
                executionSelectionLookupValid schema parentType selection := by
          simpa [executionSelectionSetLookupValid] using hrest
        exact hrestLookup selection htail
  | case4 parentType rest directives selectionSet happend =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have happendLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType
                  (selectionSet ++ rest) ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using happend
      exact
        happendLookup selection
          (by simpa [NormalForm.normalizeSelectionSet] using hmem)
  | case5 parentType rest typeCondition directives selectionSet hoverlap hrest
      happend =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have happendLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType
                  (selectionSet ++ rest) ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using happend
      exact
        happendLookup selection
          (by simpa [NormalForm.normalizeSelectionSet, hoverlap] using hmem)
  | case6 parentType rest typeCondition directives selectionSet hoverlap hrest =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      have hrestLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType rest ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using hrest
      exact
        hrestLookup selection
          (by simpa [NormalForm.normalizeSelectionSet, hfalse] using hmem)

theorem collectedGroupsFieldLookupValid_of_generatedNormalizedFieldChild
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      CollectedGroupsFieldLookupValid schema childRuntime
        (GraphQL.Execution.collectFields schema variableValues childRuntime
          (Execution.ResolverValue.object childRuntime ref)
          childSelectionSet) := by
  intro hschema hinclude hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, _hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType
            sourceSelectionSet := by
      simpa [hobject] using hchild
    simpa [hchildEq] using
      collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
        schema variableValues childType (Execution.ResolverValue.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (executionSelectionSetLookupValid_normalizeSelectionSet schema
          childType sourceSelectionSet)
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    have hpossibleMem : childRuntime ∈ schema.getPossibleTypes childType :=
      List.contains_iff_mem.mp hinclude
    have hobjects :
        ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
          NormalForm.objectTypeNameBool schema objectType = true := by
      intro objectType hobjectType
      exact
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
          schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema childType objectType hobjectType)
    have hpossibleNodup :
        (schema.getPossibleTypes childType).Nodup :=
      SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType
    have hcollect :
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    rw [hchildEq, hcollect]
    exact
      collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
        schema variableValues childRuntime
        (Execution.ResolverValue.object childRuntime ref)
        (NormalForm.normalizeSelectionSet schema childRuntime sourceSelectionSet)
        (executionSelectionSetLookupValid_normalizeSelectionSet schema
          childRuntime sourceSelectionSet)

theorem executeRootSelectionSet_eq_spec_of_allFieldsNormal
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (childReady : Name -> List Selection -> Prop)
    (hchild :
      ∀ childDepth childType runtimeType (ref : ObjectRef) childSelectionSet,
        childDepth < depth ->
        schema.typeIncludesObjectBool childType runtimeType = true ->
        childReady childType childSelectionSet ->
        NormalForm.selectionSetNormal schema childSelectionSet ->
        NormalForm.selectionSetDirectiveFree childSelectionSet ->
            executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (Execution.ResolverValue.object runtimeType ref)
                childSelectionSet
              =
              Execution.executeRootSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.ResolverValue.object runtimeType ref)
                childSelectionSet) :
    NormalForm.selectionsAllFields selectionSet ->
      NormalForm.selectionSetDirectiveFree selectionSet ->
      NormalForm.selectionSetNormal schema selectionSet ->
      executionSelectionSetLookupValid schema parentType selectionSet ->
        (∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
        childReady
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            childSelectionSet) ->
        executeRootSelectionSet schema resolvers variableValues depth
            parentType source selectionSet
          =
        Execution.executeRootSelectionSet schema resolvers variableValues depth
          parentType source selectionSet := by
  intro hall hfree hnormal hlookup hchildren
  cases depth with
  | zero =>
      exact
        (ExecutedGroupedSelectionSetState.depth_zero schema resolvers
          variableValues parentType source selectionSet
          (collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_normal
            schema variableValues parentType source selectionSet hall hfree
            hnormal)).executeRootSelectionSet_eq_spec
  | succ completionDepth =>
      apply executeRootSelectionSet_eq_spec_of_collected_groups_collectedLocalAppendInvariant
        (hcollect := rfl)
        (hflat :=
          (VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_normal
            schema resolvers variableValues completionDepth parentType source
            selectionSet hall hfree hnormal).empty)
        (hcollected :=
          executionCollectedFieldInvariant_of_allFieldsNormal schema resolvers
            variableValues completionDepth parentType source selectionSet hall
            hfree hnormal)
          (hcompatible :=
            collectedGroupsFieldValidationMergeCompatible_of_allFieldsNormal
              schema variableValues parentType source selectionSet hall hfree
              hnormal)
          (hlookups :=
            collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
              schema variableValues parentType source selectionSet hlookup)
          (happend :=
          collectedFieldGroupLocalAppendInvariant_of_allFieldsNormal schema
            resolvers variableValues completionDepth parentType source
            selectionSet childReady
            (by
              intro childDepth childType runtimeType ref childSelectionSet hlt
                hinclude hready hchildNormal hchildFree
              exact hchild childDepth childType runtimeType ref
                childSelectionSet
                (by simpa [Nat.succ_eq_add_one] using hlt)
                hinclude hready hchildNormal hchildFree)
            hall hfree hnormal hchildren)

theorem executeQueryAtDepth_eq_spec_of_allFieldsNormal
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (childReady : Name -> List Selection -> Prop)
    (hchild :
      ∀ childDepth childType runtimeType (ref : ObjectRef) childSelectionSet,
        childDepth < depth ->
        schema.typeIncludesObjectBool childType runtimeType = true ->
        childReady childType childSelectionSet ->
        NormalForm.selectionSetNormal schema childSelectionSet ->
        NormalForm.selectionSetDirectiveFree childSelectionSet ->
            executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (Execution.ResolverValue.object runtimeType ref)
                childSelectionSet
              =
              Execution.executeRootSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.ResolverValue.object runtimeType ref)
                childSelectionSet) :
      NormalForm.selectionsAllFields operation.selectionSet ->
      NormalForm.operationDirectiveFree operation ->
      NormalForm.operationNormal schema operation ->
      executionSelectionSetLookupValid schema operation.rootType
        operation.selectionSet ->
      (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
        childReady
          ((schema.fieldReturnType? operation.rootType fieldName).getD
            fieldName)
          childSelectionSet) ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source := by
  intro hall hfree hnormal hlookup hchildren
  unfold executeQueryAtDepth Execution.executeQueryAtDepth
  by_cases hsource :
      Execution.rootSourceAppliesBool schema operation source = true
  · simp [hsource]
    rw [
      executeRootSelectionSet_eq_spec_of_allFieldsNormal schema resolvers
          variableValues depth operation.rootType source operation.selectionSet
          childReady hchild hall hfree hnormal hlookup hchildren]
    rfl
  · simp [hsource]

theorem collectedGroupsFieldValidationMergeCompatible_of_generatedNormalizedFieldChild
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues childRuntime
          (Execution.ResolverValue.object childRuntime ref) childSelectionSet) := by
  intro hschema hinclude hgenerated responseName fields hgroup
  have hnonempty :
      CollectedGroupsFieldsNonempty
        (GraphQL.Execution.collectFields schema variableValues childRuntime
          (Execution.ResolverValue.object childRuntime ref) childSelectionSet) :=
    collectFields_fieldsNonempty schema variableValues childRuntime
      (Execution.ResolverValue.object childRuntime ref) childSelectionSet
  cases fields with
  | nil =>
      exact False.elim (hnonempty responseName [] hgroup rfl)
  | cons field fieldsTail =>
      have htail : fieldsTail = [] :=
        (collectFields_generatedNormalizedFieldChild_prefix_empty schema
          variableValues childType childRuntime ref childSelectionSet hschema
          hinclude hgenerated hgroup
          (prefixTail := ([] : List Execution.ExecutableField))
          (show ∀ candidate : Execution.ExecutableField,
              candidate ∈ ([] : List Execution.ExecutableField) ->
                candidate ∈ fieldsTail from
            by
              intro candidate hmem
              simp at hmem)).1
      subst fieldsTail
      exact executableFieldsFieldValidationMergeCompatible_singleton field

theorem executionCollectedFieldInvariant_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := childRuntime
            source := Execution.ResolverValue.object childRuntime ref
            selectionSet := childSelectionSet }
          initial := .object [] } := by
  intro hschema hinclude hgenerated
  constructor
  · exact PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues childRuntime
        (Execution.ResolverValue.object childRuntime ref) childSelectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        childRuntime (Execution.ResolverValue.object childRuntime ref)
        childSelectionSet)
  · intro responseName fields hgroup
    have hnonempty :
        CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref)
            childSelectionSet) :=
      collectFields_fieldsNonempty schema variableValues childRuntime
        (Execution.ResolverValue.object childRuntime ref) childSelectionSet
    cases fields with
    | nil =>
        exact False.elim (hnonempty responseName [] hgroup rfl)
    | cons field fieldsTail =>
        have htail : fieldsTail = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime ref childSelectionSet hschema
            hinclude hgenerated hgroup
            (prefixTail := ([] : List Execution.ExecutableField))
            (show ∀ candidate : Execution.ExecutableField,
                candidate ∈ ([] : List Execution.ExecutableField) ->
                  candidate ∈ fieldsTail from
              by
                intro candidate hmem
                simp at hmem)).1
        subst fieldsTail
        exact executableFieldsResolveStable_singleton resolvers
          (Execution.ResolverValue.object childRuntime ref) field

def selectionSetLocalFreshPrefixInvariants_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      SelectionSetLocalFreshPrefixInvariants schema resolvers variableValues
        depth childRuntime (Execution.ResolverValue.object childRuntime ref)
        childSelectionSet := by
  intro hschema hinclude hgenerated
  exact
    SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
      (freshPrefixSelectionDerivation_generatedNormalizedFieldChild_runtime
        schema variableValues childType childRuntime ref childSelectionSet
        hschema hinclude hgenerated)
      (executionCollectedFieldInvariant_of_generatedNormalizedFieldChild
        schema resolvers variableValues depth childType childRuntime ref
        childSelectionSet hschema hinclude hgenerated)
      (collectedGroupsFieldValidationMergeCompatible_of_generatedNormalizedFieldChild
        schema variableValues childType childRuntime ref childSelectionSet hschema
        hinclude hgenerated)
      (collectedGroupsFieldLookupValid_of_generatedNormalizedFieldChild
        schema variableValues childType childRuntime ref childSelectionSet
        hschema hinclude hgenerated)
      (by
        intro responseName field fields prefixTail later hgroup hprefix hlater
          childDepth grandchildRuntime grandchildRef hlt
        have hprefixTail : prefixTail = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime ref childSelectionSet hschema
            hinclude hgenerated hgroup hprefix).2
        subst prefixTail
        have hfields : fields = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime ref childSelectionSet hschema
            hinclude hgenerated hgroup
            (prefixTail := ([] : List Execution.ExecutableField))
            (by
              intro candidate hmem
              simp at hmem)).1
        subst fields
        simp at hlater)

def recursiveGroupedSelectionSetState_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        childRuntime (Execution.ResolverValue.object childRuntime ref)
        childSelectionSet := by
  intro hschema hinclude hgenerated
  apply RecursiveGroupedSelectionSetState.of_localFreshPrefixInvariants
    (selectionSetLocalFreshPrefixInvariants_of_generatedNormalizedFieldChild
      schema resolvers variableValues depth childType childRuntime ref
      childSelectionSet hschema hinclude hgenerated)
  intro responseName field fields prefixTail hgroup hprefix childDepth
    grandchildRuntime grandchildRef hlt hgrandchildInclude
  have hgrandchildGenerated :
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet :=
    generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
      schema variableValues childType childRuntime ref childSelectionSet hschema
      hinclude hgenerated hgroup hprefix
  have hprefixTail : prefixTail = [] :=
    (collectFields_generatedNormalizedFieldChild_prefix_empty schema
      variableValues childType childRuntime ref childSelectionSet hschema
      hinclude hgenerated hgroup hprefix).2
  subst prefixTail
  simpa [GraphQL.Execution.mergedFieldSelectionSet] using
    recursiveGroupedSelectionSetState_of_generatedNormalizedFieldChild schema
      resolvers variableValues childDepth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      grandchildRuntime grandchildRef field.selectionSet hschema
      hgrandchildInclude hgrandchildGenerated
  · intro responseName field fields prefixTail hgroup hprefix
      grandchildRuntime grandchildRef _hlt hgrandchildInclude
    have hgrandchildGenerated :
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet :=
      generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
        schema variableValues childType childRuntime ref childSelectionSet hschema
        hinclude hgenerated hgroup hprefix
    have hprefixTail : prefixTail = [] :=
      (collectFields_generatedNormalizedFieldChild_prefix_empty schema
        variableValues childType childRuntime ref childSelectionSet hschema
        hinclude hgenerated hgroup hprefix).2
    subst prefixTail
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
        schema variableValues
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        grandchildRuntime grandchildRef field.selectionSet hschema
        hgrandchildInclude hgrandchildGenerated
termination_by depth
decreasing_by exact Nat.lt_of_succ_lt hlt

theorem executeRootSelectionSet_eq_spec_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      executeRootSelectionSet schema resolvers variableValues depth childRuntime
          (Execution.ResolverValue.object childRuntime ref) childSelectionSet
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        childRuntime (Execution.ResolverValue.object childRuntime ref)
        childSelectionSet := by
  intro hschema hinclude hgenerated
  cases depth with
  | zero =>
      exact
        (ExecutedGroupedSelectionSetState.depth_zero schema resolvers
          variableValues childRuntime
          (Execution.ResolverValue.object childRuntime ref)
          childSelectionSet
          (collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
            schema variableValues childType childRuntime ref childSelectionSet
            hschema hinclude hgenerated)).executeRootSelectionSet_eq_spec
  | succ completionDepth =>
      exact
        (recursiveGroupedSelectionSetState_of_generatedNormalizedFieldChild
          schema resolvers variableValues completionDepth childType childRuntime
          ref childSelectionSet hschema hinclude
          hgenerated).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_normalizeSelectionSet
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
      executeRootSelectionSet schema resolvers variableValues depth parentType
          source (NormalForm.normalizeSelectionSet schema parentType selectionSet)
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        parentType source
        (NormalForm.normalizeSelectionSet schema parentType selectionSet) := by
  intro hschema hfree
  apply executeRootSelectionSet_eq_spec_of_allFieldsNormal schema resolvers
    variableValues depth parentType source
    (NormalForm.normalizeSelectionSet schema parentType selectionSet)
    (generatedNormalizedFieldChild schema)
  · intro childDepth childType runtimeType ref childSelectionSet _hlt hinclude
      hgenerated _hchildNormal _hchildFree
    exact
      executeRootSelectionSet_eq_spec_of_generatedNormalizedFieldChild schema
        resolvers variableValues childDepth childType runtimeType ref
        childSelectionSet hschema hinclude hgenerated
  · exact
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType selectionSet
  · exact
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
        schema parentType selectionSet hfree
  · exact
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal schema
        hschema parentType selectionSet
  · exact
      executionSelectionSetLookupValid_normalizeSelectionSet schema parentType
        selectionSet
  · intro responseName fieldName arguments directives childSelectionSet hmem
    exact
      normalizeSelectionSet_field_child_generated schema parentType selectionSet
        responseName fieldName arguments directives childSelectionSet hfree hmem

theorem executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.objectTypeNameBool schema operation.rootType = true ->
    (∃ runtimeType ref,
      source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool operation.rootType runtimeType = true) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      NormalForm.selectionSetDirectiveFree
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      NormalForm.selectionSetSemanticsReady schema operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet)
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth
        source := by
  intro hschema hcomplete hobject hsource hfree hready hmerge hsourceSpec
  rcases hsource with ⟨runtimeType, ref, hsourceEq, hinclude⟩
  have hsourceObject :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool operation.rootType runtimeType =
            true :=
    ⟨runtimeType, ref, hsourceEq, hinclude⟩
  have hroot :
      Execution.rootSourceAppliesBool schema operation source = true := by
    simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
      hsourceEq, hinclude]
  have hrootComplete :
      Execution.rootSourceAppliesBool schema
          (NormalForm.completeNormalizeOperation schema operation) source =
        true := by
    simpa [NormalForm.CompleteNormalization.completeNormalizeOperation_rootSourceAppliesBool]
      using hroot
  rcases
      NormalForm.CompleteNormalization.operationBoolVarsComplete_caseForVariableValues
        variableValues operation hcomplete with
    ⟨runtimeCase, hruntime, hagrees⟩
  let filtered :=
    NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet
  let normalized :=
    NormalForm.normalizeSelectionSet schema operation.rootType filtered
  have hfilteredRoot :
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source filtered
        =
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet := by
    simpa [filtered] using
      executeRootSelectionSet_filterSelectionSetBoolCase_eq schema resolvers
        variableValues operation runtimeCase hagrees depth operation.rootType
        source operation.selectionSet
        (by
          intro varName hmem
          exact hmem)
  have hfilteredSpec :
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source filtered
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source filtered := by
    simpa [filtered] using hsourceSpec runtimeCase hruntime hagrees
  have hgroundSpec :
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source normalized
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source filtered := by
    simpa [Execution.executeSelectionSet, filtered, normalized] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_executeSelectionSet
        schema resolvers variableValues hschema depth operation.rootType source
        filtered hobject hsourceObject
        (hfree runtimeCase hruntime hagrees)
        (hready runtimeCase hruntime hagrees)
        (hmerge runtimeCase hruntime hagrees)
  have hnormalizedSpec :
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source normalized
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source normalized := by
    simpa [filtered, normalized] using
      executeRootSelectionSet_eq_spec_of_normalizeSelectionSet schema
        resolvers variableValues depth operation.rootType source filtered
        hschema (hfree runtimeCase hruntime hagrees)
  have hcompleteRoot :
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source normalized := by
    simpa [NormalForm.completeNormalizeOperation, filtered, normalized] using
      executeRootSelectionSet_completeNormalizeRootSelectionSet_runtime schema
        resolvers variableValues operation depth operation.rootType source
        runtimeCase operation.selectionSet hruntime hagrees
  have hrootResult :
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet
        =
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet :=
    hfilteredRoot.symm.trans
      (hfilteredSpec.trans
        (hgroundSpec.symm.trans
          (hnormalizedSpec.symm.trans hcompleteRoot.symm)))
  unfold executeQueryAtDepth
  rw [hroot]
  rw [hrootComplete]
  simp [hrootResult, NormalForm.completeNormalizeOperation]

theorem executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_recursiveGroupedStates
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.objectTypeNameBool schema operation.rootType = true ->
    (∃ runtimeType ref,
      source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool operation.rootType runtimeType = true) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      NormalForm.selectionSetDirectiveFree
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      NormalForm.selectionSetSemanticsReady schema operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)) ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source := by
  intro hschema hcomplete hobject hsource hfree hready hmerge hstates
  apply executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_source_eq_spec
    schema operation resolvers variableValues (depth + 1) source hschema
    hcomplete hobject hsource hfree hready hmerge
  intro runtimeCase hruntime hagrees
  exact (hstates runtimeCase hruntime hagrees).executeRootSelectionSet_eq_spec

theorem executeQueryAtDepth_eq_spec_of_generatedNormalOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
    executionSelectionSetLookupValid schema operation.rootType
      operation.selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? operation.rootType fieldName).getD
            fieldName)
          childSelectionSet) ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source := by
  intro hschema hall hfree hnormal hlookup hchildren
  apply executeQueryAtDepth_eq_spec_of_allFieldsNormal schema operation resolvers
    variableValues depth source (generatedNormalizedFieldChild schema)
  · intro childDepth childType runtimeType ref childSelectionSet _hlt
      hinclude hgenerated _hchildNormal _hchildFree
    exact
      executeRootSelectionSet_eq_spec_of_generatedNormalizedFieldChild schema
        resolvers variableValues childDepth childType runtimeType ref
        childSelectionSet hschema hinclude hgenerated
  · exact hall
  · exact hfree
  · exact hnormal
  · exact hlookup
  · exact hchildren

theorem executeQueryAtDepth_normalizeOperation_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationDirectiveFree operation ->
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.normalizeOperation schema operation) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (NormalForm.normalizeOperation schema operation) depth source := by
  intro hschema hfree
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  apply executeQueryAtDepth_eq_spec_of_generatedNormalOperation schema
    (NormalForm.normalizeOperation schema operation) resolvers variableValues
    depth source hschema
  · simpa [NormalForm.normalizeOperation] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
        schema operation.rootType operation.selectionSet
  · exact hnormalizedFree
  · exact
      NormalForm.GroundTypeNormalization.normalizeOperation_normal schema
        operation hschema
  · simpa [NormalForm.normalizeOperation] using
      executionSelectionSetLookupValid_normalizeSelectionSet schema
        operation.rootType operation.selectionSet
  · intro responseName fieldName arguments directives childSelectionSet hmem
    exact
      (by
        simpa [NormalForm.normalizeOperation] using
          normalizeSelectionSet_field_child_generated schema
            operation.rootType operation.selectionSet responseName fieldName
            arguments directives childSelectionSet hfree
            (by simpa [NormalForm.normalizeOperation] using hmem))

theorem executeQueryAtDepth_eq_spec_of_executeRootSelectionSet_eq
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet ->
    executeQueryAtDepth schema resolvers variableValues operation depth source =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source := by
  intro hroot
  unfold executeQueryAtDepth Execution.executeQueryAtDepth
  by_cases hsource :
      Execution.rootSourceAppliesBool schema operation source = true
  · simp [hsource]
    rw [hroot]
    rfl
  · simp [hsource]

theorem executeQueryAtDepth_eq_spec_depth_zero
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef) :
    CollectedSelectionSetGroupsSingleton schema variableValues
      operation.rootType source operation.selectionSet ->
    executeQueryAtDepth schema resolvers variableValues operation 0 source =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        0 source := by
  intro hsingletons
  by_cases hsource :
      Execution.rootSourceAppliesBool schema operation source = true
  · exact
      ({ root := hsource
         selectionSet :=
          ExecutedGroupedSelectionSetState.depth_zero schema resolvers
            variableValues operation.rootType source operation.selectionSet
            hsingletons } :
        ExecutedGroupedOperationState schema resolvers variableValues operation
          0 source).executeQueryAtDepth_eq_spec
  · unfold executeQueryAtDepth Execution.executeQueryAtDepth
    simp [hsource]

theorem executeRootSelectionSet_completeNormalizeOperation_eq_spec_of_runtime_body
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase) :
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
    executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet))
      =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet)) ->
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.completeNormalizeOperation schema operation).selectionSet := by
  intro hruntime hagrees hbody
  have hungrouped :
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.normalizeSelectionSet schema operation.rootType
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)) := by
    have hvisit :=
      visitSubfields_completeNormalizeRootSelectionSet_runtime schema
        resolvers variableValues operation depth operation.rootType source
        runtimeCase operation.selectionSet (Execution.ResponseValue.object [])
        hruntime hagrees
    let toRootResult :
        Execution.ResponseValue × VisitStatus ->
          Execution.Result (List (Name × Execution.ResponseValue)) :=
      fun visited =>
        match visited.snd with
        | Except.error errors => Except.error errors
        | Except.ok (_unit, errors) =>
            match visited.fst with
            | .object fields => Except.ok (fields, errors)
            | _ => Except.error (errors + 1)
    simpa [executeRootSelectionSet, NormalForm.completeNormalizeOperation] using
      congrArg toRootResult hvisit
  have hspec :
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.normalizeSelectionSet schema operation.rootType
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)) := by
    simpa [Execution.executeSelectionSet,
      NormalForm.completeNormalizeOperation] using
      NormalForm.CompleteNormalization.executeSelectionSet_completeNormalizeRootSelectionSet_runtime
        schema resolvers variableValues operation depth operation.rootType
        source runtimeCase operation.selectionSet hruntime hagrees
  exact hungrouped.trans (hbody.trans hspec.symm)

theorem executeQueryAtDepth_completeNormalizeOperation_eq_spec_of_runtime_body
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase) :
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
    executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet))
      =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet)) ->
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source := by
  intro hruntime hagrees hbody
  apply executeQueryAtDepth_eq_spec_of_executeRootSelectionSet_eq
  simpa [NormalForm.completeNormalizeOperation] using
    executeRootSelectionSet_completeNormalizeOperation_eq_spec_of_runtime_body
      schema operation resolvers variableValues depth source runtimeCase
      hruntime hagrees hbody

theorem executeQueryAtDepth_completeNormalizeOperation_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source := by
  intro hschema hcomplete
  rcases
      NormalForm.CompleteNormalization.operationBoolVarsComplete_caseForVariableValues
        variableValues operation hcomplete with
    ⟨runtimeCase, hruntime, hagrees⟩
  apply executeQueryAtDepth_completeNormalizeOperation_eq_spec_of_runtime_body
    schema operation resolvers variableValues depth source runtimeCase hruntime
    hagrees
  apply executeRootSelectionSet_eq_spec_of_normalizeSelectionSet schema resolvers
    variableValues depth operation.rootType source
    (NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet)
    hschema
  exact NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
    schema runtimeCase operation.selectionSet

theorem specExecution_eq_ungroupedExecution_of_completeNormalizeOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      Execution.executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source := by
  intro hschema hcomplete
  exact (executeQueryAtDepth_completeNormalizeOperation_eq_spec schema
    operation resolvers variableValues depth source hschema hcomplete).symm

theorem executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source := by
  intro hschema hvalid hcomplete
  have hcompleteUngrouped :
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source :=
    executeQueryAtDepth_completeNormalizeOperation_eq_spec schema operation
      resolvers variableValues depth source hschema hcomplete
  have hcompleteSpec :
      Execution.executeQueryAtDepth schema resolvers variableValues operation
          depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source :=
    by
      exact
        NormalForm.CompleteNormalization.completeNormalizationSemanticsPreserved
          schema operation hschema hvalid resolvers variableValues depth source
          hcomplete
  exact hcompleteUngrouped.trans hcompleteSpec.symm

theorem completeNormalizationPreservesUngroupedExecutionSemantics
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues depth (source : Execution.ResolverValue ObjectRef),
      NormalForm.operationBoolVarsComplete operation variableValues ->
        executeQueryAtDepth schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth source
          =
        Execution.executeQueryAtDepth schema resolvers variableValues operation
          depth source := by
  intro hschema hvalid ObjectRef resolvers variableValues depth source hcomplete
  exact executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete

theorem ungroupedExecutionPreservesSpecExecution_semanticsPreserved
    (schema : Schema) (operation : Operation) :
    ungroupedExecutionPreservesSpecExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues depth source
    hcomplete
  exact executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    executeQueryAtDepth schema resolvers variableValues operation depth source =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source := by
  intro hschema hvalid hcomplete hsource
  have hnormalized :
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source :=
    executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
      schema operation resolvers variableValues depth source hschema hvalid
      hcomplete
  exact hsource.trans hnormalized.symm

theorem completeNormalizationPreservesUngroupedExecution_of_executedGroupedOperationState
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (state :
      ExecutedGroupedOperationState schema resolvers variableValues operation
        depth source) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth
        source := by
  intro hschema hvalid hcomplete
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete
  exact state.executeQueryAtDepth_eq_spec

theorem completeNormalizationPreservesUngroupedExecution_of_collected_groups_recursiveAppendState
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    {groups : List (Name × List Execution.ExecutableField)}
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (hcollect :
      Execution.collectFields schema variableValues operation.rootType source
        operation.selectionSet = groups)
      (hflat :
        VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          operation.rootType source operation.selectionSet (.object []))
      (hcollected :
        ExecutionCollectedFieldInvariant
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := operation.rootType
              source := source
              selectionSet := operation.selectionSet }
            initial := .object [] })
      (hlookups : CollectedGroupsFieldLookupValid schema operation.rootType groups)
      (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend :
      CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_executedGroupedOperationState
        schema operation resolvers variableValues (depth + 1) source
        (ExecutedGroupedOperationState.of_collected_groups_recursiveAppendState
          hroot hcollect hflat hcollected hlookups hcompatible happend)
        hschema hvalid hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (state :
      RecursiveGroupedOperationState schema resolvers variableValues operation
        depth source) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_executedGroupedOperationState
      schema operation resolvers variableValues (depth + 1) source
      state.toExecutedGroupedOperationState hschema hvalid hcomplete

theorem executeQueryAtDepth_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (state :
      RecursiveGroupedOperationState schema resolvers variableValues operation
        depth source) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        (depth + 1) source := by
  intro hschema hvalid hcomplete
  have hpreserved :
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source :=
    completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
      schema operation resolvers variableValues depth source state hschema
      hvalid hcomplete
  have hnormalized :
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
          source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        (depth + 1) source :=
    executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved schema
      operation resolvers variableValues (depth + 1) source hschema hvalid
      hcomplete
  exact hpreserved.trans hnormalized

theorem completeNormalizationPreservesUngroupedExecution_of_globalInvariants
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (invariants :
      RecursiveSelectionSetGlobalInvariants schema resolvers variableValues) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
      schema operation resolvers variableValues depth source
      (RecursiveGroupedOperationState.of_globalInvariants hroot invariants)
      hschema hvalid hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_globalFreshPrefixInvariants
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (invariants :
      RecursiveSelectionSetGlobalFreshPrefixInvariants schema resolvers
        variableValues) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_globalInvariants
      schema operation resolvers variableValues depth source hroot
      invariants.toGlobalInvariants hschema hvalid hcomplete

theorem executeQueryAtDepth_semanticsPreserved_of_globalFreshPrefixInvariants
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (invariants :
      RecursiveSelectionSetGlobalFreshPrefixInvariants schema resolvers
        variableValues) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        (depth + 1) source := by
  intro hschema hvalid hcomplete
  have hpreserved :
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source :=
    completeNormalizationPreservesUngroupedExecution_of_globalFreshPrefixInvariants
      schema operation resolvers variableValues depth source hroot invariants
      hschema hvalid hcomplete
  have hnormalized :
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
          source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        (depth + 1) source :=
    executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved schema
      operation resolvers variableValues (depth + 1) source hschema hvalid
      hcomplete
  exact hpreserved.trans hnormalized

theorem completeNormalizationPreservesUngroupedExecution_iff_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcomplete :
      NormalForm.operationBoolVarsComplete operation variableValues) :
      (executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source)
      ↔
      executeQueryAtDepth schema resolvers variableValues operation depth source =
        Execution.executeQueryAtDepth schema resolvers variableValues operation
          depth source := by
  have hnormalized :
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source :=
    executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
      schema operation resolvers variableValues depth source hschema hvalid
      hcomplete
  constructor
  · intro hpreserved
    exact hpreserved.trans hnormalized
  · intro hsource
    exact hsource.trans hnormalized.symm

theorem completeNormalizationPreservesUngroupedExecution_iff_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation) :
      (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
        variableValues depth (source : Execution.ResolverValue ObjectRef),
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeQueryAtDepth schema resolvers variableValues operation
              depth source
            =
          executeQueryAtDepth schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth
            source)
      ↔
      (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
        variableValues depth (source : Execution.ResolverValue ObjectRef),
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeQueryAtDepth schema resolvers variableValues operation
              depth source
            =
          Execution.executeQueryAtDepth schema resolvers variableValues
            operation depth source) := by
  constructor
  · intro hpreserved ObjectRef resolvers variableValues depth source hcomplete
    exact
      (completeNormalizationPreservesUngroupedExecution_iff_source_eq_spec
        schema operation resolvers variableValues depth source hschema hvalid
        hcomplete).mp
        (hpreserved resolvers variableValues depth source hcomplete)
  · intro hsemantics ObjectRef resolvers variableValues depth source hcomplete
    exact
      (completeNormalizationPreservesUngroupedExecution_iff_source_eq_spec
        schema operation resolvers variableValues depth source hschema hvalid
        hcomplete).mpr
        (hsemantics resolvers variableValues depth source hcomplete)

theorem completeNormalizationPreservesUngroupedExecution_of_source_semanticsPreserved
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues depth (source : Execution.ResolverValue ObjectRef),
      NormalForm.operationBoolVarsComplete operation variableValues ->
        executeQueryAtDepth schema resolvers variableValues operation
            depth source
          =
        Execution.executeQueryAtDepth schema resolvers variableValues operation
          depth source) ->
      ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
        variableValues depth (source : Execution.ResolverValue ObjectRef),
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeQueryAtDepth schema resolvers variableValues operation
              depth source
            =
          executeQueryAtDepth schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth
            source := by
  intro hschema hvalid hsourceSemantics ObjectRef resolvers variableValues
    depth source hcomplete
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete
  exact hsourceSemantics resolvers variableValues depth source hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_generatedNormalOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
    executionSelectionSetLookupValid schema operation.rootType
      operation.selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ operation.selectionSet ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? operation.rootType fieldName).getD
            fieldName)
          childSelectionSet) ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth
        source := by
  intro hschema hvalid hcomplete hall hfree hnormal hlookup hchildren
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete
  exact executeQueryAtDepth_eq_spec_of_generatedNormalOperation schema
    operation resolvers variableValues depth source hschema hall hfree hnormal
    hlookup hchildren

theorem completeNormalizationPreservesUngroupedExecution_of_normalizeOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.normalizeOperation schema operation) depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema
          (NormalForm.normalizeOperation schema operation)) depth source := by
  intro hschema hvalid hfree hfeasibleAll
  have hnormalizedValid :
      Validation.operationDefinitionValid schema
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_valid schema
      operation hschema hvalid hfree hfeasibleAll
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema (NormalForm.normalizeOperation schema operation) resolvers
    variableValues depth source hschema hnormalizedValid
    (NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
      (NormalForm.normalizeOperation schema operation) variableValues
      hnormalizedFree)
  exact executeQueryAtDepth_normalizeOperation_eq_spec schema operation
    resolvers variableValues depth source hschema hfree

theorem normalizeThenCompleteUngroupedExecution_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.selectionSetsTypeConditionFeasibleInEveryScope schema ->
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema
            (NormalForm.normalizeOperation schema operation)) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source := by
  intro hschema hvalid hfree hfeasibleAll
  have hnormalizedValid :
      Validation.operationDefinitionValid schema
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_valid schema
      operation hschema hvalid hfree hfeasibleAll
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  have hcomplete :
      NormalForm.operationBoolVarsComplete
        (NormalForm.normalizeOperation schema operation) variableValues :=
    NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
      (NormalForm.normalizeOperation schema operation) variableValues
      hnormalizedFree
  have hcompleteUngrouped :
      executeQueryAtDepth schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema
            (NormalForm.normalizeOperation schema operation)) depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (NormalForm.normalizeOperation schema operation) depth source :=
    executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved schema
      (NormalForm.normalizeOperation schema operation) resolvers
      variableValues depth source hschema hnormalizedValid hcomplete
  have hgroundSpec :
      Execution.executeQueryAtDepth schema resolvers variableValues operation
          depth source
        =
      Execution.executeQueryAtDepth schema resolvers variableValues
        (NormalForm.normalizeOperation schema operation) depth source :=
    by
      exact
        NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation
          schema operation hschema hvalid hfree resolvers variableValues depth
          source
  exact hcompleteUngrouped.trans hgroundSpec.symm

end ExecutionUngrouped
end Algorithms

end GraphQL
