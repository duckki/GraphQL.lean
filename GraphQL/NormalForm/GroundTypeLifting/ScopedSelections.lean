import GraphQL.NormalForm.GroundTypeLifting.Structural
import GraphQL.NormalForm.Shared.SemanticReadiness

/-!
Scoped selection-set machinery for ground-type lifting proofs.
-/
namespace GraphQL

namespace NormalForm

namespace GroundTypeLifting

structure ScopedSelection where
  liftParent : Name
  selection : Selection

def scopedSelectionSet (liftParent : Name) :
    List Selection -> List ScopedSelection
  | [] => []
  | selection :: rest =>
      { liftParent := liftParent, selection := selection }
        :: scopedSelectionSet liftParent rest

def eraseScopedSelection : ScopedSelection -> Selection
  | scopedSelection => scopedSelection.selection

def eraseScopedSelectionSet : List ScopedSelection -> List Selection
  | [] => []
  | scopedSelection :: rest =>
      eraseScopedSelection scopedSelection :: eraseScopedSelectionSet rest

def groundLiftScopedSelection (schema : Schema) :
    ScopedSelection -> Selection
  | scopedSelection =>
      groundLiftSelection schema scopedSelection.liftParent
        scopedSelection.selection

def groundLiftScopedSelectionSet (schema : Schema) :
    List ScopedSelection -> List Selection
  | [] => []
  | scopedSelection :: rest =>
      groundLiftScopedSelection schema scopedSelection
        :: groundLiftScopedSelectionSet schema rest

theorem eraseScopedSelectionSet_append :
    ∀ left right : List ScopedSelection,
      eraseScopedSelectionSet (left ++ right)
        =
      eraseScopedSelectionSet left ++ eraseScopedSelectionSet right
  | [], right => by
      simp [eraseScopedSelectionSet]
  | scopedSelection :: rest, right => by
      simp [eraseScopedSelectionSet,
        eraseScopedSelectionSet_append rest right]

theorem groundLiftScopedSelectionSet_append (schema : Schema) :
    ∀ left right : List ScopedSelection,
      groundLiftScopedSelectionSet schema (left ++ right)
        =
      groundLiftScopedSelectionSet schema left
        ++ groundLiftScopedSelectionSet schema right
  | [], right => by
      simp [groundLiftScopedSelectionSet]
  | scopedSelection :: rest, right => by
      simp [groundLiftScopedSelectionSet,
        groundLiftScopedSelectionSet_append schema rest right]

theorem eraseScopedSelectionSet_scopedSelectionSet
    (liftParent : Name) :
    ∀ selectionSet,
      eraseScopedSelectionSet (scopedSelectionSet liftParent selectionSet)
        =
      selectionSet
  | [] => by
      simp [eraseScopedSelectionSet, scopedSelectionSet]
  | selection :: rest => by
      simp [eraseScopedSelectionSet, eraseScopedSelection,
        scopedSelectionSet,
        eraseScopedSelectionSet_scopedSelectionSet liftParent rest]

theorem eraseScopedSelectionSet_mem_selection
    {scopedSelection : ScopedSelection} :
    ∀ {scopedSelections : List ScopedSelection},
      scopedSelection ∈ scopedSelections ->
        scopedSelection.selection ∈
          eraseScopedSelectionSet scopedSelections
  | [], hmem => by
      cases hmem
  | head :: rest, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp [eraseScopedSelectionSet, eraseScopedSelection]
      · exact List.mem_cons_of_mem (eraseScopedSelection head)
          (eraseScopedSelectionSet_mem_selection htail)

theorem groundLiftScopedSelectionSet_scopedSelectionSet
    (schema : Schema) (liftParent : Name) :
    ∀ selectionSet,
      groundLiftScopedSelectionSet schema
          (scopedSelectionSet liftParent selectionSet)
        =
      groundLiftSelectionSet schema liftParent selectionSet
  | [] => by
      simp [groundLiftScopedSelectionSet, scopedSelectionSet,
        groundLiftSelectionSet]
  | selection :: rest => by
      simp [groundLiftScopedSelectionSet, groundLiftScopedSelection,
        scopedSelectionSet, groundLiftSelectionSet,
        groundLiftScopedSelectionSet_scopedSelectionSet schema liftParent
          rest]

def scopedSelectionSetLookupValid (schema : Schema)
    (scopedSelectionSet : List ScopedSelection) : Prop :=
  ∀ scopedSelection, scopedSelection ∈ scopedSelectionSet ->
    selectionLookupValid schema scopedSelection.liftParent
      scopedSelection.selection

theorem scopedSelectionSetLookupValid_scopedSelectionSet
    (schema : Schema) (liftParent : Name) :
    ∀ selectionSet,
      scopedSelectionSetLookupValid schema
          (scopedSelectionSet liftParent selectionSet)
        ↔
      selectionSetLookupValid schema liftParent selectionSet
  | [] => by
      simp [scopedSelectionSetLookupValid, scopedSelectionSet,
        selectionSetLookupValid]
  | selection :: rest => by
      constructor
      · intro hvalid
        have hhead :
            selectionLookupValid schema liftParent selection := by
          exact hvalid { liftParent := liftParent, selection := selection }
            (by simp [scopedSelectionSet])
        have htail :
            selectionSetLookupValid schema liftParent rest := by
          exact
            (scopedSelectionSetLookupValid_scopedSelectionSet schema
              liftParent rest).mp
              (by
                intro scopedSelection hmem
                exact hvalid scopedSelection
                  (by simp [scopedSelectionSet, hmem]))
        unfold selectionSetLookupValid
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hhead
        · unfold selectionSetLookupValid at htail
          exact htail candidate hcandidate
      · intro hvalid scopedSelection hmem
        simp [scopedSelectionSet] at hmem
        rcases hmem with hhead | htail
        · subst scopedSelection
          unfold selectionSetLookupValid at hvalid
          exact hvalid selection (by simp)
        · exact
            (scopedSelectionSetLookupValid_scopedSelectionSet schema
              liftParent rest).mpr
              (selectionSetLookupValid_tail hvalid)
              scopedSelection htail

def scopedSelectionSetDirectiveFree
    (scopedSelections : List ScopedSelection) : Prop :=
  selectionSetDirectiveFree (eraseScopedSelectionSet scopedSelections)

def scopedSelectionSetSemanticsReady
    (schema : Schema) (execParent : Name)
    (scopedSelections : List ScopedSelection) : Prop :=
  selectionSetSemanticsReady schema execParent
    (eraseScopedSelectionSet scopedSelections)

def scopedSelectionSetCanMerge
    (schema : Schema) (execParent : Name)
    (scopedSelections : List ScopedSelection) : Prop :=
  FieldMerge.fieldsInSetCanMerge schema execParent
    (eraseScopedSelectionSet scopedSelections)

def scopedSelectionSetRuntimeApplies
    (schema : Schema) (runtimeType : Name)
    (scopedSelections : List ScopedSelection) : Prop :=
  ∀ scopedSelection, scopedSelection ∈ scopedSelections ->
    schema.typeIncludesObjectBool scopedSelection.liftParent runtimeType = true

theorem scopedSelectionSetLookupValid_append
    {schema : Schema} {left right : List ScopedSelection} :
    scopedSelectionSetLookupValid schema left ->
      scopedSelectionSetLookupValid schema right ->
        scopedSelectionSetLookupValid schema (left ++ right) := by
  intro hleft hright scopedSelection hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft scopedSelection hmem
  · exact hright scopedSelection hmem

theorem scopedSelectionSetLookupValid_append_left
    {schema : Schema} {left right : List ScopedSelection} :
    scopedSelectionSetLookupValid schema (left ++ right) ->
      scopedSelectionSetLookupValid schema left := by
  intro hvalid scopedSelection hmem
  exact hvalid scopedSelection (List.mem_append.mpr (Or.inl hmem))

theorem scopedSelectionSetLookupValid_append_right
    {schema : Schema} {left right : List ScopedSelection} :
    scopedSelectionSetLookupValid schema (left ++ right) ->
      scopedSelectionSetLookupValid schema right := by
  intro hvalid scopedSelection hmem
  exact hvalid scopedSelection (List.mem_append.mpr (Or.inr hmem))

theorem scopedSelectionSetLookupValid_tail
    {schema : Schema} {scopedSelection : ScopedSelection}
    {rest : List ScopedSelection} :
    scopedSelectionSetLookupValid schema (scopedSelection :: rest) ->
      scopedSelectionSetLookupValid schema rest := by
  intro hvalid candidate hcandidate
  exact hvalid candidate (List.mem_cons_of_mem scopedSelection hcandidate)

theorem scopedSelectionSetDirectiveFree_scopedSelectionSet
    (liftParent : Name) (selectionSet : List Selection) :
    scopedSelectionSetDirectiveFree
        (scopedSelectionSet liftParent selectionSet)
      ↔
    selectionSetDirectiveFree selectionSet := by
  simp [scopedSelectionSetDirectiveFree,
    eraseScopedSelectionSet_scopedSelectionSet]

theorem scopedSelectionSetSemanticsReady_scopedSelectionSet
    (schema : Schema) (execParent liftParent : Name)
    (selectionSet : List Selection) :
    scopedSelectionSetSemanticsReady schema execParent
        (scopedSelectionSet liftParent selectionSet)
      ↔
    selectionSetSemanticsReady schema execParent selectionSet := by
  simp [scopedSelectionSetSemanticsReady,
    eraseScopedSelectionSet_scopedSelectionSet]

theorem scopedSelectionSetCanMerge_scopedSelectionSet
    (schema : Schema) (execParent liftParent : Name)
    (selectionSet : List Selection) :
    scopedSelectionSetCanMerge schema execParent
        (scopedSelectionSet liftParent selectionSet)
      ↔
    FieldMerge.fieldsInSetCanMerge schema execParent selectionSet := by
  simp [scopedSelectionSetCanMerge,
    eraseScopedSelectionSet_scopedSelectionSet]

theorem scopedSelectionSetDirectiveFree_append
    {left right : List ScopedSelection} :
    scopedSelectionSetDirectiveFree left ->
      scopedSelectionSetDirectiveFree right ->
        scopedSelectionSetDirectiveFree (left ++ right) := by
  intro hleft hright
  simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet_append]
    using selectionSetDirectiveFree_append hleft hright

theorem scopedSelectionSetDirectiveFree_append_left
    {left right : List ScopedSelection} :
    scopedSelectionSetDirectiveFree (left ++ right) ->
      scopedSelectionSetDirectiveFree left := by
  intro hfree
  have hraw :
      selectionSetDirectiveFree
        (eraseScopedSelectionSet left ++ eraseScopedSelectionSet right) := by
    simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet_append]
      using hfree
  simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet_append]
    using selectionSetDirectiveFree_append_left
      (left := eraseScopedSelectionSet left)
      (right := eraseScopedSelectionSet right) hraw

theorem scopedSelectionSetDirectiveFree_append_right
    {left right : List ScopedSelection} :
    scopedSelectionSetDirectiveFree (left ++ right) ->
      scopedSelectionSetDirectiveFree right := by
  intro hfree
  have hraw :
      selectionSetDirectiveFree
        (eraseScopedSelectionSet left ++ eraseScopedSelectionSet right) := by
    simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet_append]
      using hfree
  simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet_append]
    using selectionSetDirectiveFree_append_right
      (left := eraseScopedSelectionSet left)
      (right := eraseScopedSelectionSet right) hraw

theorem scopedSelectionSetDirectiveFree_tail
    {scopedSelection : ScopedSelection} {rest : List ScopedSelection} :
    scopedSelectionSetDirectiveFree (scopedSelection :: rest) ->
      scopedSelectionSetDirectiveFree rest := by
  intro hfree
  simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet]
    using selectionSetDirectiveFree_tail
      (selection := eraseScopedSelection scopedSelection)
      (selectionSet := eraseScopedSelectionSet rest) hfree

theorem scopedSelectionSetSemanticsReady_append
    {schema : Schema} {execParent : Name}
    {left right : List ScopedSelection} :
    scopedSelectionSetSemanticsReady schema execParent left ->
      scopedSelectionSetSemanticsReady schema execParent right ->
        scopedSelectionSetSemanticsReady schema execParent
          (left ++ right) := by
  intro hleft hright
  simpa [scopedSelectionSetSemanticsReady, eraseScopedSelectionSet_append]
    using selectionSetSemanticsReady_append hleft hright

theorem scopedSelectionSetSemanticsReady_append_left
    {schema : Schema} {execParent : Name}
    {left right : List ScopedSelection} :
    scopedSelectionSetSemanticsReady schema execParent (left ++ right) ->
      scopedSelectionSetSemanticsReady schema execParent left := by
  intro hready
  have hraw :
      selectionSetSemanticsReady schema execParent
        (eraseScopedSelectionSet left ++ eraseScopedSelectionSet right) := by
    simpa [scopedSelectionSetSemanticsReady,
      eraseScopedSelectionSet_append] using hready
  simpa [scopedSelectionSetSemanticsReady, eraseScopedSelectionSet_append]
    using selectionSetSemanticsReady_append_left
      (left := eraseScopedSelectionSet left)
      (right := eraseScopedSelectionSet right) hraw

theorem scopedSelectionSetSemanticsReady_append_right
    {schema : Schema} {execParent : Name}
    {left right : List ScopedSelection} :
    scopedSelectionSetSemanticsReady schema execParent (left ++ right) ->
      scopedSelectionSetSemanticsReady schema execParent right := by
  intro hready
  have hraw :
      selectionSetSemanticsReady schema execParent
        (eraseScopedSelectionSet left ++ eraseScopedSelectionSet right) := by
    simpa [scopedSelectionSetSemanticsReady,
      eraseScopedSelectionSet_append] using hready
  simpa [scopedSelectionSetSemanticsReady, eraseScopedSelectionSet_append]
    using selectionSetSemanticsReady_append_right
      (left := eraseScopedSelectionSet left)
      (right := eraseScopedSelectionSet right) hraw

theorem scopedSelectionSetSemanticsReady_tail
    {schema : Schema} {execParent : Name}
    {scopedSelection : ScopedSelection} {rest : List ScopedSelection} :
    scopedSelectionSetSemanticsReady schema execParent
        (scopedSelection :: rest) ->
      scopedSelectionSetSemanticsReady schema execParent rest := by
  intro hready
  simpa [scopedSelectionSetSemanticsReady, eraseScopedSelectionSet]
    using selectionSetSemanticsReady_tail
      (selection := eraseScopedSelection scopedSelection)
      (selectionSet := eraseScopedSelectionSet rest) hready

theorem scopedSelectionSetCanMerge_append_left
    (schema : Schema) (execParent : Name)
    (left right : List ScopedSelection) :
    scopedSelectionSetCanMerge schema execParent (left ++ right) ->
      scopedSelectionSetCanMerge schema execParent left := by
  intro hmerge
  have hraw :
      FieldMerge.fieldsInSetCanMerge schema execParent
        (eraseScopedSelectionSet left ++ eraseScopedSelectionSet right) := by
    simpa [scopedSelectionSetCanMerge, eraseScopedSelectionSet_append]
      using hmerge
  simpa [scopedSelectionSetCanMerge, eraseScopedSelectionSet_append]
    using fieldsInSetCanMerge_append_left schema execParent
      (eraseScopedSelectionSet left) (eraseScopedSelectionSet right)
      hraw

theorem scopedSelectionSetCanMerge_append_right
    (schema : Schema) (execParent : Name)
    (left right : List ScopedSelection) :
    scopedSelectionSetCanMerge schema execParent (left ++ right) ->
      scopedSelectionSetCanMerge schema execParent right := by
  intro hmerge
  have hraw :
      FieldMerge.fieldsInSetCanMerge schema execParent
        (eraseScopedSelectionSet left ++ eraseScopedSelectionSet right) := by
    simpa [scopedSelectionSetCanMerge, eraseScopedSelectionSet_append]
      using hmerge
  simpa [scopedSelectionSetCanMerge, eraseScopedSelectionSet_append]
    using fieldsInSetCanMerge_append_right schema execParent
      (eraseScopedSelectionSet left) (eraseScopedSelectionSet right)
      hraw

theorem scopedSelectionSetCanMerge_tail
    (schema : Schema) (execParent : Name)
    (scopedSelection : ScopedSelection) (rest : List ScopedSelection) :
    scopedSelectionSetCanMerge schema execParent
        (scopedSelection :: rest) ->
      scopedSelectionSetCanMerge schema execParent rest := by
  intro hmerge
  simpa [scopedSelectionSetCanMerge, eraseScopedSelectionSet]
    using fieldsInSetCanMerge_tail schema execParent
      (eraseScopedSelection scopedSelection)
      (eraseScopedSelectionSet rest) hmerge

theorem scopedSelectionSetRuntimeApplies_scopedSelectionSet
    (schema : Schema) (liftParent runtimeType : Name)
    (selectionSet : List Selection) :
    schema.typeIncludesObjectBool liftParent runtimeType = true ->
      scopedSelectionSetRuntimeApplies schema runtimeType
        (scopedSelectionSet liftParent selectionSet) := by
  intro hinclude scopedSelection hscoped
  induction selectionSet with
  | nil =>
      simp [scopedSelectionSet] at hscoped
  | cons selection rest ih =>
      simp [scopedSelectionSet] at hscoped
      rcases hscoped with hhead | htail
      · subst scopedSelection
        exact hinclude
      · exact ih htail

theorem scopedSelectionSetRuntimeApplies_tail
    {schema : Schema} {runtimeType : Name}
    {scopedSelection : ScopedSelection} {rest : List ScopedSelection} :
    scopedSelectionSetRuntimeApplies schema runtimeType
        (scopedSelection :: rest) ->
      scopedSelectionSetRuntimeApplies schema runtimeType rest := by
  intro happlies candidate hcandidate
  exact happlies candidate (List.mem_cons_of_mem scopedSelection hcandidate)

theorem scopedSelectionSetRuntimeApplies_append
    {schema : Schema} {runtimeType : Name}
    {left right : List ScopedSelection} :
    scopedSelectionSetRuntimeApplies schema runtimeType left ->
      scopedSelectionSetRuntimeApplies schema runtimeType right ->
        scopedSelectionSetRuntimeApplies schema runtimeType (left ++ right) := by
  intro hleft hright scopedSelection hscoped
  rcases List.mem_append.mp hscoped with hscoped | hscoped
  · exact hleft scopedSelection hscoped
  · exact hright scopedSelection hscoped

theorem scopedSelectionSetRuntimeApplies_append_left
    {schema : Schema} {runtimeType : Name}
    {left right : List ScopedSelection} :
    scopedSelectionSetRuntimeApplies schema runtimeType (left ++ right) ->
      scopedSelectionSetRuntimeApplies schema runtimeType left := by
  intro happlies scopedSelection hscoped
  exact happlies scopedSelection (List.mem_append.mpr (Or.inl hscoped))

theorem scopedSelectionSetRuntimeApplies_append_right
    {schema : Schema} {runtimeType : Name}
    {left right : List ScopedSelection} :
    scopedSelectionSetRuntimeApplies schema runtimeType (left ++ right) ->
      scopedSelectionSetRuntimeApplies schema runtimeType right := by
  intro happlies scopedSelection hscoped
  exact happlies scopedSelection (List.mem_append.mpr (Or.inr hscoped))

def scopedFieldSelectionsWithResponseNameInScope
    (schema : Schema) (filterParent responseName liftParent : Name) :
    List Selection -> List ScopedSelection
  | [] => []
  | selection :: rest =>
      let restFields :=
        scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
          liftParent rest
      match selection with
      | .field fieldResponseName _fieldName _arguments _directives
          _selectionSet =>
          if fieldResponseName == responseName then
            { liftParent := liftParent, selection := selection } :: restFields
          else
            restFields
      | .inlineFragment none _directives selectionSet =>
          scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
              liftParent selectionSet
            ++ restFields
      | .inlineFragment (some typeCondition) _directives selectionSet =>
          if schema.typesOverlapBool filterParent typeCondition then
            scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
                typeCondition selectionSet
              ++ restFields
          else
            restFields

theorem scopedFieldSelectionsWithResponseNameInScope_runtimeApplies
    (schema : Schema) (filterParent responseName liftParent runtimeType : Name)
    (selectionSet : List Selection) :
    objectTypeNameBool schema filterParent = true ->
    schema.typeIncludesObjectBool filterParent runtimeType = true ->
    schema.typeIncludesObjectBool liftParent runtimeType = true ->
      scopedSelectionSetRuntimeApplies schema runtimeType
        (scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
          liftParent selectionSet) :=
  match selectionSet with
  | [] => by
      intro _hfilterObject _hfilterInclude _hliftInclude
      simp [scopedFieldSelectionsWithResponseNameInScope,
        scopedSelectionSetRuntimeApplies]
  | selection :: rest => by
      intro hfilterObject hfilterInclude hliftInclude
      have hfilterObjectProp : schema.objectType filterParent :=
        objectType_of_objectTypeNameBool_eq_true schema hfilterObject
      have hruntimeEq : runtimeType = filterParent :=
        object_typeIncludesObjectBool_eq_self schema hfilterObjectProp
          hfilterInclude
      subst runtimeType
      cases selection with
      | field fieldResponseName fieldName arguments directives subselections =>
          by_cases hresponse :
              (fieldResponseName == responseName) = true
          · intro scopedSelection hscoped
            simp [scopedFieldSelectionsWithResponseNameInScope, hresponse] at hscoped
            rcases hscoped with hhead | htail
            · subst scopedSelection
              exact hliftInclude
            · exact scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                filterParent responseName liftParent filterParent rest
                hfilterObject
                (object_typeIncludesObjectBool_self schema hfilterObjectProp)
                hliftInclude scopedSelection htail
          · have hfalse :
                (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · exact False.elim (hresponse hmatch)
            simpa [scopedFieldSelectionsWithResponseNameInScope, hfalse] using
              scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                filterParent responseName liftParent filterParent rest
                hfilterObject
                (object_typeIncludesObjectBool_self schema hfilterObjectProp)
                hliftInclude
      | inlineFragment typeCondition directives subselections =>
          cases typeCondition with
          | none =>
              have hbody :=
                scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                  filterParent responseName liftParent filterParent
                  subselections hfilterObject
                  (object_typeIncludesObjectBool_self schema
                    hfilterObjectProp)
                  hliftInclude
              have hrest :=
                scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                  filterParent responseName liftParent filterParent rest
                  hfilterObject
                  (object_typeIncludesObjectBool_self schema
                    hfilterObjectProp)
                  hliftInclude
              simpa [scopedFieldSelectionsWithResponseNameInScope] using
                scopedSelectionSetRuntimeApplies_append hbody hrest
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · have htypeInclude :
                    schema.typeIncludesObjectBool typeCondition filterParent =
                      true :=
                  typeIncludesObjectBool_of_object_typesOverlapBool schema
                    hfilterObjectProp hoverlap
                have hbody :=
                  scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                    filterParent responseName typeCondition filterParent
                    subselections hfilterObject
                    (object_typeIncludesObjectBool_self schema
                      hfilterObjectProp)
                    htypeInclude
                have hrest :=
                  scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                    filterParent responseName liftParent filterParent rest
                    hfilterObject
                    (object_typeIncludesObjectBool_self schema
                      hfilterObjectProp)
                    hliftInclude
                simpa [scopedFieldSelectionsWithResponseNameInScope, hoverlap] using
                  scopedSelectionSetRuntimeApplies_append hbody hrest
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool filterParent typeCondition
                  · rfl
                  · exact False.elim (hoverlap hmatch)
                simpa [scopedFieldSelectionsWithResponseNameInScope, hfalse] using
                  scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                    filterParent responseName liftParent filterParent rest
                    hfilterObject
                    (object_typeIncludesObjectBool_self schema
                      hfilterObjectProp)
                    hliftInclude

theorem scopedFieldSelectionsWithResponseNameInScope_lookupValid
    (schema : Schema) (filterParent responseName liftParent : Name) :
    ∀ selectionSet,
      selectionSetLookupValid schema liftParent selectionSet ->
        scopedSelectionSetLookupValid schema
          (scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
            liftParent selectionSet)
  | [], _hvalid => by
      simp [scopedFieldSelectionsWithResponseNameInScope,
        scopedSelectionSetLookupValid]
  | selection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema liftParent selection :=
        selectionSetLookupValid_head hvalid
      have htailValid :
          selectionSetLookupValid schema liftParent rest :=
        selectionSetLookupValid_tail hvalid
      have hrest :=
        scopedFieldSelectionsWithResponseNameInScope_lookupValid schema filterParent
          responseName liftParent rest htailValid
      cases selection with
      | field fieldResponseName fieldName arguments directives subselections =>
          by_cases hresponse :
              (fieldResponseName == responseName) = true
          · intro scopedSelection hscoped
            simp [scopedFieldSelectionsWithResponseNameInScope, hresponse] at hscoped
            rcases hscoped with hhead | htail
            · subst scopedSelection
              exact hheadValid
            · exact hrest scopedSelection htail
          · have hfalse :
                (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · exact False.elim (hresponse hmatch)
            simpa [scopedFieldSelectionsWithResponseNameInScope, hfalse] using hrest
      | inlineFragment typeCondition directives subselections =>
          cases typeCondition with
          | none =>
              have hbodyValid :
                  selectionSetLookupValid schema liftParent subselections := by
                simpa [selectionLookupValid] using hheadValid
              have hbody :=
                scopedFieldSelectionsWithResponseNameInScope_lookupValid schema
                  filterParent responseName liftParent subselections
                  hbodyValid
              simpa [scopedFieldSelectionsWithResponseNameInScope] using
                scopedSelectionSetLookupValid_append hbody hrest
          | some typeCondition =>
              have hbodyValid :
                  selectionSetLookupValid schema typeCondition subselections := by
                simpa [selectionLookupValid] using hheadValid
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · have hbody :=
                  scopedFieldSelectionsWithResponseNameInScope_lookupValid schema
                    filterParent responseName typeCondition subselections
                    hbodyValid
                simpa [scopedFieldSelectionsWithResponseNameInScope, hoverlap] using
                  scopedSelectionSetLookupValid_append hbody hrest
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool filterParent typeCondition
                  · rfl
                  · exact False.elim (hoverlap hmatch)
                simpa [scopedFieldSelectionsWithResponseNameInScope, hfalse] using hrest

theorem eraseScopedFieldSelectionsWithResponseNameInScope
    (schema : Schema) (filterParent responseName : Name) :
    ∀ liftParent selectionSet,
      eraseScopedSelectionSet
          (scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
            liftParent selectionSet)
        =
      fieldSelectionsWithResponseNameInScope schema filterParent responseName
        selectionSet
  | liftParent, [] => by
      simp [scopedFieldSelectionsWithResponseNameInScope,
        eraseScopedSelectionSet, fieldSelectionsWithResponseNameInScope]
  | liftParent, selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hresponse : (fieldResponseName == responseName) = true
          · simp [scopedFieldSelectionsWithResponseNameInScope,
              fieldSelectionsWithResponseNameInScope, hresponse,
              eraseScopedSelectionSet, eraseScopedSelection,
              eraseScopedFieldSelectionsWithResponseNameInScope schema filterParent
                responseName liftParent rest]
          · have hfalse :
                (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · exact False.elim (hresponse hmatch)
            simp [scopedFieldSelectionsWithResponseNameInScope,
              fieldSelectionsWithResponseNameInScope, hfalse,
              eraseScopedFieldSelectionsWithResponseNameInScope schema filterParent
                responseName liftParent rest]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [scopedFieldSelectionsWithResponseNameInScope,
                fieldSelectionsWithResponseNameInScope, eraseScopedSelectionSet_append,
                eraseScopedFieldSelectionsWithResponseNameInScope schema filterParent
                  responseName liftParent selectionSet,
                eraseScopedFieldSelectionsWithResponseNameInScope schema filterParent
                  responseName liftParent rest]
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [scopedFieldSelectionsWithResponseNameInScope,
                  fieldSelectionsWithResponseNameInScope, hoverlap,
                  eraseScopedSelectionSet_append,
                  eraseScopedFieldSelectionsWithResponseNameInScope schema filterParent
                    responseName typeCondition selectionSet,
                  eraseScopedFieldSelectionsWithResponseNameInScope schema filterParent
                    responseName liftParent rest]
              · have hoverlapFalse :
                    schema.typesOverlapBool filterParent typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool filterParent typeCondition
                  · rfl
                  · exact False.elim (hoverlap hmatch)
                simp [scopedFieldSelectionsWithResponseNameInScope,
                  fieldSelectionsWithResponseNameInScope, hoverlapFalse,
                  eraseScopedFieldSelectionsWithResponseNameInScope schema filterParent
                    responseName liftParent rest]

theorem fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
    (schema : Schema) (filterParent responseName liftParent : Name) :
    ∀ selectionSet,
      fieldSelectionsWithResponseNameInScope schema filterParent responseName
        (groundLiftSelectionSet schema liftParent selectionSet)
      =
      groundLiftScopedSelectionSet schema
        (scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
          liftParent selectionSet)
  | [] => by
      simp [groundLiftSelectionSet, fieldSelectionsWithResponseNameInScope,
        scopedFieldSelectionsWithResponseNameInScope, groundLiftScopedSelectionSet]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField liftParent fieldName <;>
            by_cases hresponse : (fieldResponseName == responseName) = true <;>
              simp [groundLiftSelectionSet, groundLiftSelection, hlookup,
                fieldSelectionsWithResponseNameInScope,
                scopedFieldSelectionsWithResponseNameInScope, hresponse,
                groundLiftScopedSelectionSet, groundLiftScopedSelection,
                fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                  schema filterParent responseName liftParent rest]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [groundLiftSelectionSet, groundLiftSelection,
                fieldSelectionsWithResponseNameInScope,
                scopedFieldSelectionsWithResponseNameInScope,
                groundLiftScopedSelectionSet_append,
                fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                  schema filterParent responseName liftParent selectionSet,
                fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                  schema filterParent responseName liftParent rest]
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [groundLiftSelectionSet, groundLiftSelection,
                  fieldSelectionsWithResponseNameInScope,
                  scopedFieldSelectionsWithResponseNameInScope, hoverlap,
                  groundLiftScopedSelectionSet_append,
                  fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                    schema filterParent responseName typeCondition
                    selectionSet,
                  fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                    schema filterParent responseName liftParent rest]
              · have hoverlapFalse :
                    schema.typesOverlapBool filterParent typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool filterParent typeCondition
                  · rfl
                  · exact False.elim (hoverlap hmatch)
                simp [groundLiftSelectionSet, groundLiftSelection,
                  fieldSelectionsWithResponseNameInScope,
                  scopedFieldSelectionsWithResponseNameInScope, hoverlapFalse,
                  fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                    schema filterParent responseName liftParent rest]

def scopedSelectionSetFieldSelectionsWithResponseNameInScope
    (schema : Schema) (filterParent responseName : Name) :
    List ScopedSelection -> List ScopedSelection
  | [] => []
  | scopedSelection :: rest =>
      let restFields :=
        scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
          responseName rest
      match scopedSelection.selection with
      | .field fieldResponseName _fieldName _arguments _directives
          _selectionSet =>
          if fieldResponseName == responseName then
            scopedSelection :: restFields
          else
            restFields
      | .inlineFragment none _directives selectionSet =>
          scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
              scopedSelection.liftParent selectionSet
            ++ restFields
      | .inlineFragment (some typeCondition) _directives selectionSet =>
          if schema.typesOverlapBool filterParent typeCondition then
            scopedFieldSelectionsWithResponseNameInScope schema filterParent responseName
                typeCondition selectionSet
              ++ restFields
          else
            restFields

def scopedSelectionSetWithoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name) :
    List ScopedSelection -> List ScopedSelection
  | [] => []
  | scopedSelection :: rest =>
      let filteredRest :=
        scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
          rest
      match scopedSelection.selection with
      | .field fieldResponseName _fieldName _arguments _directives
          _selectionSet =>
          if fieldResponseName == responseName then
            filteredRest
          else
            scopedSelection :: filteredRest
      | .inlineFragment typeCondition directives selectionSet =>
          { scopedSelection with
            selection :=
              .inlineFragment typeCondition directives
                (withoutFieldSelectionsWithResponseName schema responseName
                  selectionSet) }
            :: filteredRest

theorem scopedSelectionSetFieldSelectionsWithResponseNameInScope_runtimeApplies
    (schema : Schema) (filterParent responseName runtimeType : Name) :
    ∀ scopedSelections,
      objectTypeNameBool schema filterParent = true ->
      schema.typeIncludesObjectBool filterParent runtimeType = true ->
      scopedSelectionSetRuntimeApplies schema runtimeType scopedSelections ->
        scopedSelectionSetRuntimeApplies schema runtimeType
          (scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
            responseName scopedSelections)
  | [], _hfilterObject, _hfilterInclude, _happlies => by
      simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
        scopedSelectionSetRuntimeApplies]
  | scopedSelection :: rest, hfilterObject, hfilterInclude, happlies => by
      have hheadApply :
          schema.typeIncludesObjectBool scopedSelection.liftParent runtimeType =
            true :=
        happlies scopedSelection (by simp)
      have htailApply :
          scopedSelectionSetRuntimeApplies schema runtimeType rest :=
        scopedSelectionSetRuntimeApplies_tail happlies
      have hrest :=
        scopedSelectionSetFieldSelectionsWithResponseNameInScope_runtimeApplies schema
          filterParent responseName runtimeType rest hfilterObject
          hfilterInclude htailApply
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              subselections =>
              by_cases hresponse :
                  (fieldResponseName == responseName) = true
              · intro candidate hcandidate
                simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                  hresponse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  exact hheadApply
                · exact hrest candidate hcandidate
              · have hfalse :
                    (fieldResponseName == responseName) = false := by
                  cases hmatch : fieldResponseName == responseName
                  · rfl
                  · exact False.elim (hresponse hmatch)
                simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                  hfalse] using hrest
          | inlineFragment typeCondition directives subselections =>
              cases typeCondition with
              | none =>
                  have hbody :=
                    scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                      filterParent responseName liftParent runtimeType
                      subselections hfilterObject hfilterInclude hheadApply
                  simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope] using
                    scopedSelectionSetRuntimeApplies_append hbody hrest
              | some typeCondition =>
                  by_cases hoverlap :
                      schema.typesOverlapBool filterParent typeCondition =
                        true
                  · have hbody :=
                      scopedFieldSelectionsWithResponseNameInScope_runtimeApplies schema
                        filterParent responseName typeCondition runtimeType
                        subselections hfilterObject hfilterInclude
                        (by
                          have hfilterObjectProp :
                              schema.objectType filterParent :=
                            objectType_of_objectTypeNameBool_eq_true schema
                              hfilterObject
                          have hruntimeEq : runtimeType = filterParent :=
                            object_typeIncludesObjectBool_eq_self schema
                              hfilterObjectProp hfilterInclude
                          subst runtimeType
                          exact
                            typeIncludesObjectBool_of_object_typesOverlapBool
                              schema hfilterObjectProp hoverlap)
                    simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                      hoverlap] using
                      scopedSelectionSetRuntimeApplies_append hbody hrest
                  · have hfalse :
                        schema.typesOverlapBool filterParent typeCondition =
                          false := by
                      cases hmatch :
                          schema.typesOverlapBool filterParent typeCondition
                      · rfl
                      · exact False.elim (hoverlap hmatch)
                    simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                      hfalse] using hrest

theorem scopedSelectionSetFieldSelectionsWithResponseNameInScope_lookupValid
    (schema : Schema) (filterParent responseName : Name) :
    ∀ scopedSelections,
      scopedSelectionSetLookupValid schema scopedSelections ->
        scopedSelectionSetLookupValid schema
          (scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
            responseName scopedSelections)
  | [], _hvalid => by
      simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
        scopedSelectionSetLookupValid]
  | scopedSelection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema scopedSelection.liftParent
            scopedSelection.selection :=
        hvalid scopedSelection (by simp)
      have htailValid :
          scopedSelectionSetLookupValid schema rest :=
        scopedSelectionSetLookupValid_tail hvalid
      have hrest :=
        scopedSelectionSetFieldSelectionsWithResponseNameInScope_lookupValid schema
          filterParent responseName rest htailValid
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              subselections =>
              by_cases hresponse :
                  (fieldResponseName == responseName) = true
              · intro candidate hcandidate
                simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                  hresponse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  exact hheadValid
                · exact hrest candidate hcandidate
              · have hfalse :
                    (fieldResponseName == responseName) = false := by
                  cases hmatch : fieldResponseName == responseName
                  · rfl
                  · exact False.elim (hresponse hmatch)
                simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                  hfalse] using hrest
          | inlineFragment typeCondition directives subselections =>
              cases typeCondition with
              | none =>
                  have hbodyValid :
                      selectionSetLookupValid schema liftParent
                        subselections := by
                    simpa [selectionLookupValid] using hheadValid
                  have hbody :=
                    scopedFieldSelectionsWithResponseNameInScope_lookupValid schema
                      filterParent responseName liftParent subselections
                      hbodyValid
                  simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope] using
                    scopedSelectionSetLookupValid_append hbody hrest
              | some typeCondition =>
                  have hbodyValid :
                      selectionSetLookupValid schema typeCondition
                        subselections := by
                    simpa [selectionLookupValid] using hheadValid
                  by_cases hoverlap :
                      schema.typesOverlapBool filterParent typeCondition =
                        true
                  · have hbody :=
                      scopedFieldSelectionsWithResponseNameInScope_lookupValid schema
                        filterParent responseName typeCondition subselections
                        hbodyValid
                    simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                      hoverlap] using
                      scopedSelectionSetLookupValid_append hbody hrest
                  · have hfalse :
                        schema.typesOverlapBool filterParent typeCondition =
                          false := by
                      cases hmatch :
                          schema.typesOverlapBool filterParent typeCondition
                      · rfl
                      · exact False.elim (hoverlap hmatch)
                    simpa [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                      hfalse] using hrest

theorem scopedSelectionSetWithoutFieldSelectionsWithResponseName_runtimeApplies
    (schema : Schema) (responseName runtimeType : Name) :
    ∀ scopedSelections,
      scopedSelectionSetRuntimeApplies schema runtimeType scopedSelections ->
        scopedSelectionSetRuntimeApplies schema runtimeType
          (scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
            scopedSelections)
  | [], _happlies => by
      simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
        scopedSelectionSetRuntimeApplies]
  | scopedSelection :: rest, happlies => by
      have hheadApply :
          schema.typeIncludesObjectBool scopedSelection.liftParent runtimeType =
            true :=
        happlies scopedSelection (by simp)
      have htailApply :
          scopedSelectionSetRuntimeApplies schema runtimeType rest :=
        scopedSelectionSetRuntimeApplies_tail happlies
      have hrest :=
        scopedSelectionSetWithoutFieldSelectionsWithResponseName_runtimeApplies schema
          responseName runtimeType rest htailApply
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              subselections =>
              by_cases hresponse :
                  (fieldResponseName == responseName) = true
              · simpa [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                  hresponse] using hrest
              · have hfalse :
                    (fieldResponseName == responseName) = false := by
                  cases hmatch : fieldResponseName == responseName
                  · rfl
                  · exact False.elim (hresponse hmatch)
                intro candidate hcandidate
                simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                  hfalse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  exact hheadApply
                · exact hrest candidate hcandidate
          | inlineFragment typeCondition directives subselections =>
              intro candidate hcandidate
              simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName] at hcandidate
              rcases hcandidate with hcandidate | hcandidate
              · subst candidate
                exact hheadApply
              · exact hrest candidate hcandidate

theorem eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope
    (schema : Schema) (filterParent responseName : Name) :
    ∀ scopedSelections,
      eraseScopedSelectionSet
          (scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
            responseName scopedSelections)
        =
      fieldSelectionsWithResponseNameInScope schema filterParent responseName
        (eraseScopedSelectionSet scopedSelections)
  | [] => by
      simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
        eraseScopedSelectionSet, fieldSelectionsWithResponseNameInScope]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              selectionSet =>
              by_cases hresponse :
                  (fieldResponseName == responseName) = true
              · simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                  fieldSelectionsWithResponseNameInScope, hresponse,
                  eraseScopedSelectionSet, eraseScopedSelection,
                  eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope schema
                    filterParent responseName rest]
              · have hfalse :
                    (fieldResponseName == responseName) = false := by
                  cases hmatch : fieldResponseName == responseName
                  · rfl
                  · exact False.elim (hresponse hmatch)
                simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                  fieldSelectionsWithResponseNameInScope, hfalse,
                  eraseScopedSelectionSet, eraseScopedSelection,
                  eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope schema
                    filterParent responseName rest]
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                    fieldSelectionsWithResponseNameInScope,
                    eraseScopedSelectionSet, eraseScopedSelection,
                    eraseScopedSelectionSet_append,
                    eraseScopedFieldSelectionsWithResponseNameInScope schema
                      filterParent responseName liftParent selectionSet,
                    eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope schema
                      filterParent responseName rest]
              | some typeCondition =>
                  by_cases hoverlap :
                      schema.typesOverlapBool filterParent typeCondition =
                        true
                  · simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                      fieldSelectionsWithResponseNameInScope, hoverlap,
                      eraseScopedSelectionSet, eraseScopedSelection,
                      eraseScopedSelectionSet_append,
                      eraseScopedFieldSelectionsWithResponseNameInScope schema
                        filterParent responseName typeCondition selectionSet,
                      eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope
                        schema filterParent responseName rest]
                  · have hoverlapFalse :
                        schema.typesOverlapBool filterParent typeCondition =
                          false := by
                      cases hmatch :
                          schema.typesOverlapBool filterParent typeCondition
                      · rfl
                      · exact False.elim (hoverlap hmatch)
                    simp [scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                      fieldSelectionsWithResponseNameInScope, hoverlapFalse,
                      eraseScopedSelectionSet, eraseScopedSelection,
                      eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope
                      schema filterParent responseName rest]

theorem scopedSelectionSetFieldSelectionsWithResponseNameInScope_mem_field
    (schema : Schema) (filterParent responseName : Name)
    (scopedSelections : List ScopedSelection)
    (scopedSelection : ScopedSelection) :
    scopedSelection ∈
        scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
          responseName scopedSelections ->
      ∃ fieldName arguments directives subselections,
        scopedSelection.selection =
          Selection.field responseName fieldName arguments directives
            subselections := by
  intro hscoped
  have hselectionMem :
      scopedSelection.selection ∈
        eraseScopedSelectionSet
          (scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
            responseName scopedSelections) :=
    eraseScopedSelectionSet_mem_selection hscoped
  rw [eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope schema
    filterParent responseName scopedSelections] at hselectionMem
  exact fieldSelectionsWithResponseNameInScope_mem_field schema filterParent
    responseName (eraseScopedSelectionSet scopedSelections)
    scopedSelection.selection hselectionMem

theorem fieldSelectionsWithResponseNameInScope_groundLiftScopedSelectionSet
    (schema : Schema) (filterParent responseName : Name) :
    ∀ scopedSelections,
      fieldSelectionsWithResponseNameInScope schema filterParent responseName
        (groundLiftScopedSelectionSet schema scopedSelections)
      =
      groundLiftScopedSelectionSet schema
        (scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
          responseName scopedSelections)
  | [] => by
      simp [groundLiftScopedSelectionSet,
        scopedSelectionSetFieldSelectionsWithResponseNameInScope,
        fieldSelectionsWithResponseNameInScope]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              selectionSet =>
              cases hlookup : schema.lookupField liftParent fieldName <;>
                by_cases hresponse :
                    (fieldResponseName == responseName) = true <;>
                  simp [groundLiftScopedSelectionSet, groundLiftScopedSelection,
                    groundLiftSelection,
                    scopedSelectionSetFieldSelectionsWithResponseNameInScope, hlookup,
                    fieldSelectionsWithResponseNameInScope, hresponse,
                    fieldSelectionsWithResponseNameInScope_groundLiftScopedSelectionSet
                      schema filterParent responseName rest]
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  simp [groundLiftScopedSelectionSet, groundLiftScopedSelection,
                    groundLiftSelection, fieldSelectionsWithResponseNameInScope,
                    scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                    groundLiftScopedSelectionSet_append,
                    fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                      schema filterParent responseName liftParent
                      selectionSet,
                    fieldSelectionsWithResponseNameInScope_groundLiftScopedSelectionSet
                      schema filterParent responseName rest]
              | some typeCondition =>
                  by_cases hoverlap :
                      schema.typesOverlapBool filterParent typeCondition =
                        true
                  · simp [groundLiftScopedSelectionSet,
                      groundLiftScopedSelection, groundLiftSelection,
                      fieldSelectionsWithResponseNameInScope,
                      scopedSelectionSetFieldSelectionsWithResponseNameInScope, hoverlap,
                      groundLiftScopedSelectionSet_append,
                      fieldSelectionsWithResponseNameInScope_groundLiftSelectionSet_scoped
                        schema filterParent responseName typeCondition
                        selectionSet,
                      fieldSelectionsWithResponseNameInScope_groundLiftScopedSelectionSet
                        schema filterParent responseName rest]
                  · have hoverlapFalse :
                        schema.typesOverlapBool filterParent typeCondition =
                          false := by
                      cases hmatch :
                          schema.typesOverlapBool filterParent typeCondition
                      · rfl
                      · exact False.elim (hoverlap hmatch)
                    simp [groundLiftScopedSelectionSet,
                      groundLiftScopedSelection, groundLiftSelection,
                      fieldSelectionsWithResponseNameInScope,
                      scopedSelectionSetFieldSelectionsWithResponseNameInScope,
                      hoverlapFalse,
                      fieldSelectionsWithResponseNameInScope_groundLiftScopedSelectionSet
                        schema filterParent responseName rest]

theorem eraseScopedSelectionSet_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name) :
    ∀ scopedSelections,
      eraseScopedSelectionSet
          (scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
            scopedSelections)
        =
      withoutFieldSelectionsWithResponseName schema responseName
        (eraseScopedSelectionSet scopedSelections)
  | [] => by
      simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
        eraseScopedSelectionSet, withoutFieldSelectionsWithResponseName]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              selectionSet =>
              by_cases hresponse :
                  (fieldResponseName == responseName) = true
              · simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                  withoutFieldSelectionsWithResponseName, hresponse,
                  eraseScopedSelectionSet, eraseScopedSelection,
                  eraseScopedSelectionSet_withoutFieldSelectionsWithResponseName schema
                    responseName rest]
              · have hfalse :
                    (fieldResponseName == responseName) = false := by
                  cases hmatch : fieldResponseName == responseName
                  · rfl
                  · exact False.elim (hresponse hmatch)
                simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                  withoutFieldSelectionsWithResponseName, hfalse,
                  eraseScopedSelectionSet, eraseScopedSelection,
                  eraseScopedSelectionSet_withoutFieldSelectionsWithResponseName schema
                    responseName rest]
          | inlineFragment typeCondition directives selectionSet =>
              simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                withoutFieldSelectionsWithResponseName, eraseScopedSelectionSet,
                eraseScopedSelection,
                eraseScopedSelectionSet_withoutFieldSelectionsWithResponseName schema
                  responseName rest]

theorem groundLiftScopedSelectionSet_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name) :
    ∀ scopedSelections,
      groundLiftScopedSelectionSet schema
          (scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
            scopedSelections)
        =
      withoutFieldSelectionsWithResponseName schema responseName
        (groundLiftScopedSelectionSet schema scopedSelections)
  | [] => by
      simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
        groundLiftScopedSelectionSet, withoutFieldSelectionsWithResponseName]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              selectionSet =>
              cases hlookup : schema.lookupField liftParent fieldName <;>
                by_cases hresponse :
                    (fieldResponseName == responseName) = true <;>
                  simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                    groundLiftScopedSelectionSet, groundLiftScopedSelection,
                    groundLiftSelection, withoutFieldSelectionsWithResponseName,
                    hlookup, hresponse,
                    groundLiftScopedSelectionSet_withoutFieldSelectionsWithResponseName
                      schema responseName rest]
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                    groundLiftScopedSelectionSet, groundLiftScopedSelection,
                    groundLiftSelection, withoutFieldSelectionsWithResponseName,
                    withoutFieldSelectionsWithResponseName_groundLiftSelectionSet schema
                      responseName liftParent selectionSet,
                    groundLiftScopedSelectionSet_withoutFieldSelectionsWithResponseName
                      schema responseName rest]
              | some typeCondition =>
                  simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                    groundLiftScopedSelectionSet, groundLiftScopedSelection,
                    groundLiftSelection, withoutFieldSelectionsWithResponseName,
                    withoutFieldSelectionsWithResponseName_groundLiftSelectionSet schema
                      responseName typeCondition selectionSet,
                    groundLiftScopedSelectionSet_withoutFieldSelectionsWithResponseName
                      schema responseName rest]

theorem groundLiftScopedSelectionSet_directiveFree
    (schema : Schema) :
    ∀ scopedSelections,
      scopedSelectionSetDirectiveFree scopedSelections ->
        selectionSetDirectiveFree
          (groundLiftScopedSelectionSet schema scopedSelections)
  | [], _hfree => by
      simp [groundLiftScopedSelectionSet, selectionSetDirectiveFree]
  | scopedSelection :: rest, hfree => by
      have hheadFree :
          selectionDirectiveFree scopedSelection.selection := by
        simpa [scopedSelectionSetDirectiveFree, eraseScopedSelectionSet,
          eraseScopedSelection] using selectionSetDirectiveFree_head
          (selection := eraseScopedSelection scopedSelection)
          (selectionSet := eraseScopedSelectionSet rest) hfree
      have htailFree :
          scopedSelectionSetDirectiveFree rest :=
        scopedSelectionSetDirectiveFree_tail hfree
      cases scopedSelection with
      | mk liftParent selection =>
          exact ⟨
            groundLiftSelection_directiveFree schema liftParent selection
              hheadFree,
            groundLiftScopedSelectionSet_directiveFree schema rest
              htailFree⟩

theorem scopedSelectionSetFieldSelectionsWithResponseNameInScope_directiveFree
    (schema : Schema) (filterParent responseName : Name)
    (scopedSelections : List ScopedSelection) :
    scopedSelectionSetDirectiveFree scopedSelections ->
      scopedSelectionSetDirectiveFree
        (scopedSelectionSetFieldSelectionsWithResponseNameInScope schema filterParent
          responseName scopedSelections) := by
  intro hfree
  have hvalid :
      selectionSetDirectiveFree
        (fieldSelectionsWithResponseNameInScope schema filterParent responseName
          (eraseScopedSelectionSet scopedSelections)) :=
    fieldSelectionsWithResponseNameInScope_directiveFree schema filterParent
      responseName (eraseScopedSelectionSet scopedSelections) hfree
  simpa [scopedSelectionSetDirectiveFree,
    eraseScopedSelectionSet_fieldSelectionsWithResponseNameInScope schema filterParent
      responseName scopedSelections] using hvalid

theorem scopedSelectionSetWithoutFieldSelectionsWithResponseName_directiveFree
    (schema : Schema) (responseName : Name)
    (scopedSelections : List ScopedSelection) :
    scopedSelectionSetDirectiveFree scopedSelections ->
      scopedSelectionSetDirectiveFree
        (scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
          scopedSelections) := by
  intro hfree
  have hfiltered :
      selectionSetDirectiveFree
        (withoutFieldSelectionsWithResponseName schema responseName
          (eraseScopedSelectionSet scopedSelections)) :=
    withoutFieldSelectionsWithResponseName_directiveFree schema responseName
      (eraseScopedSelectionSet scopedSelections) hfree
  simpa [scopedSelectionSetDirectiveFree,
    eraseScopedSelectionSet_withoutFieldSelectionsWithResponseName schema responseName
      scopedSelections] using hfiltered

theorem scopedSelectionSetWithoutFieldSelectionsWithResponseName_semanticsReady
    (schema : Schema) (execParent responseName : Name)
    (scopedSelections : List ScopedSelection) :
    scopedSelectionSetSemanticsReady schema execParent scopedSelections ->
      scopedSelectionSetSemanticsReady schema execParent
        (scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
          scopedSelections) := by
  intro hready
  have hfiltered :
      selectionSetSemanticsReady schema execParent
        (withoutFieldSelectionsWithResponseName schema responseName
          (eraseScopedSelectionSet scopedSelections)) :=
    selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
      responseName execParent (eraseScopedSelectionSet scopedSelections)
      hready
  simpa [scopedSelectionSetSemanticsReady,
    eraseScopedSelectionSet_withoutFieldSelectionsWithResponseName schema responseName
      scopedSelections] using hfiltered

theorem scopedSelectionSetWithoutFieldSelectionsWithResponseName_lookupValid
    (schema : Schema) (responseName : Name) :
    ∀ scopedSelections,
      scopedSelectionSetLookupValid schema scopedSelections ->
        scopedSelectionSetLookupValid schema
          (scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
            scopedSelections)
  | [], _hvalid => by
      simp [scopedSelectionSetLookupValid,
        scopedSelectionSetWithoutFieldSelectionsWithResponseName]
  | scopedSelection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema scopedSelection.liftParent
            scopedSelection.selection :=
        hvalid scopedSelection (by simp)
      have htailValid :
          scopedSelectionSetLookupValid schema rest :=
        scopedSelectionSetLookupValid_tail hvalid
      cases scopedSelection with
      | mk liftParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives
              selectionSet =>
              by_cases hresponse :
                  (fieldResponseName == responseName) = true
              · simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                  hresponse]
                exact
                  scopedSelectionSetWithoutFieldSelectionsWithResponseName_lookupValid
                    schema responseName rest htailValid
              · have hfalse :
                    (fieldResponseName == responseName) = false := by
                  cases hmatch : fieldResponseName == responseName
                  · rfl
                  · exact False.elim (hresponse hmatch)
                intro candidate hcandidate
                simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName,
                  hfalse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  simpa [selectionLookupValid] using hheadValid
                · exact
                    scopedSelectionSetWithoutFieldSelectionsWithResponseName_lookupValid
                      schema responseName rest htailValid candidate
                      hcandidate
          | inlineFragment typeCondition directives selectionSet =>
              intro candidate hcandidate
              simp [scopedSelectionSetWithoutFieldSelectionsWithResponseName] at hcandidate
              rcases hcandidate with hcandidate | hcandidate
              · subst candidate
                cases typeCondition with
                | none =>
                    simpa [selectionLookupValid] using
                      selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                        schema responseName liftParent selectionSet
                        (by simpa [selectionLookupValid] using hheadValid)
                | some typeCondition =>
                    simpa [selectionLookupValid] using
                      selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                        schema responseName typeCondition selectionSet
                        (by simpa [selectionLookupValid] using hheadValid)
              · exact
                  scopedSelectionSetWithoutFieldSelectionsWithResponseName_lookupValid
                    schema responseName rest htailValid candidate hcandidate

theorem scopedSelectionSetWithoutFieldSelectionsWithResponseName_canMerge
    (schema : Schema) (execParent responseName : Name)
    (scopedSelections : List ScopedSelection) :
    scopedSelectionSetCanMerge schema execParent scopedSelections ->
      scopedSelectionSetCanMerge schema execParent
        (scopedSelectionSetWithoutFieldSelectionsWithResponseName schema responseName
          scopedSelections) := by
  intro hmerge
  have hfiltered :
      FieldMerge.fieldsInSetCanMerge schema execParent
        (withoutFieldSelectionsWithResponseName schema responseName
          (eraseScopedSelectionSet scopedSelections)) :=
    fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema responseName
      execParent (eraseScopedSelectionSet scopedSelections) hmerge
  simpa [scopedSelectionSetCanMerge,
    eraseScopedSelectionSet_withoutFieldSelectionsWithResponseName schema responseName
      scopedSelections] using hfiltered

theorem scopedFieldHead_lookupPair_of_semanticsReady_lookupValid
    (schema : Schema)
    (execParent liftParent responseName fieldName : Name)
    (arguments : List Argument)
    (subselections : List Selection) (rest : List ScopedSelection) :
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
      ∃ execFieldDefinition liftFieldDefinition,
        schema.lookupField execParent fieldName = some execFieldDefinition
          ∧ schema.lookupField liftParent fieldName = some liftFieldDefinition := by
  intro hready hlookupValid
  have hheadReady :
      selectionSemanticsReady schema execParent
        (Selection.field responseName fieldName arguments [] subselections) := by
    unfold scopedSelectionSetSemanticsReady at hready
    unfold selectionSetSemanticsReady at hready
    exact hready _ (by simp [eraseScopedSelectionSet, eraseScopedSelection])
  have hheadLookup :
      selectionLookupValid schema liftParent
        (Selection.field responseName fieldName arguments [] subselections) :=
    hlookupValid
      { liftParent := liftParent,
        selection :=
          Selection.field responseName fieldName arguments [] subselections }
      (by simp)
  simp [selectionSemanticsReady] at hheadReady
  simp [selectionLookupValid] at hheadLookup
  rcases hheadReady with ⟨execFieldDefinition, hexecLookup, _hchildren⟩
  rcases hheadLookup with ⟨liftFieldDefinition, hliftLookup⟩
  exact ⟨execFieldDefinition, liftFieldDefinition, hexecLookup, hliftLookup⟩

end GroundTypeLifting

end NormalForm

end GraphQL
