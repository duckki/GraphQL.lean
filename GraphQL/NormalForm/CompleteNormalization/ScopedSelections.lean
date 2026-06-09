import GraphQL.NormalForm.CompleteNormalization.StaticCollection
import GraphQL.NormalForm.GroundTypeNormalization.SemanticReadiness

/-!
Scoped selection-set machinery for complete-normalization proofs.

The executable normalizer keeps the public API unscoped. This proof layer makes
the per-selection lookup context explicit, which is needed when merged response
groups contain fields collected through different typed inline fragments.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

open GroundTypeNormalization

structure CompleteScopedSelection where
  lookupParent : Name
  selection : Selection

def completeScopedSelectionSet (lookupParent : Name) :
    List Selection -> List CompleteScopedSelection
  | [] => []
  | selection :: rest =>
      { lookupParent := lookupParent, selection := selection }
        :: completeScopedSelectionSet lookupParent rest

def eraseCompleteScopedSelection :
    CompleteScopedSelection -> Selection
  | scopedSelection => scopedSelection.selection

def eraseCompleteScopedSelectionSet :
    List CompleteScopedSelection -> List Selection
  | [] => []
  | scopedSelection :: rest =>
      eraseCompleteScopedSelection scopedSelection
        :: eraseCompleteScopedSelectionSet rest

theorem eraseCompleteScopedSelectionSet_mem_of_mem
    {scopedSelection : CompleteScopedSelection}
    {scopedSelections : List CompleteScopedSelection} :
    scopedSelection ∈ scopedSelections ->
      scopedSelection.selection ∈
        eraseCompleteScopedSelectionSet scopedSelections := by
  intro hmem
  induction scopedSelections with
  | nil =>
      cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst scopedSelection
        simp [eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection]
      · exact List.mem_cons_of_mem (eraseCompleteScopedSelection head)
          (ih htail)

def staticCollectCompleteScopedSelection
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (boolCase : BoolCase) :
    CompleteScopedSelection -> List Selection
  | scopedSelection =>
      staticCollectForGround schema variables
        scopedSelection.lookupParent groundType boolCase
        [scopedSelection.selection]

def staticCollectCompleteScopedSelectionSet
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (boolCase : BoolCase) :
    List CompleteScopedSelection -> List Selection
  | [] => []
  | scopedSelection :: rest =>
      staticCollectCompleteScopedSelection schema variables groundType
        boolCase scopedSelection
        ++ staticCollectCompleteScopedSelectionSet schema variables
          groundType boolCase rest

def completeScopedSelectionRuntimeReady
    (schema : Schema) (boolCase : BoolCase)
    (runtimeType : Name) (scopedSelection : CompleteScopedSelection) : Prop :=
  match scopedSelection.selection with
  | .field _responseName fieldName _arguments directives _selectionSet =>
      directivesAllowIn boolCase directives = true
        ∧ ∃ fieldDefinition,
          schema.lookupField scopedSelection.lookupParent fieldName =
            some fieldDefinition
          ∧ leafTypeNameBool schema fieldDefinition.outputType.namedType =
            false
          ∧ runtimeType ∈
            groundObjectTypesForType schema
              fieldDefinition.outputType.namedType
  | .inlineFragment _typeCondition _directives _selectionSet => False

theorem eraseCompleteScopedSelectionSet_append :
    ∀ left right : List CompleteScopedSelection,
      eraseCompleteScopedSelectionSet (left ++ right)
        =
      eraseCompleteScopedSelectionSet left
        ++ eraseCompleteScopedSelectionSet right
  | [], right => by
      simp [eraseCompleteScopedSelectionSet]
  | scopedSelection :: rest, right => by
      simp [eraseCompleteScopedSelectionSet,
        eraseCompleteScopedSelectionSet_append rest right]

theorem staticCollectCompleteScopedSelectionSet_append
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (boolCase : BoolCase) :
    ∀ left right : List CompleteScopedSelection,
      staticCollectCompleteScopedSelectionSet schema variables groundType
          boolCase (left ++ right)
        =
      staticCollectCompleteScopedSelectionSet schema variables groundType
          boolCase left
        ++ staticCollectCompleteScopedSelectionSet schema variables groundType
          boolCase right
  | [], right => by
      simp [staticCollectCompleteScopedSelectionSet]
  | scopedSelection :: rest, right => by
      simp [staticCollectCompleteScopedSelectionSet,
        staticCollectCompleteScopedSelectionSet_append schema variables
          groundType boolCase rest right, List.append_assoc]

theorem eraseCompleteScopedSelectionSet_completeScopedSelectionSet
    (lookupParent : Name) :
    ∀ selectionSet,
      eraseCompleteScopedSelectionSet
          (completeScopedSelectionSet lookupParent selectionSet)
        =
      selectionSet
  | [] => by
      simp [eraseCompleteScopedSelectionSet, completeScopedSelectionSet]
  | selection :: rest => by
      simp [eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
        completeScopedSelectionSet,
        eraseCompleteScopedSelectionSet_completeScopedSelectionSet
          lookupParent rest]

theorem completeScopedSelectionSet_lookupParent_eq
    {lookupParent : Name} {scopedSelection : CompleteScopedSelection} :
    ∀ {selectionSet : List Selection},
      scopedSelection ∈ completeScopedSelectionSet lookupParent selectionSet ->
        scopedSelection.lookupParent = lookupParent
  | [], hmem => by
      cases hmem
  | selection :: rest, hmem => by
      simp [completeScopedSelectionSet] at hmem
      rcases hmem with hhead | htail
      · subst scopedSelection
        rfl
      · exact completeScopedSelectionSet_lookupParent_eq htail

theorem staticCollectCompleteScopedSelectionSet_completeScopedSelectionSet
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name) (boolCase : BoolCase) :
    ∀ selectionSet,
      staticCollectCompleteScopedSelectionSet schema variables groundType
          boolCase
          (completeScopedSelectionSet lookupParent selectionSet)
        =
      staticCollectForGround schema variables lookupParent
        groundType boolCase selectionSet
  | [] => by
      simp [staticCollectCompleteScopedSelectionSet,
        completeScopedSelectionSet, staticCollectForGround]
  | selection :: rest => by
      have happend :=
        staticCollectForGround_append schema variables
          lookupParent groundType boolCase [selection] rest
      simp [staticCollectCompleteScopedSelectionSet,
        staticCollectCompleteScopedSelection,
        completeScopedSelectionSet,
        staticCollectCompleteScopedSelectionSet_completeScopedSelectionSet
          schema variables lookupParent groundType boolCase rest]
      simpa using happend.symm

theorem completeSelectionSet_size_append (left right : List Selection) :
    SelectionSet.size (left ++ right)
      =
    SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

theorem eraseCompleteScopedSelectionSet_completeScopedSelectionSet_size
    (lookupParent : Name) (selectionSet : List Selection) :
    SelectionSet.size
        (eraseCompleteScopedSelectionSet
          (completeScopedSelectionSet lookupParent selectionSet))
      =
    SelectionSet.size selectionSet := by
  rw [eraseCompleteScopedSelectionSet_completeScopedSelectionSet]

theorem eraseCompleteScopedSelectionSet_tail_size_lt
    (scopedSelection : CompleteScopedSelection)
    (rest : List CompleteScopedSelection) :
    SelectionSet.size (eraseCompleteScopedSelectionSet rest)
      <
    SelectionSet.size
      (eraseCompleteScopedSelectionSet (scopedSelection :: rest)) := by
  cases scopedSelection with
  | mk lookupParent selection =>
      cases selection <;>
        simp [eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
          SelectionSet.size, Selection.size] <;>
        omega

theorem eraseCompleteScopedSelectionSet_inlineFragment_none_flatten_size_lt
    (lookupParent : Name) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection) :
    SelectionSet.size
        (eraseCompleteScopedSelectionSet
          (completeScopedSelectionSet lookupParent selectionSet ++ rest))
      <
    SelectionSet.size
      (eraseCompleteScopedSelectionSet
        ({ lookupParent := lookupParent,
           selection := Selection.inlineFragment none [] selectionSet }
          :: rest)) := by
  simp [eraseCompleteScopedSelectionSet_append,
    eraseCompleteScopedSelectionSet_completeScopedSelectionSet,
    eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
    completeSelectionSet_size_append, SelectionSet.size, Selection.size]

theorem eraseCompleteScopedSelectionSet_inlineFragment_some_flatten_size_lt
    (lookupParent typeCondition : Name) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection) :
    SelectionSet.size
        (eraseCompleteScopedSelectionSet
          (completeScopedSelectionSet typeCondition selectionSet ++ rest))
      <
    SelectionSet.size
      (eraseCompleteScopedSelectionSet
        ({ lookupParent := lookupParent,
           selection :=
            Selection.inlineFragment (some typeCondition) [] selectionSet }
          :: rest)) := by
  simp [eraseCompleteScopedSelectionSet_append,
    eraseCompleteScopedSelectionSet_completeScopedSelectionSet,
    eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
    completeSelectionSet_size_append, SelectionSet.size, Selection.size]

theorem completeSize_withoutFieldsWithResponseName_le
    (schema : Schema) (responseName : Name) :
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
            completeSize_withoutFieldsWithResponseName_le schema responseName
              rest
          cases hresponse : fieldResponseName == responseName <;>
            simp [withoutFieldsWithResponseName, hresponse, SelectionSet.size,
              Selection.size] <;>
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            completeSize_withoutFieldsWithResponseName_le schema responseName
              selectionSet
          have hrest :=
            completeSize_withoutFieldsWithResponseName_le schema responseName
              rest
          cases typeCondition <;>
            simp [withoutFieldsWithResponseName, SelectionSet.size,
              Selection.size] <;>
            omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem validFieldsWithResponseName_append
    (schema : Schema) (parentType responseName : Name) :
    ∀ left right,
      validFieldsWithResponseName schema parentType responseName
          (left ++ right)
        =
      validFieldsWithResponseName schema parentType responseName left
        ++ validFieldsWithResponseName schema parentType responseName right
  | [], right => by
      simp [validFieldsWithResponseName]
  | selection :: rest, right => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hresponse : fieldResponseName == responseName <;>
            simp [validFieldsWithResponseName, hresponse,
              validFieldsWithResponseName_append schema parentType
                responseName rest right]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [validFieldsWithResponseName,
                validFieldsWithResponseName_append schema parentType
                  responseName rest right,
                List.append_assoc]
          | some typeCondition =>
              cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition <;>
                simp [validFieldsWithResponseName, hoverlap,
                  validFieldsWithResponseName_append schema parentType
                    responseName rest right,
                  List.append_assoc]

def completeScopedSelectionSetLookupValid
    (schema : Schema) (scopedSelections : List CompleteScopedSelection) :
    Prop :=
  ∀ scopedSelection, scopedSelection ∈ scopedSelections ->
    selectionLookupValid schema scopedSelection.lookupParent
      scopedSelection.selection

theorem completeScopedSelectionSetLookupValid_completeScopedSelectionSet
    (schema : Schema) (lookupParent : Name) :
    ∀ selectionSet,
      completeScopedSelectionSetLookupValid schema
          (completeScopedSelectionSet lookupParent selectionSet)
        ↔
      selectionSetLookupValid schema lookupParent selectionSet
  | [] => by
      simp [completeScopedSelectionSetLookupValid,
        completeScopedSelectionSet, selectionSetLookupValid]
  | selection :: rest => by
      constructor
      · intro hvalid
        have hhead :
            selectionLookupValid schema lookupParent selection := by
          exact hvalid { lookupParent := lookupParent, selection := selection }
            (by simp [completeScopedSelectionSet])
        have htail :
            selectionSetLookupValid schema lookupParent rest := by
          exact
            (completeScopedSelectionSetLookupValid_completeScopedSelectionSet
              schema lookupParent rest).mp
              (by
                intro scopedSelection hmem
                exact hvalid scopedSelection
                  (by simp [completeScopedSelectionSet, hmem]))
        unfold selectionSetLookupValid
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hhead
        · unfold selectionSetLookupValid at htail
          exact htail candidate hcandidate
      · intro hvalid scopedSelection hmem
        simp [completeScopedSelectionSet] at hmem
        rcases hmem with hhead | htail
        · subst scopedSelection
          unfold selectionSetLookupValid at hvalid
          exact hvalid selection (by simp)
        · exact
            (completeScopedSelectionSetLookupValid_completeScopedSelectionSet
              schema lookupParent rest).mpr
              (selectionSetLookupValid_tail hvalid)
              scopedSelection htail

theorem completeScopedSelectionSetLookupValid_append
    {schema : Schema} {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetLookupValid schema left ->
      completeScopedSelectionSetLookupValid schema right ->
        completeScopedSelectionSetLookupValid schema (left ++ right) := by
  intro hleft hright scopedSelection hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft scopedSelection hmem
  · exact hright scopedSelection hmem

theorem completeScopedSelectionSetLookupValid_append_left
    {schema : Schema} {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetLookupValid schema (left ++ right) ->
      completeScopedSelectionSetLookupValid schema left := by
  intro hvalid scopedSelection hmem
  exact hvalid scopedSelection (List.mem_append.mpr (Or.inl hmem))

theorem completeScopedSelectionSetLookupValid_append_right
    {schema : Schema} {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetLookupValid schema (left ++ right) ->
      completeScopedSelectionSetLookupValid schema right := by
  intro hvalid scopedSelection hmem
  exact hvalid scopedSelection (List.mem_append.mpr (Or.inr hmem))

theorem completeScopedSelectionSetLookupValid_tail
    {schema : Schema} {scopedSelection : CompleteScopedSelection}
    {rest : List CompleteScopedSelection} :
    completeScopedSelectionSetLookupValid schema (scopedSelection :: rest) ->
      completeScopedSelectionSetLookupValid schema rest := by
  intro hvalid candidate hcandidate
  exact hvalid candidate (List.mem_cons_of_mem scopedSelection hcandidate)

def completeScopedSelectionSetGroundApplies
    (schema : Schema) (groundType : Name)
    (scopedSelections : List CompleteScopedSelection) : Prop :=
  ∀ scopedSelection, scopedSelection ∈ scopedSelections ->
    schema.typeIncludesObjectBool scopedSelection.lookupParent groundType =
      true

def completeScopedSelectionSetSemanticsReady
    (schema : Schema) (execParent : Name)
    (scopedSelections : List CompleteScopedSelection) : Prop :=
  selectionSetSemanticsReady schema execParent
    (eraseCompleteScopedSelectionSet scopedSelections)

def completeScopedSelectionSetCanMerge
    (schema : Schema) (execParent : Name)
    (scopedSelections : List CompleteScopedSelection) : Prop :=
  FieldMerge.fieldsInSetCanMerge schema execParent
    (eraseCompleteScopedSelectionSet scopedSelections)

theorem completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
    (schema : Schema) (execParent lookupParent : Name)
    (selectionSet : List Selection) :
    completeScopedSelectionSetSemanticsReady schema execParent
        (completeScopedSelectionSet lookupParent selectionSet)
      ↔
    selectionSetSemanticsReady schema execParent selectionSet := by
  simp [completeScopedSelectionSetSemanticsReady,
    eraseCompleteScopedSelectionSet_completeScopedSelectionSet]

theorem completeScopedSelectionSetCanMerge_completeScopedSelectionSet
    (schema : Schema) (execParent lookupParent : Name)
    (selectionSet : List Selection) :
    completeScopedSelectionSetCanMerge schema execParent
        (completeScopedSelectionSet lookupParent selectionSet)
      ↔
    FieldMerge.fieldsInSetCanMerge schema execParent selectionSet := by
  simp [completeScopedSelectionSetCanMerge,
    eraseCompleteScopedSelectionSet_completeScopedSelectionSet]

theorem completeScopedSelectionSetSemanticsReady_append
    {schema : Schema} {execParent : Name}
    {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetSemanticsReady schema execParent left ->
      completeScopedSelectionSetSemanticsReady schema execParent right ->
        completeScopedSelectionSetSemanticsReady schema execParent
          (left ++ right) := by
  intro hleft hright
  simpa [completeScopedSelectionSetSemanticsReady,
    eraseCompleteScopedSelectionSet_append] using
    selectionSetSemanticsReady_append hleft hright

theorem completeScopedSelectionSetSemanticsReady_append_left
    {schema : Schema} {execParent : Name}
    {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetSemanticsReady schema execParent
        (left ++ right) ->
      completeScopedSelectionSetSemanticsReady schema execParent left := by
  intro hready
  have hraw :
      selectionSetSemanticsReady schema execParent
        (eraseCompleteScopedSelectionSet left
          ++ eraseCompleteScopedSelectionSet right) := by
    simpa [completeScopedSelectionSetSemanticsReady,
      eraseCompleteScopedSelectionSet_append] using hready
  simpa [completeScopedSelectionSetSemanticsReady,
    eraseCompleteScopedSelectionSet_append] using
    selectionSetSemanticsReady_append_left
      (left := eraseCompleteScopedSelectionSet left)
      (right := eraseCompleteScopedSelectionSet right) hraw

theorem completeScopedSelectionSetSemanticsReady_append_right
    {schema : Schema} {execParent : Name}
    {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetSemanticsReady schema execParent
        (left ++ right) ->
      completeScopedSelectionSetSemanticsReady schema execParent right := by
  intro hready
  have hraw :
      selectionSetSemanticsReady schema execParent
        (eraseCompleteScopedSelectionSet left
          ++ eraseCompleteScopedSelectionSet right) := by
    simpa [completeScopedSelectionSetSemanticsReady,
      eraseCompleteScopedSelectionSet_append] using hready
  simpa [completeScopedSelectionSetSemanticsReady,
    eraseCompleteScopedSelectionSet_append] using
    selectionSetSemanticsReady_append_right
      (left := eraseCompleteScopedSelectionSet left)
      (right := eraseCompleteScopedSelectionSet right) hraw

theorem completeScopedSelectionSetSemanticsReady_tail
    {schema : Schema} {execParent : Name}
    {scopedSelection : CompleteScopedSelection}
    {rest : List CompleteScopedSelection} :
    completeScopedSelectionSetSemanticsReady schema execParent
        (scopedSelection :: rest) ->
      completeScopedSelectionSetSemanticsReady schema execParent rest := by
  intro hready
  simpa [completeScopedSelectionSetSemanticsReady,
    eraseCompleteScopedSelectionSet] using
    selectionSetSemanticsReady_tail
      (selection := eraseCompleteScopedSelection scopedSelection)
      (selectionSet := eraseCompleteScopedSelectionSet rest) hready

theorem completeScopedSelectionSetCanMerge_append_left
    (schema : Schema) (execParent : Name)
    (left right : List CompleteScopedSelection) :
    completeScopedSelectionSetCanMerge schema execParent (left ++ right) ->
      completeScopedSelectionSetCanMerge schema execParent left := by
  intro hmerge
  have hraw :
      FieldMerge.fieldsInSetCanMerge schema execParent
        (eraseCompleteScopedSelectionSet left
          ++ eraseCompleteScopedSelectionSet right) := by
    simpa [completeScopedSelectionSetCanMerge,
      eraseCompleteScopedSelectionSet_append] using hmerge
  simpa [completeScopedSelectionSetCanMerge,
    eraseCompleteScopedSelectionSet_append] using
    fieldsInSetCanMerge_append_left schema execParent
      (eraseCompleteScopedSelectionSet left)
      (eraseCompleteScopedSelectionSet right) hraw

theorem completeScopedSelectionSetCanMerge_append_right
    (schema : Schema) (execParent : Name)
    (left right : List CompleteScopedSelection) :
    completeScopedSelectionSetCanMerge schema execParent (left ++ right) ->
      completeScopedSelectionSetCanMerge schema execParent right := by
  intro hmerge
  have hraw :
      FieldMerge.fieldsInSetCanMerge schema execParent
        (eraseCompleteScopedSelectionSet left
          ++ eraseCompleteScopedSelectionSet right) := by
    simpa [completeScopedSelectionSetCanMerge,
      eraseCompleteScopedSelectionSet_append] using hmerge
  simpa [completeScopedSelectionSetCanMerge,
    eraseCompleteScopedSelectionSet_append] using
    fieldsInSetCanMerge_append_right schema execParent
      (eraseCompleteScopedSelectionSet left)
      (eraseCompleteScopedSelectionSet right) hraw

theorem completeScopedSelectionSetCanMerge_tail
    (schema : Schema) (execParent : Name)
    (scopedSelection : CompleteScopedSelection)
    (rest : List CompleteScopedSelection) :
    completeScopedSelectionSetCanMerge schema execParent
        (scopedSelection :: rest) ->
      completeScopedSelectionSetCanMerge schema execParent rest := by
  intro hmerge
  simpa [completeScopedSelectionSetCanMerge,
    eraseCompleteScopedSelectionSet] using
    fieldsInSetCanMerge_tail schema execParent
      (eraseCompleteScopedSelection scopedSelection)
      (eraseCompleteScopedSelectionSet rest) hmerge

theorem completeScopedSelectionSetGroundApplies_append
    {schema : Schema} {groundType : Name}
    {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetGroundApplies schema groundType left ->
      completeScopedSelectionSetGroundApplies schema groundType right ->
        completeScopedSelectionSetGroundApplies schema groundType
          (left ++ right) := by
  intro hleft hright scopedSelection hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft scopedSelection hmem
  · exact hright scopedSelection hmem

theorem completeScopedSelectionSetGroundApplies_append_left
    {schema : Schema} {groundType : Name}
    {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetGroundApplies schema groundType
        (left ++ right) ->
      completeScopedSelectionSetGroundApplies schema groundType left := by
  intro hground scopedSelection hmem
  exact hground scopedSelection (List.mem_append.mpr (Or.inl hmem))

theorem completeScopedSelectionSetGroundApplies_append_right
    {schema : Schema} {groundType : Name}
    {left right : List CompleteScopedSelection} :
    completeScopedSelectionSetGroundApplies schema groundType
        (left ++ right) ->
      completeScopedSelectionSetGroundApplies schema groundType right := by
  intro hground scopedSelection hmem
  exact hground scopedSelection (List.mem_append.mpr (Or.inr hmem))

theorem completeScopedSelectionSetGroundApplies_tail
    {schema : Schema} {groundType : Name}
    {scopedSelection : CompleteScopedSelection}
    {rest : List CompleteScopedSelection} :
    completeScopedSelectionSetGroundApplies schema groundType
        (scopedSelection :: rest) ->
      completeScopedSelectionSetGroundApplies schema groundType rest := by
  intro hground candidate hcandidate
  exact hground candidate (List.mem_cons_of_mem scopedSelection hcandidate)

def staticScopedFieldsWithResponseName
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    List Selection -> List CompleteScopedSelection
  | [] => []
  | selection :: rest =>
      let restFields :=
        staticScopedFieldsWithResponseName schema boolCase lookupParent
          groundType responseName rest
      match selection with
      | .field fieldResponseName _fieldName _arguments directives
          _selectionSet =>
          if directivesAllowIn boolCase directives then
            if fieldResponseName == responseName then
              { lookupParent := lookupParent, selection := selection }
                :: restFields
            else
              restFields
          else
            restFields
      | .inlineFragment none directives selectionSet =>
          if directivesAllowIn boolCase directives then
            staticScopedFieldsWithResponseName schema boolCase lookupParent
                groundType responseName selectionSet
              ++ restFields
          else
            restFields
      | .inlineFragment (some typeCondition) directives selectionSet =>
          if directivesAllowIn boolCase directives
              && schema.typeIncludesObjectBool typeCondition groundType then
            staticScopedFieldsWithResponseName schema boolCase typeCondition
                groundType responseName selectionSet
              ++ restFields
          else
            restFields

def completeScopedSelectionSetStaticFieldsWithResponseName
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name) :
    List CompleteScopedSelection -> List CompleteScopedSelection
  | [] => []
  | scopedSelection :: rest =>
      let restFields :=
        completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName rest
      match scopedSelection.selection with
      | .field fieldResponseName _fieldName _arguments directives
          _selectionSet =>
          if directivesAllowIn boolCase directives then
            if fieldResponseName == responseName then
              scopedSelection :: restFields
            else
              restFields
          else
            restFields
      | .inlineFragment none directives selectionSet =>
          if directivesAllowIn boolCase directives then
            staticScopedFieldsWithResponseName schema boolCase
                scopedSelection.lookupParent groundType responseName
                selectionSet
              ++ restFields
          else
            restFields
      | .inlineFragment (some typeCondition) directives selectionSet =>
          if directivesAllowIn boolCase directives
              && schema.typeIncludesObjectBool typeCondition groundType then
            staticScopedFieldsWithResponseName schema boolCase typeCondition
                groundType responseName selectionSet
              ++ restFields
          else
            restFields

def completeScopedSelectionSetWithoutFieldsWithResponseName
    (schema : Schema) (responseName : Name) :
    List CompleteScopedSelection -> List CompleteScopedSelection
  | [] => []
  | scopedSelection :: rest =>
      let filteredRest :=
        completeScopedSelectionSetWithoutFieldsWithResponseName schema
          responseName rest
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
                (withoutFieldsWithResponseName schema responseName
                  selectionSet) }
            :: filteredRest

theorem completeScopedSelectionSetStaticFieldsWithResponseName_append
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name) :
    ∀ left right,
      completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName (left ++ right)
        =
      completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName left
        ++
      completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName right
  | [], right => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName]
  | scopedSelection :: rest, right => by
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives <;>
              cases hresponse : fieldResponseName == responseName <;>
                simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                  hallow, hresponse,
                  completeScopedSelectionSetStaticFieldsWithResponseName_append
                    schema boolCase groundType responseName rest right]
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow,
                      completeScopedSelectionSetStaticFieldsWithResponseName_append
                        schema boolCase groundType responseName rest right]
                  · simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow,
                      completeScopedSelectionSetStaticFieldsWithResponseName_append
                        schema boolCase groundType responseName rest right,
                      List.append_assoc]
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch,
                      completeScopedSelectionSetStaticFieldsWithResponseName_append
                        schema boolCase groundType responseName rest right]
                  · simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch,
                      completeScopedSelectionSetStaticFieldsWithResponseName_append
                        schema boolCase groundType responseName rest right,
                      List.append_assoc]

theorem completeScopedSelectionSetWithoutFieldsWithResponseName_append
    (schema : Schema) (responseName : Name) :
    ∀ left right,
      completeScopedSelectionSetWithoutFieldsWithResponseName schema
          responseName (left ++ right)
        =
      completeScopedSelectionSetWithoutFieldsWithResponseName schema
          responseName left
        ++
      completeScopedSelectionSetWithoutFieldsWithResponseName schema
          responseName right
  | [], right => by
      simp [completeScopedSelectionSetWithoutFieldsWithResponseName]
  | scopedSelection :: rest, right => by
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hresponse : fieldResponseName == responseName <;>
                simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
                  hresponse,
                  completeScopedSelectionSetWithoutFieldsWithResponseName_append
                    schema responseName rest right]
          | inlineFragment typeCondition directives selectionSet =>
              simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
                completeScopedSelectionSetWithoutFieldsWithResponseName_append
                  schema responseName rest right]

theorem eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName
    (schema : Schema) (responseName : Name) :
    ∀ scopedSelections,
      eraseCompleteScopedSelectionSet
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName scopedSelections)
        =
      withoutFieldsWithResponseName schema responseName
        (eraseCompleteScopedSelectionSet scopedSelections)
  | [] => by
      simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
        eraseCompleteScopedSelectionSet, withoutFieldsWithResponseName]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hresponse : fieldResponseName == responseName <;>
                simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
                  eraseCompleteScopedSelectionSet,
                  eraseCompleteScopedSelection, withoutFieldsWithResponseName,
                  hresponse,
                  eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName
                    schema responseName rest]
          | inlineFragment typeCondition directives selectionSet =>
              simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
                eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
                withoutFieldsWithResponseName,
                eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName
                  schema responseName rest]

theorem eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName_size_lt_field_directives
    (schema : Schema) (lookupParent responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (rest : List CompleteScopedSelection) :
    SelectionSet.size
        (eraseCompleteScopedSelectionSet
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName rest))
      <
    SelectionSet.size
      (eraseCompleteScopedSelectionSet
        ({ lookupParent := lookupParent,
           selection :=
            Selection.field responseName fieldName arguments directives
              selectionSet }
          :: rest)) := by
  have hle :
      SelectionSet.size
          (withoutFieldsWithResponseName schema responseName
            (eraseCompleteScopedSelectionSet rest))
        ≤
      SelectionSet.size (eraseCompleteScopedSelectionSet rest) :=
    completeSize_withoutFieldsWithResponseName_le schema responseName
      (eraseCompleteScopedSelectionSet rest)
  have htail :
      SelectionSet.size (eraseCompleteScopedSelectionSet rest)
        <
      SelectionSet.size
        (eraseCompleteScopedSelectionSet
          ({ lookupParent := lookupParent,
             selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
            :: rest)) :=
    eraseCompleteScopedSelectionSet_tail_size_lt
      { lookupParent := lookupParent,
        selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
      rest
  rw [eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName]
  exact Nat.lt_of_le_of_lt hle htail

theorem completeScopedSelectionSetWithoutFieldsWithResponseName_lookupValid
    (schema : Schema) (responseName : Name) :
    ∀ scopedSelections,
      completeScopedSelectionSetLookupValid schema scopedSelections ->
        completeScopedSelectionSetLookupValid schema
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName scopedSelections)
  | [], _hvalid => by
      simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
        completeScopedSelectionSetLookupValid]
  | scopedSelection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema scopedSelection.lookupParent
            scopedSelection.selection :=
        hvalid scopedSelection (by simp)
      have htailValid :
          completeScopedSelectionSetLookupValid schema rest := by
        intro candidate hcandidate
        exact hvalid candidate (by simp [hcandidate])
      have hrest :=
        completeScopedSelectionSetWithoutFieldsWithResponseName_lookupValid
          schema responseName rest htailValid
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hresponse : fieldResponseName == responseName
              · intro candidate hcandidate
                simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
                  hresponse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  exact hheadValid
                · exact hrest candidate hcandidate
              · simpa [completeScopedSelectionSetWithoutFieldsWithResponseName,
                  hresponse] using hrest
          | inlineFragment typeCondition directives selectionSet =>
              intro candidate hcandidate
              simp [completeScopedSelectionSetWithoutFieldsWithResponseName]
                at hcandidate
              rcases hcandidate with hcandidate | hcandidate
              · subst candidate
                cases typeCondition with
                | none =>
                    have hbodyValid :
                        selectionSetLookupValid schema lookupParent
                          selectionSet := by
                      simpa [selectionLookupValid] using hheadValid
                    simpa [selectionLookupValid] using
                      selectionSetLookupValid_withoutFieldsWithResponseName
                        schema responseName lookupParent selectionSet
                        hbodyValid
                | some typeCondition =>
                    have hbodyValid :
                        selectionSetLookupValid schema typeCondition
                          selectionSet := by
                      simpa [selectionLookupValid] using hheadValid
                    simpa [selectionLookupValid] using
                      selectionSetLookupValid_withoutFieldsWithResponseName
                        schema responseName typeCondition selectionSet
                        hbodyValid
              · exact hrest candidate hcandidate

theorem completeScopedSelectionSetWithoutFieldsWithResponseName_semanticsReady
    (schema : Schema) (execParent responseName : Name) :
    ∀ scopedSelections,
      completeScopedSelectionSetSemanticsReady schema execParent
          scopedSelections ->
        completeScopedSelectionSetSemanticsReady schema execParent
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName scopedSelections)
  | scopedSelections, hready => by
      simpa [completeScopedSelectionSetSemanticsReady,
        eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName] using
        selectionSetSemanticsReady_withoutFieldsWithResponseName schema
          responseName execParent
          (eraseCompleteScopedSelectionSet scopedSelections) hready

theorem completeScopedSelectionSetWithoutFieldsWithResponseName_canMerge
    (schema : Schema) (execParent responseName : Name) :
    ∀ scopedSelections,
      completeScopedSelectionSetCanMerge schema execParent scopedSelections ->
        completeScopedSelectionSetCanMerge schema execParent
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName scopedSelections)
  | scopedSelections, hmerge => by
      simpa [completeScopedSelectionSetCanMerge,
        eraseCompleteScopedSelectionSet_withoutFieldsWithResponseName] using
        fieldsInSetCanMerge_withoutFieldsWithResponseName schema responseName
          execParent (eraseCompleteScopedSelectionSet scopedSelections) hmerge

theorem completeScopedSelectionSetWithoutFieldsWithResponseName_groundApplies
    (schema : Schema) (groundType responseName : Name) :
    ∀ scopedSelections,
      completeScopedSelectionSetGroundApplies schema groundType
          scopedSelections ->
        completeScopedSelectionSetGroundApplies schema groundType
          (completeScopedSelectionSetWithoutFieldsWithResponseName schema
            responseName scopedSelections)
  | [], _hground => by
      simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
        completeScopedSelectionSetGroundApplies]
  | scopedSelection :: rest, hground => by
      have hheadGround :
          schema.typeIncludesObjectBool scopedSelection.lookupParent
              groundType =
            true :=
        hground scopedSelection (by simp)
      have htailGround :
          completeScopedSelectionSetGroundApplies schema groundType rest := by
        intro candidate hcandidate
        exact hground candidate (by simp [hcandidate])
      have hrest :=
        completeScopedSelectionSetWithoutFieldsWithResponseName_groundApplies
          schema groundType responseName rest htailGround
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hresponse : fieldResponseName == responseName
              · intro candidate hcandidate
                simp [completeScopedSelectionSetWithoutFieldsWithResponseName,
                  hresponse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  exact hheadGround
                · exact hrest candidate hcandidate
              · simpa [completeScopedSelectionSetWithoutFieldsWithResponseName,
                  hresponse] using hrest
          | inlineFragment typeCondition directives selectionSet =>
              intro candidate hcandidate
              simp [completeScopedSelectionSetWithoutFieldsWithResponseName]
                at hcandidate
              rcases hcandidate with hcandidate | hcandidate
              · subst candidate
                exact hheadGround
              · exact hrest candidate hcandidate

theorem eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
    (schema : Schema) (boolCase : BoolCase)
    (leftParent rightParent groundType responseName : Name) :
    ∀ selectionSet,
      eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase leftParent
            groundType responseName selectionSet)
        =
      eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase rightParent
            groundType responseName selectionSet)
  | [] => by
      simp [staticScopedFieldsWithResponseName,
        eraseCompleteScopedSelectionSet]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives <;>
            cases hresponse : fieldResponseName == responseName <;>
              simp [staticScopedFieldsWithResponseName, hallow, hresponse,
                eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
                eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                  schema boolCase leftParent rightParent groundType
                  responseName rest]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simp [staticScopedFieldsWithResponseName, hallow,
                  eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                    schema boolCase leftParent rightParent groundType
                    responseName rest]
              · simp [staticScopedFieldsWithResponseName, hallow,
                  eraseCompleteScopedSelectionSet_append,
                  eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                    schema boolCase leftParent rightParent groundType
                    responseName selectionSet,
                  eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                    schema boolCase leftParent rightParent groundType
                    responseName rest]
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · simp [staticScopedFieldsWithResponseName, hbranch,
                  eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                    schema boolCase leftParent rightParent groundType
                    responseName rest]
              · simp [staticScopedFieldsWithResponseName, hbranch,
                  eraseCompleteScopedSelectionSet_append,
                  eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                    schema boolCase leftParent rightParent groundType
                    responseName rest]

theorem eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ scopedSelections,
      eraseCompleteScopedSelectionSet
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName scopedSelections)
        =
      eraseCompleteScopedSelectionSet
        (staticScopedFieldsWithResponseName schema boolCase lookupParent
          groundType responseName
          (eraseCompleteScopedSelectionSet scopedSelections))
  | [] => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName,
        staticScopedFieldsWithResponseName, eraseCompleteScopedSelectionSet]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk scopedLookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives <;>
                cases hresponse : fieldResponseName == responseName <;>
                  simp [
                    completeScopedSelectionSetStaticFieldsWithResponseName,
                    staticScopedFieldsWithResponseName,
                    eraseCompleteScopedSelectionSet,
                    eraseCompleteScopedSelection, hallow, hresponse,
                    eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                      schema boolCase lookupParent groundType responseName
                      rest]
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simp [
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      staticScopedFieldsWithResponseName,
                      eraseCompleteScopedSelectionSet,
                      eraseCompleteScopedSelection, hallow,
                      eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                        schema boolCase lookupParent groundType responseName
                        rest]
                  · simp [
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      staticScopedFieldsWithResponseName,
                      eraseCompleteScopedSelectionSet,
                      eraseCompleteScopedSelection, hallow,
                      eraseCompleteScopedSelectionSet_append,
                      eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                        schema boolCase scopedLookupParent lookupParent
                        groundType responseName selectionSet,
                      eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                        schema boolCase lookupParent groundType responseName
                        rest]
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · simp [
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      staticScopedFieldsWithResponseName,
                      eraseCompleteScopedSelectionSet,
                      eraseCompleteScopedSelection, hbranch,
                      eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                        schema boolCase lookupParent groundType responseName
                        rest]
                  · simp [
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      staticScopedFieldsWithResponseName,
                      eraseCompleteScopedSelectionSet,
                      eraseCompleteScopedSelection, hbranch,
                      eraseCompleteScopedSelectionSet_append,
                      eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
                        schema boolCase lookupParent groundType responseName
                        rest]

theorem validFieldsWithResponseName_staticCollectForGround_scoped
    (schema : Schema) (variables : List BoolVar)
    (filterParent lookupParent groundType responseName : Name)
    (boolCase : BoolCase) :
    ∀ selectionSet,
      validFieldsWithResponseName schema filterParent responseName
          (staticCollectForGround schema variables lookupParent
            groundType boolCase selectionSet)
        =
      staticCollectCompleteScopedSelectionSet schema variables groundType
        boolCase
        (staticScopedFieldsWithResponseName schema boolCase lookupParent
          groundType responseName selectionSet)
  | [] => by
      simp [validFieldsWithResponseName, staticCollectForGround,
        staticScopedFieldsWithResponseName,
        staticCollectCompleteScopedSelectionSet]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · simp [staticCollectForGround,
              staticScopedFieldsWithResponseName, hallow,
              validFieldsWithResponseName_staticCollectForGround_scoped
                schema variables filterParent lookupParent groundType responseName
                boolCase rest]
          · cases hresponse : fieldResponseName == responseName <;>
              cases hlookup : schema.lookupField lookupParent fieldName <;>
                simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName,
                  staticCollectCompleteScopedSelectionSet,
                  staticCollectCompleteScopedSelection,
                  validFieldsWithResponseName, hallow, hresponse, hlookup,
                  validFieldsWithResponseName_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType responseName
                    boolCase rest]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hallow,
                  validFieldsWithResponseName_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hallow,
                  validFieldsWithResponseName_append,
                  staticCollectCompleteScopedSelectionSet_append,
                  validFieldsWithResponseName_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase selectionSet,
                  validFieldsWithResponseName_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hbranch,
                  validFieldsWithResponseName_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hbranch,
                  validFieldsWithResponseName_append,
                  staticCollectCompleteScopedSelectionSet_append,
                  validFieldsWithResponseName_staticCollectForGround_scoped
                    schema variables filterParent typeCondition groundType
                    responseName boolCase selectionSet,
                  validFieldsWithResponseName_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]

theorem validFieldsWithResponseName_staticCollectCompleteScopedSelectionSet
    (schema : Schema) (variables : List BoolVar)
    (filterParent groundType responseName : Name)
    (boolCase : BoolCase) :
    ∀ scopedSelections,
      validFieldsWithResponseName schema filterParent responseName
          (staticCollectCompleteScopedSelectionSet schema variables groundType
            boolCase scopedSelections)
        =
      staticCollectCompleteScopedSelectionSet schema variables groundType
        boolCase
        (completeScopedSelectionSetStaticFieldsWithResponseName schema
          boolCase groundType responseName scopedSelections)
  | [] => by
      simp [validFieldsWithResponseName,
        staticCollectCompleteScopedSelectionSet,
        completeScopedSelectionSetStaticFieldsWithResponseName]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk lookupParent selection =>
          have hhead :=
            validFieldsWithResponseName_staticCollectForGround_scoped
              schema variables filterParent lookupParent groundType
              responseName boolCase [selection]
          have hrest :=
            validFieldsWithResponseName_staticCollectCompleteScopedSelectionSet
              schema variables filterParent groundType responseName boolCase
              rest
          rw [staticCollectCompleteScopedSelectionSet]
          rw [validFieldsWithResponseName_append]
          change
            validFieldsWithResponseName schema filterParent responseName
                (staticCollectForGround schema variables
                  lookupParent groundType boolCase [selection])
              ++
            validFieldsWithResponseName schema filterParent responseName
                (staticCollectCompleteScopedSelectionSet schema variables
                  groundType boolCase rest)
              =
            staticCollectCompleteScopedSelectionSet schema variables groundType
              boolCase
              (completeScopedSelectionSetStaticFieldsWithResponseName schema
                boolCase groundType responseName
                ({ lookupParent := lookupParent, selection := selection }
                  :: rest))
          rw [hhead, hrest]
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives <;>
                cases hresponse : fieldResponseName == responseName <;>
                  cases hlookup : schema.lookupField lookupParent fieldName <;>
                    simp [staticCollectCompleteScopedSelectionSet,
                      staticCollectCompleteScopedSelection,
                      staticCollectForGround,
                      staticScopedFieldsWithResponseName,
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow, hresponse, hlookup]
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives <;>
                    simp [staticCollectCompleteScopedSelectionSet,
                      staticCollectCompleteScopedSelectionSet_append,
                      staticScopedFieldsWithResponseName,
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow]
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType <;>
                    simp [staticCollectCompleteScopedSelectionSet,
                      staticCollectCompleteScopedSelectionSet_append,
                      staticScopedFieldsWithResponseName,
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch]

theorem staticScopedFieldsWithResponseName_lookupValid
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ selectionSet,
      selectionSetLookupValid schema lookupParent selectionSet ->
        completeScopedSelectionSetLookupValid schema
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet)
  | [], _hvalid => by
      simp [staticScopedFieldsWithResponseName,
        completeScopedSelectionSetLookupValid]
  | selection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema lookupParent selection :=
        selectionSetLookupValid_head hvalid
      have htailValid :
          selectionSetLookupValid schema lookupParent rest :=
        selectionSetLookupValid_tail hvalid
      have hrest :=
        staticScopedFieldsWithResponseName_lookupValid schema boolCase
          lookupParent groundType responseName rest htailValid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · simpa [staticScopedFieldsWithResponseName, hallow] using hrest
          · cases hresponse : fieldResponseName == responseName
            · simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                using hrest
            · intro scopedSelection hmem
              simp [staticScopedFieldsWithResponseName, hallow, hresponse]
                at hmem
              rcases hmem with hhead | htail
              · subst scopedSelection
                exact hheadValid
              · exact hrest scopedSelection htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [staticScopedFieldsWithResponseName, hallow]
                  using hrest
              · have hbodyValid :
                    selectionSetLookupValid schema lookupParent
                      selectionSet := by
                  simpa [selectionLookupValid] using hheadValid
                have hbody :=
                  staticScopedFieldsWithResponseName_lookupValid schema
                    boolCase lookupParent groundType responseName
                    selectionSet hbodyValid
                simpa [staticScopedFieldsWithResponseName, hallow] using
                  completeScopedSelectionSetLookupValid_append hbody hrest
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · simpa [staticScopedFieldsWithResponseName, hbranch]
                  using hrest
              · have hbodyValid :
                    selectionSetLookupValid schema typeCondition
                      selectionSet := by
                  simpa [selectionLookupValid] using hheadValid
                have hbody :=
                  staticScopedFieldsWithResponseName_lookupValid schema
                    boolCase typeCondition groundType responseName
                    selectionSet hbodyValid
                simpa [staticScopedFieldsWithResponseName, hbranch] using
                  completeScopedSelectionSetLookupValid_append hbody hrest

theorem staticScopedFieldsWithResponseName_groundApplies
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ selectionSet,
      schema.typeIncludesObjectBool lookupParent groundType = true ->
        completeScopedSelectionSetGroundApplies schema groundType
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet)
  | [], _hincludes => by
      simp [staticScopedFieldsWithResponseName,
        completeScopedSelectionSetGroundApplies]
  | selection :: rest, hincludes => by
      have hrest :=
        staticScopedFieldsWithResponseName_groundApplies schema boolCase
          lookupParent groundType responseName rest hincludes
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · simpa [staticScopedFieldsWithResponseName, hallow] using hrest
          · cases hresponse : fieldResponseName == responseName
            · simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                using hrest
            · intro scopedSelection hmem
              simp [staticScopedFieldsWithResponseName, hallow, hresponse]
                at hmem
              rcases hmem with hhead | htail
              · subst scopedSelection
                exact hincludes
              · exact hrest scopedSelection htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [staticScopedFieldsWithResponseName, hallow]
                  using hrest
              · have hbody :=
                  staticScopedFieldsWithResponseName_groundApplies schema
                    boolCase lookupParent groundType responseName
                    selectionSet hincludes
                simpa [staticScopedFieldsWithResponseName, hallow] using
                  completeScopedSelectionSetGroundApplies_append hbody hrest
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · simpa [staticScopedFieldsWithResponseName, hbranch]
                  using hrest
              · have htypeIncludes :
                    schema.typeIncludesObjectBool typeCondition groundType =
                      true := by
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simp [hallow] at hbranch
                  · simpa [hallow] using hbranch
                have hbody :=
                  staticScopedFieldsWithResponseName_groundApplies schema
                    boolCase typeCondition groundType responseName
                    selectionSet htypeIncludes
                simpa [staticScopedFieldsWithResponseName, hbranch] using
                  completeScopedSelectionSetGroundApplies_append hbody hrest

theorem completeScopedSelectionSetStaticFieldsWithResponseName_lookupValid
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name) :
    ∀ scopedSelections,
      completeScopedSelectionSetLookupValid schema scopedSelections ->
        completeScopedSelectionSetLookupValid schema
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName scopedSelections)
  | [], _hvalid => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName,
        completeScopedSelectionSetLookupValid]
  | scopedSelection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema scopedSelection.lookupParent
            scopedSelection.selection :=
        hvalid scopedSelection (by simp)
      have htailValid :
          completeScopedSelectionSetLookupValid schema rest := by
        intro candidate hcandidate
        exact hvalid candidate (by simp [hcandidate])
      have hrest :=
        completeScopedSelectionSetStaticFieldsWithResponseName_lookupValid
          schema boolCase groundType responseName rest htailValid
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                  hallow] using hrest
              · cases hresponse : fieldResponseName == responseName
                · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] using hrest
                · intro candidate hcandidate
                  simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] at hcandidate
                  rcases hcandidate with hcandidate | hcandidate
                  · subst candidate
                    exact hheadValid
                  · exact hrest candidate hcandidate
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using hrest
                  · have hbodyValid :
                        selectionSetLookupValid schema lookupParent
                          selectionSet := by
                      simpa [selectionLookupValid] using hheadValid
                    have hbody :=
                      staticScopedFieldsWithResponseName_lookupValid schema
                        boolCase lookupParent groundType responseName
                        selectionSet hbodyValid
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using
                      completeScopedSelectionSetLookupValid_append hbody hrest
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using hrest
                  · have hbodyValid :
                        selectionSetLookupValid schema typeCondition
                          selectionSet := by
                      simpa [selectionLookupValid] using hheadValid
                    have hbody :=
                      staticScopedFieldsWithResponseName_lookupValid schema
                        boolCase typeCondition groundType responseName
                        selectionSet hbodyValid
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using
                      completeScopedSelectionSetLookupValid_append hbody hrest

theorem completeScopedSelectionSetStaticFieldsWithResponseName_groundApplies
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name) :
    ∀ scopedSelections,
      completeScopedSelectionSetGroundApplies schema groundType
          scopedSelections ->
        completeScopedSelectionSetGroundApplies schema groundType
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName scopedSelections)
  | [], _hground => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName,
        completeScopedSelectionSetGroundApplies]
  | scopedSelection :: rest, hground => by
      have hheadGround :
          schema.typeIncludesObjectBool scopedSelection.lookupParent
              groundType =
            true :=
        hground scopedSelection (by simp)
      have htailGround :
          completeScopedSelectionSetGroundApplies schema groundType rest := by
        intro candidate hcandidate
        exact hground candidate (by simp [hcandidate])
      have hrest :=
        completeScopedSelectionSetStaticFieldsWithResponseName_groundApplies
          schema boolCase groundType responseName rest htailGround
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                  hallow] using hrest
              · cases hresponse : fieldResponseName == responseName
                · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] using hrest
                · intro candidate hcandidate
                  simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] at hcandidate
                  rcases hcandidate with hcandidate | hcandidate
                  · subst candidate
                    exact hheadGround
                  · exact hrest candidate hcandidate
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using hrest
                  · have hbody :=
                      staticScopedFieldsWithResponseName_groundApplies schema
                        boolCase lookupParent groundType responseName
                        selectionSet hheadGround
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using
                      completeScopedSelectionSetGroundApplies_append hbody hrest
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using hrest
                  · have htypeGround :
                        schema.typeIncludesObjectBool typeCondition
                            groundType =
                          true := by
                      cases hallow :
                          directivesAllowIn boolCase
                            directives
                      · simp [hallow] at hbranch
                      · simpa [hallow] using hbranch
                    have hbody :=
                      staticScopedFieldsWithResponseName_groundApplies schema
                        boolCase typeCondition groundType responseName
                        selectionSet htypeGround
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using
                      completeScopedSelectionSetGroundApplies_append hbody hrest

theorem typesOverlapBool_true_of_common_ground
    (schema : Schema) {left right groundType : Name} :
    schema.typeIncludesObjectBool left groundType = true ->
    schema.typeIncludesObjectBool right groundType = true ->
      schema.typesOverlapBool left right = true := by
  intro hleft hright
  unfold Schema.typesOverlapBool
  exact List.any_eq_true.mpr
    ⟨groundType, List.contains_iff_mem.mp hleft, hright⟩

theorem erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ selectionSet selection,
      schema.typeIncludesObjectBool lookupParent groundType = true ->
      selection ∈
          eraseCompleteScopedSelectionSet
            (staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet) ->
        selection ∈ validFieldsWithResponseName schema lookupParent
          responseName selectionSet
  | [], selection, _hincludes, hmem => by
      simp [staticScopedFieldsWithResponseName,
        eraseCompleteScopedSelectionSet] at hmem
  | Selection.field fieldResponseName fieldName arguments directives
      selectionSet :: rest, selection, hincludes, hmem => by
      have hrest :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName rest
          selection hincludes
      cases hallow :
          directivesAllowIn boolCase directives
      · have hrestMem :
            selection ∈
              eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hallow] using hmem
        cases hresponse : fieldResponseName == responseName <;>
          simp [validFieldsWithResponseName, hresponse, hrest hrestMem]
      · cases hresponse : fieldResponseName == responseName
        · have hrestMem :
              selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest) := by
            simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
              using hmem
          simp [validFieldsWithResponseName, hresponse, hrest hrestMem]
        · have hmem' :
              selection =
                  Selection.field fieldResponseName fieldName arguments
                    directives selectionSet
                ∨ selection ∈
                  eraseCompleteScopedSelectionSet
                    (staticScopedFieldsWithResponseName schema boolCase
                      lookupParent groundType responseName rest) := by
            simpa [staticScopedFieldsWithResponseName, hallow, hresponse,
              eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection]
              using hmem
          rcases hmem' with hhead | htail
          · subst selection
            simp [validFieldsWithResponseName, hresponse]
          · simp [validFieldsWithResponseName, hresponse, hrest htail]
  | Selection.inlineFragment none directives selectionSet :: rest, selection,
      hincludes, hmem => by
      have hselection :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName selectionSet
          selection hincludes
      have hrest :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName rest
          selection hincludes
      cases hallow :
          directivesAllowIn boolCase directives
      · have hrestMem :
            selection ∈
              eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hallow] using hmem
        simp [validFieldsWithResponseName, hrest hrestMem]
      · have hmem' :
            selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName selectionSet)
              ∨ selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hallow,
            eraseCompleteScopedSelectionSet_append] using hmem
        rcases hmem' with hchild | htail
        · simp [validFieldsWithResponseName, hselection hchild]
        · simp [validFieldsWithResponseName, hrest htail]
  | Selection.inlineFragment (some typeCondition) directives selectionSet ::
      rest, selection, hincludes, hmem => by
      have hrest :=
        erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
          schema boolCase lookupParent groundType responseName rest
          selection hincludes
      cases hbranch :
          directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType
      · have hrestMem :
            selection ∈
              eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hbranch] using hmem
        cases hoverlap :
            schema.typesOverlapBool lookupParent typeCondition <;>
          simp [validFieldsWithResponseName, hoverlap, hrest hrestMem]
      · have hconditionIncludes :
            schema.typeIncludesObjectBool typeCondition groundType = true := by
          cases hallow :
              directivesAllowIn boolCase directives
          · simp [hallow] at hbranch
          · simpa [hallow] using hbranch
        have hoverlap :
            schema.typesOverlapBool lookupParent typeCondition = true :=
          typesOverlapBool_true_of_common_ground schema hincludes
            hconditionIncludes
        have hselection :=
          erase_staticScopedFieldsWithResponseName_mem_validFieldsWithResponseName
            schema boolCase lookupParent groundType responseName
            selectionSet selection hincludes
        have hmem' :
            selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    typeCondition groundType responseName selectionSet)
              ∨ selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hbranch,
            eraseCompleteScopedSelectionSet_append] using hmem
        rcases hmem' with hchild | htail
        · have hchildLookup :
              selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName selectionSet) := by
            simpa [
              eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                schema boolCase typeCondition lookupParent groundType
                responseName selectionSet] using hchild
          simp [validFieldsWithResponseName, hoverlap,
            hselection hchildLookup]
        · simp [validFieldsWithResponseName, hoverlap, hrest htail]

theorem staticScopedFieldsWithResponseName_mem_field
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ selectionSet scopedSelection,
      scopedSelection ∈
          staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet ->
        ∃ fieldResponseName fieldName arguments directives subselections,
          scopedSelection.selection =
            Selection.field fieldResponseName fieldName arguments directives
              subselections
  | [], scopedSelection, hmem => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, hmem => by
      have hrest :=
        staticScopedFieldsWithResponseName_mem_field schema boolCase
          lookupParent groundType responseName rest scopedSelection
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · exact hrest
              (by simpa [staticScopedFieldsWithResponseName, hallow] using hmem)
          · cases hresponse : fieldResponseName == responseName
            · exact hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow,
                    hresponse] using hmem)
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field fieldResponseName fieldName
                            arguments directives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                exact ⟨fieldResponseName, fieldName, arguments, directives,
                  selectionSet, rfl⟩
              · exact hrest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow]
                      using hmem)
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field schema
                      boolCase lookupParent groundType responseName
                      selectionSet scopedSelection hchild
                · exact hrest htail
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hbranch]
                      using hmem)
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field schema
                      boolCase typeCondition groundType responseName
                      selectionSet scopedSelection hchild
                · exact hrest htail

theorem collectFields_scoped_mem_lookupValid
    (schema : Schema) (parentType : Name) :
    ∀ selectionSet scopedField,
      selectionSetLookupValid schema parentType selectionSet ->
      scopedField ∈ FieldMerge.collectFields schema parentType selectionSet ->
        ∃ fieldDefinition,
          schema.lookupField scopedField.parentType scopedField.fieldName =
            some fieldDefinition
            ∧ fieldDefinition.outputType = scopedField.outputType
  | [], scopedField, _hlookupValid, hscoped => by
      simp [FieldMerge.collectFields] at hscoped
  | selection :: rest, scopedField, hlookupValid, hscoped => by
      have hheadLookup :
          selectionLookupValid schema parentType selection :=
        selectionSetLookupValid_head hlookupValid
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          simp [selectionLookupValid] at hheadLookup
          rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
          simp [FieldMerge.collectFields, hlookup] at hscoped
          rcases hscoped with hcurrent | hrest
          · subst scopedField
            exact ⟨fieldDefinition, hlookup, rfl⟩
          · exact collectFields_scoped_mem_lookupValid schema parentType rest
              scopedField htailLookup hrest
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionLookup :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              simp [FieldMerge.collectFields] at hscoped
              rcases hscoped with hselectionSet | hrest
              · exact collectFields_scoped_mem_lookupValid schema parentType
                  selectionSet scopedField hselectionLookup hselectionSet
              · exact collectFields_scoped_mem_lookupValid schema parentType
                  rest scopedField htailLookup hrest
          | some typeCondition =>
              have hselectionLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              simp [FieldMerge.collectFields] at hscoped
              rcases hscoped with hselectionSet | hrest
              · exact collectFields_scoped_mem_lookupValid schema typeCondition
                  selectionSet scopedField hselectionLookup hselectionSet
              · exact collectFields_scoped_mem_lookupValid schema parentType
                  rest scopedField htailLookup hrest

theorem staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ selectionSet scopedSelection fieldResponseName fieldName arguments
      directives subselections,
      selectionSetLookupValid schema lookupParent selectionSet ->
      scopedSelection ∈
          staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet ->
      scopedSelection.selection =
        Selection.field fieldResponseName fieldName arguments directives
          subselections ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema lookupParent
            selectionSet
            ∧ scopedField.parentType = scopedSelection.lookupParent
            ∧ scopedField.responseName = fieldResponseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, _hlookupValid, hmem, _hselection => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, fieldResponseName, fieldName,
      arguments, directives, subselections, hlookupValid, hmem,
      hselection => by
      have hheadLookup :
          selectionLookupValid schema lookupParent selection :=
        selectionSetLookupValid_head hlookupValid
      have htailLookup :
          selectionSetLookupValid schema lookupParent rest :=
        selectionSetLookupValid_tail hlookupValid
      have hrest :=
        staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
          schema boolCase lookupParent groundType responseName rest
          scopedSelection fieldResponseName fieldName arguments directives
          subselections htailLookup
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet =>
          simp [selectionLookupValid] at hheadLookup
          rcases hheadLookup with ⟨selectionFieldDefinition, hlookup⟩
          cases hallow :
              directivesAllowIn boolCase
                selectionDirectives
          · rcases
              hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow] using
                    hmem)
                hselection with
              ⟨scopedField, hscoped, hparent, hresponse, hfield, hargs,
                hsubselections⟩
            refine ⟨scopedField, ?_, hparent, hresponse, hfield, hargs,
              hsubselections⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · cases hresponse : selectionResponseName == responseName
            · rcases
                hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow,
                      hresponse] using hmem)
                  hselection with
                ⟨scopedField, hscoped, hresponseName, hfield, hargs,
                  hsubselections⟩
              refine ⟨scopedField, ?_, hresponseName, hfield, hargs,
                hsubselections⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field selectionResponseName
                            selectionFieldName selectionArguments
                            selectionDirectives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                injection hselection with hresponseName hfield hargs
                  hdirectives hsubselections
                subst fieldResponseName
                subst fieldName
                subst arguments
                subst directives
                subst subselections
                refine ⟨{
                  parentType := lookupParent,
                  responseName := selectionResponseName,
                  fieldName := selectionFieldName,
                  arguments := selectionArguments,
                  outputType := selectionFieldDefinition.outputType,
                  selectionSet := selectionSet
                }, ?_, rfl, rfl, rfl, rfl, rfl⟩
                simp [FieldMerge.collectFields, hlookup]
              · rcases hrest htail hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionLookup :
                  selectionSetLookupValid schema lookupParent selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
                  schema boolCase lookupParent groundType responseName
                  selectionSet scopedSelection fieldResponseName fieldName
                  arguments directives subselections hselectionLookup
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hallow]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
                  schema boolCase typeCondition groundType responseName
                  selectionSet scopedSelection fieldResponseName fieldName
                  arguments directives subselections hselectionLookup
              cases hbranch :
                  directivesAllowIn boolCase
                      selectionDirectives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hbranch]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]

theorem staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ selectionSet scopedSelection fieldResponseName fieldName arguments
      directives subselections,
      Validation.selectionSetValid schema variableDefinitions lookupParent
        selectionSet ->
      scopedSelection ∈
          staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet ->
      scopedSelection.selection =
        Selection.field fieldResponseName fieldName arguments directives
          subselections ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema lookupParent
            selectionSet
            ∧ scopedField.parentType = scopedSelection.lookupParent
            ∧ scopedField.responseName = fieldResponseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, _hvalid, hmem, _hselection => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, fieldResponseName, fieldName,
      arguments, directives, subselections, hvalid, hmem, hselection => by
      have hheadValid :
          Validation.selectionValid schema variableDefinitions lookupParent
            selection := by
        simp [Validation.selectionSetValid] at hvalid
        exact hvalid.1
      have htailValid :
          Validation.selectionSetValid schema variableDefinitions lookupParent
            rest :=
        Validation.selectionSetValid_tail hvalid
      have hrest :=
        staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
          schema variableDefinitions boolCase lookupParent groundType
          responseName rest scopedSelection fieldResponseName fieldName
          arguments directives subselections htailValid
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet =>
          rcases Validation.selectionValid_field_lookup hheadValid with
            ⟨selectionFieldDefinition, hlookup, _harguments, _hchild⟩
          cases hallow :
              directivesAllowIn boolCase
                selectionDirectives
          · rcases
              hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow] using
                    hmem)
                hselection with
              ⟨scopedField, hscoped, hparent, hresponse, hfield, hargs,
                hsubselections⟩
            refine ⟨scopedField, ?_, hparent, hresponse, hfield, hargs,
              hsubselections⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · cases hresponse : selectionResponseName == responseName
            · rcases
                hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow,
                      hresponse] using hmem)
                  hselection with
                ⟨scopedField, hscoped, hparent, hresponseName, hfield, hargs,
                  hsubselections⟩
              refine ⟨scopedField, ?_, hparent, hresponseName, hfield, hargs,
                hsubselections⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field selectionResponseName
                            selectionFieldName selectionArguments
                            selectionDirectives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                injection hselection with hresponseName hfield hargs
                  hdirectives hsubselections
                subst fieldResponseName
                subst fieldName
                subst arguments
                subst directives
                subst subselections
                refine ⟨{
                  parentType := lookupParent,
                  responseName := selectionResponseName,
                  fieldName := selectionFieldName,
                  arguments := selectionArguments,
                  outputType := selectionFieldDefinition.outputType,
                  selectionSet := selectionSet
                }, ?_, rfl, rfl, rfl, rfl, rfl⟩
                simp [FieldMerge.collectFields, hlookup]
              · rcases hrest htail hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionValid :
                  Validation.selectionSetValid schema variableDefinitions
                    lookupParent selectionSet :=
                Validation.selectionValid_inlineFragment_none_selectionSetValid
                  hheadValid
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
                  schema variableDefinitions boolCase lookupParent groundType
                  responseName selectionSet scopedSelection fieldResponseName
                  fieldName arguments directives subselections hselectionValid
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hallow]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionValid :
                  Validation.selectionSetValid schema variableDefinitions
                    typeCondition selectionSet :=
                Validation.selectionValid_inlineFragment_some_selectionSetValid
                  hheadValid
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
                  schema variableDefinitions boolCase typeCondition
                  groundType responseName selectionSet scopedSelection
                  fieldResponseName fieldName arguments directives subselections
                  hselectionValid
              cases hbranch :
                  directivesAllowIn boolCase
                      selectionDirectives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hbranch]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]

theorem staticScopedFieldsWithResponseName_mem_field_allowed
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) :
    ∀ selectionSet scopedSelection fieldResponseName fieldName arguments
      directives subselections,
      scopedSelection ∈
          staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet ->
      scopedSelection.selection =
        Selection.field fieldResponseName fieldName arguments directives
          subselections ->
        directivesAllowIn boolCase directives = true
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, hmem, _hselection => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, fieldResponseName, fieldName,
      arguments, directives, subselections, hmem, hselection => by
      have hrest :=
        staticScopedFieldsWithResponseName_mem_field_allowed schema boolCase
          lookupParent groundType responseName rest scopedSelection
          fieldResponseName fieldName arguments directives subselections
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase
                selectionDirectives
          · exact hrest
              (by simpa [staticScopedFieldsWithResponseName, hallow] using hmem)
              hselection
          · cases hresponse : selectionResponseName == responseName
            · exact hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow,
                    hresponse] using hmem)
                hselection
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field selectionResponseName
                            selectionFieldName selectionArguments
                            selectionDirectives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                injection hselection with _hresponse _hfield _harguments
                  hdirectives _hsubselections
                subst directives
                exact hallow
              · exact hrest htail hselection
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow]
                      using hmem)
                  hselection
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field_allowed
                      schema boolCase lookupParent groundType responseName
                      selectionSet scopedSelection fieldResponseName fieldName
                      arguments directives subselections hchild hselection
                · exact hrest htail hselection
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase
                      selectionDirectives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hbranch]
                      using hmem)
                  hselection
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field_allowed
                      schema boolCase typeCondition groundType responseName
                      selectionSet scopedSelection fieldResponseName fieldName
                      arguments directives subselections hchild hselection
                · exact hrest htail hselection

theorem completeScopedSelectionSetStaticFieldsWithResponseName_mem_field_allowed
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name) :
    ∀ scopedSelections scopedSelection fieldResponseName fieldName arguments
      directives subselections,
      scopedSelection ∈
          completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName scopedSelections ->
      scopedSelection.selection =
        Selection.field fieldResponseName fieldName arguments directives
          subselections ->
        directivesAllowIn boolCase directives = true
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, hmem, _hselection => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName] at hmem
  | head :: rest, scopedSelection, fieldResponseName, fieldName, arguments,
      directives, subselections, hmem, hselection => by
      have hrest :=
        completeScopedSelectionSetStaticFieldsWithResponseName_mem_field_allowed
          schema boolCase groundType responseName rest scopedSelection
          fieldResponseName fieldName arguments directives subselections
      cases head with
      | mk lookupParent selection =>
          cases selection with
          | field selectionResponseName selectionFieldName selectionArguments
              selectionDirectives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · exact hrest
                  (by
                    simpa [
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using hmem)
                  hselection
              · cases hresponse : selectionResponseName == responseName
                · exact hrest
                    (by
                      simpa [
                        completeScopedSelectionSetStaticFieldsWithResponseName,
                        hallow, hresponse] using hmem)
                    hselection
                · have hmem' :
                      scopedSelection =
                          { lookupParent := lookupParent,
                            selection :=
                              Selection.field selectionResponseName
                                selectionFieldName selectionArguments
                                selectionDirectives selectionSet }
                        ∨ scopedSelection ∈
                          completeScopedSelectionSetStaticFieldsWithResponseName
                            schema boolCase groundType responseName rest := by
                      simpa [
                        completeScopedSelectionSetStaticFieldsWithResponseName,
                        hallow, hresponse] using hmem
                  rcases hmem' with hhead | htail
                  · subst scopedSelection
                    injection hselection with _hresponse _hfield _harguments
                      hdirectives _hsubselections
                    subst directives
                    exact hallow
                  · exact hrest htail hselection
          | inlineFragment typeCondition selectionDirectives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase
                        selectionDirectives
                  · exact hrest
                      (by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hallow] using hmem)
                      hselection
                  · have hmem' :
                        scopedSelection ∈
                            staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              selectionSet
                          ∨ scopedSelection ∈
                            completeScopedSelectionSetStaticFieldsWithResponseName
                              schema boolCase groundType responseName rest := by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hallow] using hmem
                    rcases hmem' with hchild | htail
                    · exact
                        staticScopedFieldsWithResponseName_mem_field_allowed
                          schema boolCase lookupParent groundType
                          responseName selectionSet scopedSelection
                          fieldResponseName fieldName arguments directives
                          subselections hchild hselection
                    · exact hrest htail hselection
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase
                          selectionDirectives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · exact hrest
                      (by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hbranch] using hmem)
                      hselection
                  · have hmem' :
                        scopedSelection ∈
                            staticScopedFieldsWithResponseName schema
                              boolCase typeCondition groundType responseName
                              selectionSet
                          ∨ scopedSelection ∈
                            completeScopedSelectionSetStaticFieldsWithResponseName
                              schema boolCase groundType responseName rest := by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hbranch] using hmem
                    rcases hmem' with hchild | htail
                    · exact
                        staticScopedFieldsWithResponseName_mem_field_allowed
                          schema boolCase typeCondition groundType
                          responseName selectionSet scopedSelection
                          fieldResponseName fieldName arguments directives
                          subselections hchild hselection
                    · exact hrest htail hselection

theorem selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) (varName : BoolVar) :
    ∀ selectionSet,
      varName ∈ selectionSetBooleanVariables
          (eraseCompleteScopedSelectionSet
            (staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet)) ->
        varName ∈ selectionSetBooleanVariables selectionSet
  | [], hmem => by
      simp [staticScopedFieldsWithResponseName,
        eraseCompleteScopedSelectionSet, selectionSetBooleanVariables] at hmem
  | selection :: rest, hmem => by
      have hrest :=
        selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
          schema boolCase lookupParent groundType responseName varName rest
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · have hrestMem :
                varName ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet
                    (staticScopedFieldsWithResponseName schema boolCase
                      lookupParent groundType responseName rest)) := by
                simpa [staticScopedFieldsWithResponseName, hallow] using hmem
            exact
              selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                varName
                (Selection.field fieldResponseName fieldName arguments
                  directives selectionSet)
                rest (hrest hrestMem)
          · cases hresponse : fieldResponseName == responseName
            · have hrestMem :
                  varName ∈ selectionSetBooleanVariables
                    (eraseCompleteScopedSelectionSet
                      (staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest)) := by
                  simpa [staticScopedFieldsWithResponseName, hallow,
                    hresponse] using hmem
              exact
                selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                  varName
                  (Selection.field fieldResponseName fieldName arguments
                    directives selectionSet)
                  rest (hrest hrestMem)
            · have hmem' :
                  varName ∈
                    selectionBooleanVariables
                        (Selection.field fieldResponseName fieldName arguments
                          directives selectionSet)
                      ++ selectionSetBooleanVariables
                        (eraseCompleteScopedSelectionSet
                          (staticScopedFieldsWithResponseName schema boolCase
                            lookupParent groundType responseName rest)) := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse,
                    eraseCompleteScopedSelectionSet,
                    eraseCompleteScopedSelection,
                    selectionSetBooleanVariables] using hmem
              rcases List.mem_append.mp hmem' with hhead | htail
              · exact
                  selectionBooleanVariables_mem_selectionSetBooleanVariables_head
                    varName
                    (Selection.field fieldResponseName fieldName arguments
                      directives selectionSet)
                    rest hhead
              · exact
                  selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                    varName
                    (Selection.field fieldResponseName fieldName arguments
                      directives selectionSet)
                    rest (hrest htail)
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · have hrestMem :
                    varName ∈ selectionSetBooleanVariables
                      (eraseCompleteScopedSelectionSet
                        (staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using hmem
                exact
                  selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                    varName
                    (Selection.inlineFragment none directives selectionSet)
                    rest (hrest hrestMem)
              · have hmem' :
                    varName ∈
                      selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              selectionSet))
                        ++ selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hallow,
                      eraseCompleteScopedSelectionSet_append,
                      selectionSetBooleanVariables_append] using hmem
                rcases List.mem_append.mp hmem' with hchild | htail
                · exact
                    childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_inline_head
                      varName none directives selectionSet rest
                      (selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
                        schema boolCase lookupParent groundType responseName
                        varName selectionSet hchild)
                · exact
                    selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                      varName
                      (Selection.inlineFragment none directives selectionSet)
                      rest (hrest htail)
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · have hrestMem :
                    varName ∈ selectionSetBooleanVariables
                      (eraseCompleteScopedSelectionSet
                        (staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                exact
                  selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                    varName
                    (Selection.inlineFragment (some typeCondition) directives
                      selectionSet)
                    rest (hrest hrestMem)
              · have hmem' :
                    varName ∈
                      selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase typeCondition groundType responseName
                              selectionSet))
                        ++ selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hbranch,
                      eraseCompleteScopedSelectionSet_append,
                      selectionSetBooleanVariables_append] using hmem
                rcases List.mem_append.mp hmem' with hchild | htail
                · exact
                    childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_inline_head
                      varName (some typeCondition) directives selectionSet rest
                      (selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
                        schema boolCase typeCondition groundType responseName
                        varName selectionSet hchild)
                · exact
                    selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                      varName
                      (Selection.inlineFragment (some typeCondition) directives
                        selectionSet)
                      rest (hrest htail)

theorem sourceSelectionSetVariables_erase_staticScopedFieldsWithResponseName
    (operation : Operation) (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    (selectionSet : List Selection) :
    (∀ varName,
      varName ∈ selectionSetBooleanVariables selectionSet ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    ∀ varName,
      varName ∈ selectionSetBooleanVariables
          (eraseCompleteScopedSelectionSet
            (staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet)) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName
    (selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
      schema boolCase lookupParent groundType responseName varName
      selectionSet hmem)

theorem sourceSelectionSetVariables_merge_erase_staticScopedFieldsWithResponseName
    (operation : Operation) (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    (selectionSet : List Selection) :
    (∀ varName,
      varName ∈ selectionSetBooleanVariables selectionSet ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    ∀ varName,
      varName ∈ selectionSetBooleanVariables
          (mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName selectionSet))) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact
    sourceSelectionSetVariables_erase_staticScopedFieldsWithResponseName
      operation schema boolCase lookupParent groundType responseName
      selectionSet hsourceVars varName
      (mergeSelectionSetsBooleanVariables_mem_selectionSetBooleanVariables
        varName
        (eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet))
        hmem)

theorem sourceSelectionSetVariables_field_staticScoped_merged
    (operation : Operation)
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    (∀ varName,
      varName ∈ selectionSetBooleanVariables
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      varName ∈ selectionSetBooleanVariables operation.selectionSet) ->
    ∀ varName,
      varName ∈ selectionSetBooleanVariables
          (selectionSet ++
            mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest))) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  have hmem' :
      varName ∈ selectionSetBooleanVariables selectionSet
        ∨ varName ∈ selectionSetBooleanVariables
          (mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName rest))) := by
    have happend :
        varName ∈
          selectionSetBooleanVariables selectionSet
            ++ selectionSetBooleanVariables
              (mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest))) := by
      simpa [selectionSetBooleanVariables_append] using hmem
    exact List.mem_append.mp happend
  rcases hmem' with hchild | htail
  · exact sourceSelectionSetVariables_field_child operation responseName
      fieldName arguments directives selectionSet rest hsourceVars varName
      hchild
  · exact
      sourceSelectionSetVariables_merge_erase_staticScopedFieldsWithResponseName
        operation schema boolCase lookupParent groundType responseName rest
        (sourceSelectionSetVariables_tail operation
          (Selection.field responseName fieldName arguments directives
            selectionSet)
          rest hsourceVars)
        varName htail

end CompleteNormalization

end NormalForm

end GraphQL
