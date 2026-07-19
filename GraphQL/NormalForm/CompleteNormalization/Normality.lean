import GraphQL.NormalForm.CompleteNormalization.OperationNormality
import GraphQL.NormalForm.CompleteNormalization.StaticCollection
import GraphQL.NormalForm.GroundTypeNormalization.Normality

/-!
Normal-shape facts for complete normalization.
-/
namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

def completeOperationNormal (schema : Schema) (operation : Operation) : Prop :=
  selectionSetGroundTyped schema operation.selectionSet

mutual
  def bottomSelectionDirectiveFree : Selection -> Prop
    | .field _responseName _fieldName _arguments directives _selectionSet =>
        directives = []
    | .inlineFragment none directives selectionSet =>
        directives ≠ [] ∧ bottomSelectionSetDirectiveFree selectionSet
    | .inlineFragment (some _typeCondition) _directives _selectionSet =>
        False

  def bottomSelectionSetDirectiveFree : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        bottomSelectionDirectiveFree selection ∧ bottomSelectionSetDirectiveFree rest
end

def caseBodySelectionShape : Selection -> Prop
  | .field _responseName _fieldName _arguments directives _selectionSet =>
      directives = []
  | .inlineFragment (some _typeCondition) [] selectionSet =>
      bottomSelectionSetDirectiveFree selectionSet
  | _ => False

def caseBodySelectionSetShape (selectionSet : List Selection) : Prop :=
  ∀ selection, selection ∈ selectionSet -> caseBodySelectionShape selection

def boolCaseWrapperShape : List BoolVar -> List Selection -> Prop
  | [], selectionSet => caseBodySelectionSetShape selectionSet
  | _variable :: restVariables,
    [Selection.inlineFragment none directives selectionSet] =>
      directives ≠ [] ∧ boolCaseWrapperShape restVariables selectionSet
  | _variable :: _restVariables, _ => False

def boolCaseVars : BoolCase -> List BoolVar
  | [] => []
  | (varName, _value) :: rest => varName :: boolCaseVars rest

theorem boolCaseVars_cons (varName : BoolVar) (value : Bool) (boolCase : BoolCase)
    : boolCaseVars ((varName, value) :: boolCase)
      = varName :: boolCaseVars boolCase := by
  rfl

theorem boolCaseWrapperShape_wrapWithBoolCase
    : ∀ boolCase selectionSet,
        caseBodySelectionSetShape selectionSet
        -> boolCaseWrapperShape (boolCaseVars boolCase)
            (wrapWithBoolCase boolCase selectionSet)
  | [], selectionSet, hbody => hbody
  | (varName, value) :: rest, selectionSet, hbody => by
      simp [boolCaseVars, wrapWithBoolCase,
        boolCaseWrapperShape]
      exact boolCaseWrapperShape_wrapWithBoolCase rest
        selectionSet hbody

theorem boolCaseVars_of_mem_allBoolCases
    : ∀ {variables boolCase},
        boolCase ∈ allBoolCases variables -> boolCaseVars boolCase = variables
  | [], boolCase, hmem => by
      simp [allBoolCases] at hmem
      subst boolCase
      rfl
  | varName :: restVariables, boolCase, hmem => by
      simp [allBoolCases] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with ⟨restCase, hrestMem, hcase⟩
        subst boolCase
        simp [boolCaseVars,
          boolCaseVars_of_mem_allBoolCases hrestMem]
      · rcases hmem with ⟨restCase, hrestMem, hcase⟩
        subst boolCase
        simp [boolCaseVars,
          boolCaseVars_of_mem_allBoolCases hrestMem]

theorem boolCaseWrapperShape_wrapWithBoolCase_of_mem
    {variables : List BoolVar} {boolCase : BoolCase}
    {selectionSet : List Selection}
    : boolCase ∈ allBoolCases variables
      -> caseBodySelectionSetShape selectionSet
      -> boolCaseWrapperShape variables (wrapWithBoolCase boolCase selectionSet) := by
  intro hmem hbody
  have hvariables := boolCaseVars_of_mem_allBoolCases hmem
  rw [← hvariables]
  exact boolCaseWrapperShape_wrapWithBoolCase boolCase
    selectionSet hbody

theorem caseBodySelectionSetShape_singleton_of_mem
    {selection : Selection} {selectionSet : List Selection}
    : caseBodySelectionSetShape selectionSet
      -> selection ∈ selectionSet
      -> caseBodySelectionSetShape [selection] := by
  intro hbody hmem candidate hcandidate
  simp at hcandidate
  subst candidate
  exact hbody selection hmem

theorem boolCaseWrapperShape_singleton_of_mem_wrapWithBoolCase
    : ∀ boolCase selectionSet selection,
        caseBodySelectionSetShape selectionSet
        -> selection ∈ wrapWithBoolCase boolCase selectionSet
        -> boolCaseWrapperShape (boolCaseVars boolCase) [selection]
  | [], selectionSet, selection, hbody, hmem => by
      exact caseBodySelectionSetShape_singleton_of_mem hbody hmem
  | (varName, value) :: rest, selectionSet, selection, hbody, hmem => by
      simp [wrapWithBoolCase] at hmem
      subst selection
      simp [boolCaseVars, boolCaseWrapperShape]
      exact boolCaseWrapperShape_wrapWithBoolCase rest
        selectionSet hbody

theorem boolCaseWrapperShape_singleton_of_mem_wrapWithBoolCase_of_mem
    {variables : List BoolVar} {boolCase : BoolCase}
    {selectionSet : List Selection} {selection : Selection}
    : boolCase ∈ allBoolCases variables
      -> caseBodySelectionSetShape selectionSet
      -> selection ∈ wrapWithBoolCase boolCase selectionSet
      -> boolCaseWrapperShape variables [selection] := by
  intro hmem hbody hselection
  have hvariables := boolCaseVars_of_mem_allBoolCases hmem
  rw [← hvariables]
  exact
    boolCaseWrapperShape_singleton_of_mem_wrapWithBoolCase
      boolCase selectionSet selection hbody hselection

theorem bottomSelectionSetDirectiveFree_of_allFields_noDirectives
    : ∀ selectionSet,
        selectionsAllFields selectionSet
        -> (∀ responseName fieldName arguments directives subselections,
              Selection.field responseName fieldName arguments directives subselections
                ∈ selectionSet
              -> directives = [])
        -> bottomSelectionSetDirectiveFree selectionSet
  | [], _hall, _hdirectives => by
      simp [bottomSelectionSetDirectiveFree]
  | selection :: rest, hall, hdirectives => by
      have hrestAll : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have hrestDirectives :
          ∀ responseName fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives
              subselections ∈ rest ->
              directives = [] := by
        intro responseName fieldName arguments directives subselections hmem
        exact hdirectives responseName fieldName arguments directives
          subselections (List.mem_cons_of_mem selection hmem)
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      cases selection with
      | field responseName fieldName arguments directives subselections =>
          have hdirectivesHead :
              directives = [] :=
            hdirectives responseName fieldName arguments directives
              subselections (by simp)
          simp [bottomSelectionSetDirectiveFree,
            bottomSelectionDirectiveFree, hdirectivesHead,
            bottomSelectionSetDirectiveFree_of_allFields_noDirectives rest
              hrestAll hrestDirectives]
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem bottomSelectionDirectiveFree_of_mem {selection : Selection}
    : ∀ {selectionSet},
        bottomSelectionSetDirectiveFree selectionSet
        -> selection ∈ selectionSet
        -> bottomSelectionDirectiveFree selection
  | [], hbottom, hmem => by
      simp at hmem
  | head :: rest, hbottom, hmem => by
      simp [bottomSelectionSetDirectiveFree] at hbottom
      simp at hmem
      rcases hmem with hhead | htail
      · cases hhead
        exact hbottom.1
      · exact bottomSelectionDirectiveFree_of_mem hbottom.2 htail

theorem bottomSelectionSetDirectiveFree_singleton {selection : Selection}
    : bottomSelectionDirectiveFree selection
      -> bottomSelectionSetDirectiveFree [selection] := by
  intro hselection
  simp [bottomSelectionSetDirectiveFree, hselection]

theorem selectionDirectiveFree_of_mem {selection : Selection}
    : ∀ {selectionSet},
        selectionSetDirectiveFree selectionSet
        -> selection ∈ selectionSet
        -> selectionDirectiveFree selection
  | [], _hfree, hmem => by
      simp at hmem
  | head :: rest, hfree, hmem => by
      simp at hmem
      rcases hmem with hhead | htail
      · subst head
        exact hfree.1
      · exact selectionDirectiveFree_of_mem hfree.2 htail

theorem caseBodySelectionShape_of_field_directiveFree {selection : Selection}
    : Selection.isField selection
      -> selectionDirectiveFree selection
      -> caseBodySelectionShape selection := by
  intro hfield hfree
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      rcases hfree with ⟨hdirectives, _hselectionSet⟩
      simpa [caseBodySelectionShape] using hdirectives
  | inlineFragment typeCondition directives selectionSet =>
      simp [Selection.isField] at hfield

theorem caseBodySelectionSetShape_of_allFields_directiveFree
    {selectionSet : List Selection}
    : selectionsAllFields selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> caseBodySelectionSetShape selectionSet := by
  intro hall hfree selection hmem
  exact caseBodySelectionShape_of_field_directiveFree
    (hall selection hmem)
    (selectionDirectiveFree_of_mem hfree hmem)

theorem staticCollectForGround_bottomDirectiveFree
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name) (boolCase : BoolCase)
    (selectionSet : List Selection)
    : bottomSelectionSetDirectiveFree
        (staticCollectForGround schema variables lookupParent
          groundType boolCase selectionSet) := by
  apply bottomSelectionSetDirectiveFree_of_allFields_noDirectives
  · exact staticCollectForGround_allFields schema variables
      lookupParent groundType boolCase selectionSet
  · intro responseName fieldName arguments directives subselections hmem
    rcases
      staticCollectForGround_field_shape schema variables
        lookupParent groundType boolCase hmem with
      ⟨matchedResponseName, matchedFieldName, matchedArguments,
        matchedSelectionSet, hshape⟩
    cases hshape
    rfl

theorem staticCollectForGround_caseBodyShape
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name) (boolCase : BoolCase)
    (selectionSet : List Selection)
    : caseBodySelectionSetShape
        (staticCollectForGround schema variables lookupParent
          groundType boolCase selectionSet) := by
  intro selection hmem
  rcases
    staticCollectForGround_field_shape schema variables
      lookupParent groundType boolCase hmem with
    ⟨matchedResponseName, matchedFieldName, matchedArguments,
      matchedSelectionSet, hshape⟩
  cases hshape
  simp [caseBodySelectionShape]

theorem normalizeBoolCaseForType_caseBodyShape
    (schema : Schema) (boolCase : BoolCase) (returnType : Name)
    (selectionSet : List Selection)
    : caseBodySelectionSetShape
        (normalizeBoolCaseForType schema boolCase returnType selectionSet) := by
  apply caseBodySelectionSetShape_of_allFields_directiveFree
  · simpa [normalizeBoolCaseForType] using
      GroundTypeNormalization.normalizeSelectionSet_allFields schema
        returnType (filterSelectionSetBoolCase boolCase selectionSet)
  · simpa [normalizeBoolCaseForType] using
      GroundTypeNormalization.normalizeSelectionSet_directiveFree schema
        returnType (filterSelectionSetBoolCase boolCase selectionSet)
        (filterSelectionSetBoolCase_directiveFree schema boolCase selectionSet)

def groundBranchShape (_variables : List BoolVar) : Selection -> Prop
  | .inlineFragment (some _typeCondition) [] selectionSet =>
      bottomSelectionSetDirectiveFree selectionSet
  | _ => False

def completeBranchShape (variables : List BoolVar) : Selection -> Prop :=
  fun selection =>
    groundBranchShape variables selection ∨ boolCaseWrapperShape variables [selection]

def completeSelectionSetShape (variables : List BoolVar) (selectionSet : List Selection)
    : Prop :=
  ∀ selection,
    selection ∈ selectionSet
    -> Selection.isField selection ∨ completeBranchShape variables selection

def completeOperationShape (schema : Schema)
    (variables : List BoolVar) (operation : Operation)
    : Prop :=
  completeOperationNormal schema operation
  ∧ completeSelectionSetShape variables operation.selectionSet

theorem normalizeForType_leaf
    (schema : Schema) (variables : List BoolVar) (returnType : Name)
    (selectionSet : List Selection)
    : leafTypeNameBool schema returnType = true
      -> normalizeForType schema variables returnType selectionSet = [] := by
  intro hleaf
  simp [normalizeForType, hleaf]

theorem boolCaseBranchesForGround_layerShape
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (selectionSet : List Selection)
    : selectionsAllFields
        (boolCaseBranchesForGround schema groundType variables selectionSet)
      ∨ selectionsAllInlineFragments
          (boolCaseBranchesForGround schema groundType variables selectionSet) := by
  cases variables with
  | nil =>
      apply Or.inl
      simp [boolCaseBranchesForGround, allBoolCases,
        wrapWithBoolCase]
      exact staticCollectForGround_allFields schema [] groundType
        groundType [] selectionSet
  | cons varName rest =>
      apply Or.inr
      intro selection hmem
      simp [boolCaseBranchesForGround, allBoolCases,
        wrapWithBoolCase] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with
          ⟨branch, ⟨boolCase, _hcase, hbranch⟩, hselection⟩
        subst branch
        simp at hselection
        subst selection
        simp [Selection.isInlineFragment]
      · rcases hmem with
          ⟨branch, ⟨boolCase, _hcase, hbranch⟩, hselection⟩
        subst branch
        simp at hselection
        subst selection
        simp [Selection.isInlineFragment]

theorem boolCaseBranchesForGround_boolCaseWrapperShape
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (selectionSet : List Selection)
    : ∀ selection,
        selection ∈ boolCaseBranchesForGround schema groundType variables selectionSet
        -> boolCaseWrapperShape variables [selection] := by
  cases variables with
  | nil =>
      intro selection hmem
      have hbottom :=
        staticCollectForGround_caseBodyShape schema []
          groundType groundType [] selectionSet
      have hselectionBottom :=
        caseBodySelectionSetShape_singleton_of_mem hbottom (by
          simpa [boolCaseBranchesForGround, allBoolCases,
            wrapWithBoolCase] using hmem)
      exact hselectionBottom
  | cons varName restVariables =>
      intro selection hmem
      simp [boolCaseBranchesForGround, allBoolCases,
        wrapWithBoolCase] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with
          ⟨branch, ⟨boolCase, hcase, hbranch⟩, hselection⟩
        subst branch
        simp at hselection
        subst selection
        simp [boolCaseWrapperShape]
        exact boolCaseWrapperShape_wrapWithBoolCase_of_mem
          hcase
          (staticCollectForGround_caseBodyShape schema
            (varName :: restVariables) groundType groundType
            ((varName, false) :: boolCase) selectionSet)
      · rcases hmem with
          ⟨branch, ⟨boolCase, hcase, hbranch⟩, hselection⟩
        subst branch
        simp at hselection
        subst selection
        simp [boolCaseWrapperShape]
        exact boolCaseWrapperShape_wrapWithBoolCase_of_mem
          hcase
          (staticCollectForGround_caseBodyShape schema
            (varName :: restVariables) groundType groundType
            ((varName, true) :: boolCase) selectionSet)

theorem boolCaseBranchesForGround_completeSelectionSetShape
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (selectionSet : List Selection)
    : completeSelectionSetShape variables
        (boolCaseBranchesForGround schema groundType variables selectionSet) := by
  intro selection hmem
  exact Or.inr (Or.inr
    (boolCaseBranchesForGround_boolCaseWrapperShape schema variables
      groundType selectionSet selection hmem))

theorem normalizeForType_boolCaseWrapperShape
    (schema : Schema) (variables : List BoolVar)
    (returnType : Name) (selectionSet : List Selection)
    : ∀ selection,
        selection ∈ normalizeForType schema variables returnType selectionSet
        -> boolCaseWrapperShape variables [selection] := by
  intro selection hmem
  cases hleaf : leafTypeNameBool schema returnType with
  | true =>
      simp [normalizeForType, hleaf] at hmem
  | false =>
      simp [normalizeForType, hleaf] at hmem
      rcases hmem with ⟨branch, ⟨boolCase, hcase, hbranch⟩,
        hselection⟩
      subst branch
      exact
        boolCaseWrapperShape_singleton_of_mem_wrapWithBoolCase_of_mem
          hcase
          (normalizeBoolCaseForType_caseBodyShape
            schema boolCase returnType selectionSet)
          hselection

theorem normalizeForType_completeSelectionSetShape
    (schema : Schema) (variables : List BoolVar) (returnType : Name)
    (selectionSet : List Selection)
    : completeSelectionSetShape variables
        (normalizeForType schema variables returnType selectionSet) := by
  intro selection hmem
  exact Or.inr (Or.inr
    (normalizeForType_boolCaseWrapperShape schema
      variables returnType selectionSet selection hmem))

theorem completeNormalizeRootSelectionSetShape
    (schema : Schema) (variables : List BoolVar) (parentType : Name)
    (selectionSet normalizedSelectionSet : List Selection)
    : completeNormalizeRootSelectionSet schema variables parentType selectionSet
        = normalizedSelectionSet
      -> completeSelectionSetShape variables normalizedSelectionSet := by
  intro hnormalized selection hmem
  unfold completeNormalizeRootSelectionSet at hnormalized
  let branches :=
    List.flatten ((allBoolCases variables).map
      (fun boolCase =>
        match normalizeBoolCaseForType schema boolCase parentType
            selectionSet with
        | [] => []
        | selection :: rest =>
            wrapWithBoolCase boolCase (selection :: rest)))
  change branches = normalizedSelectionSet at hnormalized
  subst normalizedSelectionSet
  have hflattenMem : selection ∈ branches := hmem
  unfold branches at hflattenMem
  rw [List.mem_flatten] at hflattenMem
  rcases hflattenMem with ⟨branch, hbranchMem, hselection⟩
  rw [List.mem_map] at hbranchMem
  rcases hbranchMem with ⟨boolCase, hcase, hbranch⟩
  subst branch
  cases hbody :
      normalizeBoolCaseForType schema boolCase parentType selectionSet with
  | nil =>
      simp [hbody] at hselection
  | cons bodyHead bodyTail =>
      exact Or.inr (Or.inr
        (boolCaseWrapperShape_singleton_of_mem_wrapWithBoolCase_of_mem
          hcase
          (normalizeBoolCaseForType_caseBodyShape schema boolCase
            parentType selectionSet)
          (by simpa [hbody] using hselection)))

theorem completeNormalizeOperation_selectionSetShape
    (schema : Schema) (operation : Operation)
    : completeSelectionSetShape (operationBoolVars operation)
        (completeNormalizeOperation schema operation).selectionSet := by
  exact completeNormalizeRootSelectionSetShape schema
    (operationBoolVars operation) operation.rootType operation.selectionSet
    (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
      operation.rootType operation.selectionSet)
    rfl

theorem completeNormalizeOperation_rootSelectionSetShape
    (schema : Schema) (operation : Operation)
    : completeSelectionSetShape (operationBoolVars operation)
        (completeNormalizeOperation schema operation).selectionSet := by
  exact completeNormalizeOperation_selectionSetShape schema operation

end CompleteNormalization

end NormalForm

end GraphQL
