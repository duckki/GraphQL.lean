import GraphQL.Algorithms.ExecutionUngrouped
import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Final
import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Recursive
import GraphQL.NormalForm.GroundTypeNormalization.FieldCollection
import GraphQL.NormalForm.GroundTypeNormalization.Normality
import GraphQL.NormalForm.GroundTypeNormalization.Semantics
import GraphQL.NormalForm.GroundTypeNormalization.Validity
import GraphQL.NormalForm.CompleteNormalization.Variables
import GraphQL.NormalForm.CompleteNormalization.OperationNormality
import GraphQL.NormalForm.CompleteNormalization.Semantics
import GraphQL.NormalForm.CompleteNormalization.FilterReadiness
import GraphQL.NormalForm.Shared.Execution

/-!
Semantic preservation for the ungrouped execution algorithm.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

variable {ObjectRef : Type}

theorem lookupResponseField?_eq_none_of_not_mem
    {responseName : Name} :
    ∀ fields : List (Name × Execution.Response),
      responseName ∉ fields.map Prod.fst ->
        lookupResponseField? responseName fields = none
  | [], _hnotMem => by
      rfl
  | (fieldResponseName, response) :: rest, hnotMem => by
      have hhead : fieldResponseName ≠ responseName := by
        intro heq
        exact hnotMem (by simp [heq])
      have htail : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotMem (by simp [hmem])
      have hfalse : (fieldResponseName == responseName) = false := by
        cases hmatch : fieldResponseName == responseName
        · rfl
        · exact False.elim (hhead (beq_iff_eq.mp hmatch))
      simp [lookupResponseField?, hfalse,
        lookupResponseField?_eq_none_of_not_mem rest htail]

theorem responseObjectField?_eq_none_of_not_mem
    {responseName : Name} {fields : List (Name × Execution.Response)} :
    responseName ∉ fields.map Prod.fst ->
      responseObjectField? responseName (Execution.Response.object fields) =
        none := by
  intro hnotMem
  exact lookupResponseField?_eq_none_of_not_mem fields hnotMem

theorem mergeResponseField_eq_append_of_not_mem
    {responseName : Name} (incoming : Execution.Response) :
    ∀ fields : List (Name × Execution.Response),
      responseName ∉ fields.map Prod.fst ->
        mergeResponseField responseName incoming fields =
          fields ++ [(responseName, incoming)]
  | [], _hnotMem => by
      simp [mergeResponseField]
  | (fieldResponseName, existing) :: rest, hnotMem => by
      have hhead : fieldResponseName ≠ responseName := by
        intro heq
        exact hnotMem (by simp [heq])
      have htail : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotMem (by simp [hmem])
      have hfalse : (fieldResponseName == responseName) = false := by
        cases hmatch : fieldResponseName == responseName
        · rfl
        · exact False.elim (hhead (beq_iff_eq.mp hmatch))
      simp [mergeResponseField, hfalse,
        mergeResponseField_eq_append_of_not_mem incoming rest htail]

theorem mergeResponseFieldIntoObject_eq_append_of_not_mem
    {responseName : Name} (incoming : Execution.Response)
    {fields : List (Name × Execution.Response)} :
    responseName ∉ fields.map Prod.fst ->
      mergeResponseFieldIntoObject responseName incoming
          (Execution.Response.object fields)
        =
        Execution.Response.object (fields ++ [(responseName, incoming)]) := by
  intro hnotMem
  simp [mergeResponseFieldIntoObject,
    mergeResponseField_eq_append_of_not_mem incoming fields hnotMem]

theorem foldlCompleteValues_no_previous_eq_map
    (complete :
      Execution.Value ObjectRef -> Execution.Response -> Execution.Response) :
    ∀ (values : List (Execution.Value ObjectRef))
      (acc : List Execution.Response),
      ((values.foldl
        (fun (state : List Execution.Response × List Execution.Response)
            value =>
          (complete value
              (match state.snd with
              | [] => Execution.Response.null
              | previous :: _rest => previous) ::
              state.fst,
            match state.snd with
            | [] => []
            | _previous :: rest => rest))
        (acc, [])).fst).reverse =
        acc.reverse ++ values.map (fun value =>
          complete value Execution.Response.null)
  | [], acc => by
      simp
  | value :: rest, acc => by
      simpa [List.append_assoc] using
        foldlCompleteValues_no_previous_eq_map complete rest
          (complete value Execution.Response.null :: acc)

theorem visitSubfields_append
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef) :
    ∀ (left right : List Selection) output,
      visitSubfields schema resolvers variableValues depth parentType source
          (left ++ right) output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        right
        (visitSubfields schema resolvers variableValues depth parentType
          source left output)
  | [], _right, _output => by
      simp [visitSubfields]
  | selection :: rest, right, output => by
      simp [visitSubfields,
        visitSubfields_append schema resolvers variableValues depth
          parentType source rest right]

theorem visitSubfields_wrapWithBoolCase_empty
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef) :
    ∀ boolCase output,
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase boolCase []) output
        =
      output
  | [], output => by
      simp [NormalForm.wrapWithBoolCase, visitSubfields]
  | (varName, value) :: rest, output => by
      cases hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [NormalForm.directiveForBit varName value]
      · simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection,
          hallow]
      · simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection,
          hallow,
          visitSubfields_wrapWithBoolCase_empty schema resolvers
            variableValues depth parentType source rest output]

theorem visitSubfields_wrapWithBoolCase_cons_allowed
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.Response) :
    Execution.selectionDirectivesAllowBool variableValues
        [NormalForm.directiveForBit varName value] = true ->
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase
            ((varName, value) :: rest) selectionSet) output
        =
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase rest selectionSet) output := by
  intro hallow
  simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection, hallow]

theorem visitSubfields_wrapWithBoolCase_cons_skipped
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.Response) :
    Execution.selectionDirectivesAllowBool variableValues
        [NormalForm.directiveForBit varName value] = false ->
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase
            ((varName, value) :: rest) selectionSet) output
        =
      output := by
  intro hallow
  simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection, hallow]

theorem visitSubfields_wrapWithBoolCase_cons_mismatch
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.Response) :
    Execution.inputValueBoolean? variableValues (.variable varName)
        = some (!value) ->
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase
            ((varName, value) :: rest) selectionSet) output
        =
      output := by
  intro hmismatch
  exact visitSubfields_wrapWithBoolCase_cons_skipped schema resolvers
    variableValues depth parentType source varName value rest selectionSet
    output
    (NormalForm.CompleteNormalization.selectionDirectivesAllowBool_boolCaseBit_of_mismatch
      variableValues varName value hmismatch)

theorem visitSubfields_wrapWithBoolCase_of_mismatch_pair
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) :
    ∀ boolCase (varName : NormalForm.BoolVar) (value : Bool),
      (varName, value) ∈ boolCase ->
      Execution.inputValueBoolean? variableValues (.variable varName)
        = some (!value) ->
      ∀ output,
        visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase boolCase selectionSet) output
          =
        output
  | [], _varName, _value, hpair, _hmismatch, _output => by
      cases hpair
  | (headVar, headValue) :: rest, varName, value, hpair, hmismatch,
      output => by
      simp at hpair
      rcases hpair with hhead | htail
      · have hvar : varName = headVar := hhead.1
        have hvalue : value = headValue := hhead.2
        subst varName
        subst value
        exact visitSubfields_wrapWithBoolCase_cons_mismatch schema
          resolvers variableValues depth parentType source headVar headValue
          rest selectionSet output hmismatch
      · cases hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [NormalForm.directiveForBit headVar headValue]
        · exact visitSubfields_wrapWithBoolCase_cons_skipped schema
            resolvers variableValues depth parentType source headVar
            headValue rest selectionSet output hallow
        · have htailVisit :=
            visitSubfields_wrapWithBoolCase_of_mismatch_pair schema
              resolvers variableValues depth parentType source selectionSet
              rest varName value htail hmismatch output
          exact
            (visitSubfields_wrapWithBoolCase_cons_allowed schema
              resolvers variableValues depth parentType source headVar
              headValue rest selectionSet output hallow).trans htailVisit

theorem visitSubfields_wrapWithBoolCase_of_agrees
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) :
    ∀ boolCase,
      (∀ varName value, (varName, value) ∈ boolCase ->
        Execution.inputValueBoolean? variableValues (.variable varName)
          =
        some value) ->
      ∀ output,
        visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase boolCase selectionSet) output
          =
        visitSubfields schema resolvers variableValues depth parentType source
          selectionSet output
  | [], _hagrees, output => by
      rfl
  | (varName, value) :: rest, hagrees, output => by
      have hhead :
          Execution.selectionDirectivesAllowBool variableValues
              [NormalForm.directiveForBit varName value] = true :=
        NormalForm.CompleteNormalization.selectionDirectivesAllowBool_boolCaseBit_of_agrees
          variableValues varName value (hagrees varName value (by simp))
      have hrest :
          visitSubfields schema resolvers variableValues depth parentType
              source (NormalForm.wrapWithBoolCase rest selectionSet) output
            =
          visitSubfields schema resolvers variableValues depth parentType
              source selectionSet output :=
        visitSubfields_wrapWithBoolCase_of_agrees schema resolvers
          variableValues depth parentType source selectionSet rest
          (by
            intro restVar restValue hmem
            exact hagrees restVar restValue (by simp [hmem]))
          output
      exact
        (visitSubfields_wrapWithBoolCase_cons_allowed schema resolvers
          variableValues depth parentType source varName value rest
          selectionSet output hhead).trans hrest

theorem visitSubfields_wrapWithBoolCase_of_variableValuesAgree
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (variables : List NormalForm.BoolVar)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.Response) :
    (∀ varName value, (varName, value) ∈ boolCase ->
      varName ∈ variables ∧ NormalForm.BoolCase.lookup? boolCase varName =
        some value) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues boolCase variables ->
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase boolCase selectionSet) output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet output := by
  intro hcase hagrees
  exact visitSubfields_wrapWithBoolCase_of_agrees schema resolvers
    variableValues depth parentType source selectionSet boolCase
    (by
      intro varName value hmem
      rcases hcase varName value hmem with ⟨hvar, hvalue⟩
      exact (hagrees varName hvar).trans hvalue)
    output

theorem visitSubfields_wrapWithBoolCase_of_mem_allBoolCases
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (variables : List NormalForm.BoolVar)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.Response) :
    variables.Nodup ->
    boolCase ∈ NormalForm.allBoolCases variables ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues boolCase variables ->
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase boolCase selectionSet) output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet output := by
  intro hnodup hmem hagrees
  exact
    visitSubfields_wrapWithBoolCase_of_variableValuesAgree schema resolvers
      variableValues depth parentType source variables boolCase selectionSet
      output
      (by
        intro varName value hpair
        exact ⟨
          NormalForm.CompleteNormalization.boolCase_pair_variable_mem_of_allBoolCases
            hmem hpair,
          NormalForm.CompleteNormalization.BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
            hnodup hmem hpair⟩)
      hagrees

theorem visitSubfields_flatten_boolCaseWrappers_nonruntime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection) :
    ∀ (boolCases : List NormalForm.BoolCase) output,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
      (∀ candidateCase, candidateCase ∈ boolCases ->
        candidateCase ∈
          NormalForm.allBoolCases (NormalForm.operationBoolVars operation)) ->
      (∀ candidateCase, candidateCase ∈ boolCases ->
        candidateCase ≠ runtimeCase) ->
        visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              (boolCases.map (fun boolCase =>
                NormalForm.wrapWithBoolCase boolCase
                  (selectionSetForCase boolCase))))
            output
          =
        output
  | [], output, _hruntime, _hagrees, _hall, _hne => by
      simp [visitSubfields]
  | candidateCase :: restCases, output, hruntime, hagrees, hall, hne => by
      have hcandidate :
          candidateCase ∈
            NormalForm.allBoolCases
              (NormalForm.operationBoolVars operation) :=
        hall candidateCase (by simp)
      have hcandidateNe :
          candidateCase ≠ runtimeCase :=
        hne candidateCase (by simp)
      rcases
          NormalForm.CompleteNormalization.operationBoolVars_case_mismatch_of_ne
            variableValues operation hruntime hcandidate hagrees
            hcandidateNe with
        ⟨varName, value, hpair, hmismatch⟩
      have hhead :
          visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase candidateCase
                (selectionSetForCase candidateCase))
              output
            =
          output :=
        visitSubfields_wrapWithBoolCase_of_mismatch_pair schema resolvers
          variableValues depth parentType source
          (selectionSetForCase candidateCase)
          candidateCase varName value hpair hmismatch output
      have hrest :
          visitSubfields schema resolvers variableValues depth parentType source
              (List.flatten
                (restCases.map (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase
                    (selectionSetForCase boolCase))))
              output
            =
          output :=
        visitSubfields_flatten_boolCaseWrappers_nonruntime schema resolvers
          variableValues operation depth parentType source runtimeCase
          selectionSetForCase restCases output hruntime hagrees
          (by
            intro boolCase hmem
            exact hall boolCase (by simp [hmem]))
          (by
            intro boolCase hmem
            exact hne boolCase (by simp [hmem]))
      simp [List.flatten_cons,
        visitSubfields_append schema resolvers variableValues depth
          parentType source
          (NormalForm.wrapWithBoolCase candidateCase
            (selectionSetForCase candidateCase))
          (List.flatten
            (restCases.map (fun boolCase =>
              NormalForm.wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
          output,
        hhead, hrest]

theorem visitSubfields_flatten_boolCaseWrappers_split_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    (before after : List NormalForm.BoolCase)
    (output : Execution.Response) :
    NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
        =
      before ++ runtimeCase :: after ->
    (∀ candidate, candidate ∈ before -> candidate ≠ runtimeCase) ->
    (∀ candidate, candidate ∈ after -> candidate ≠ runtimeCase) ->
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
      visitSubfields schema resolvers variableValues depth parentType source
          (List.flatten
            ((NormalForm.allBoolCases
              (NormalForm.operationBoolVars operation)).map
              (fun boolCase =>
                NormalForm.wrapWithBoolCase boolCase
                  (selectionSetForCase boolCase))))
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (selectionSetForCase runtimeCase) output := by
  intro hsplit hbeforeNe hafterNe hruntime hagrees
  have hbeforeAll :
      ∀ candidateCase, candidateCase ∈ before ->
        candidateCase ∈
          NormalForm.allBoolCases (NormalForm.operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hafterAll :
      ∀ candidateCase, candidateCase ∈ after ->
        candidateCase ∈
          NormalForm.allBoolCases (NormalForm.operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hbeforeVisit :
      visitSubfields schema resolvers variableValues depth parentType source
          (List.flatten
            (before.map (fun boolCase =>
              NormalForm.wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
          output
        =
      output :=
    visitSubfields_flatten_boolCaseWrappers_nonruntime schema resolvers
      variableValues operation depth parentType source runtimeCase
      selectionSetForCase before output hruntime hagrees hbeforeAll
      hbeforeNe
  let runtimeOutput :=
    visitSubfields schema resolvers variableValues depth parentType source
      (selectionSetForCase runtimeCase) output
  have hafterVisit :
      visitSubfields schema resolvers variableValues depth parentType source
          (List.flatten
            (after.map (fun boolCase =>
              NormalForm.wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
          runtimeOutput
        =
      runtimeOutput :=
    visitSubfields_flatten_boolCaseWrappers_nonruntime schema resolvers
      variableValues operation depth parentType source runtimeCase
      selectionSetForCase after runtimeOutput hruntime hagrees hafterAll
      hafterNe
  have hruntimeVisit :
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase runtimeCase
            (selectionSetForCase runtimeCase))
          output
        =
      runtimeOutput :=
    visitSubfields_wrapWithBoolCase_of_mem_allBoolCases schema resolvers
      variableValues depth parentType source
      (NormalForm.operationBoolVars operation) runtimeCase
      (selectionSetForCase runtimeCase) output
      (NormalForm.CompleteNormalization.operationBoolVars_nodup operation)
      hruntime hagrees
  rw [hsplit]
  simp [List.map_append, List.flatten_append,
    visitSubfields_append]
  rw [hbeforeVisit, hruntimeVisit]
  exact hafterVisit

theorem visitSubfields_flatten_boolCaseWrappers_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    (output : Execution.Response) :
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
      visitSubfields schema resolvers variableValues depth parentType source
          (List.flatten
            ((NormalForm.allBoolCases
              (NormalForm.operationBoolVars operation)).map
              (fun boolCase =>
                NormalForm.wrapWithBoolCase boolCase
                  (selectionSetForCase boolCase))))
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (selectionSetForCase runtimeCase) output := by
  intro hruntime hagrees
  rcases
      NormalForm.CompleteNormalization.allBoolCases_operationBoolVars_split
        operation hruntime with
    ⟨before, after, hsplit, hbeforeNe, hafterNe⟩
  exact visitSubfields_flatten_boolCaseWrappers_split_runtime schema
    resolvers variableValues operation depth parentType source runtimeCase
    selectionSetForCase before after output hsplit hbeforeNe hafterNe
    hruntime hagrees

theorem visitSubfields_completeRootBranch_eq_wrapped
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection)
    (output : Execution.Response) :
    visitSubfields schema resolvers variableValues depth parentType source
        (match selectionSet with
        | [] => []
        | selection :: rest =>
            NormalForm.wrapWithBoolCase boolCase (selection :: rest))
        output
      =
    visitSubfields schema resolvers variableValues depth parentType source
      (NormalForm.wrapWithBoolCase boolCase selectionSet) output := by
  cases selectionSet with
  | nil =>
      simpa [visitSubfields] using
        (visitSubfields_wrapWithBoolCase_empty schema resolvers
          variableValues depth parentType source boolCase output).symm
  | cons selection rest =>
      rfl

theorem visitSubfields_completeNormalizeRootSelectionSet_eq_wrapped
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (variables : List NormalForm.BoolVar)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) :
    ∀ output,
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.completeNormalizeRootSelectionSet schema variables
            parentType selectionSet)
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (List.flatten ((NormalForm.allBoolCases variables).map
          (fun boolCase =>
            NormalForm.wrapWithBoolCase boolCase
              (NormalForm.normalizeSelectionSet schema parentType
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)))))
        output := by
  unfold NormalForm.completeNormalizeRootSelectionSet
  induction NormalForm.allBoolCases variables with
  | nil =>
      intro output
      simp [visitSubfields]
  | cons boolCase rest ih =>
      intro output
      simp [List.flatten_cons, visitSubfields_append]
      have hhead :=
        visitSubfields_completeRootBranch_eq_wrapped schema resolvers
          variableValues depth parentType source boolCase
          (NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase boolCase selectionSet))
          output
      exact
        (congrArg
          (fun nextOutput =>
            visitSubfields schema resolvers variableValues depth parentType
              source
              (List.flatten
                (rest.map (fun boolCase =>
                  match NormalForm.normalizeSelectionSet schema parentType
                      (NormalForm.filterSelectionSetBoolCase boolCase
                        selectionSet) with
                  | [] => []
                  | selection :: rest =>
                      NormalForm.wrapWithBoolCase boolCase
                        (selection :: rest))))
              nextOutput)
          hhead).trans
          (ih
            (visitSubfields schema resolvers variableValues depth parentType
              source
              (NormalForm.wrapWithBoolCase boolCase
                (NormalForm.normalizeSelectionSet schema parentType
                  (NormalForm.filterSelectionSetBoolCase boolCase
                    selectionSet)))
              output))

theorem visitSubfields_completeNormalizeRootSelectionSet_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSet : List Selection)
    (output : Execution.Response) :
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.completeNormalizeRootSelectionSet schema
            (NormalForm.operationBoolVars operation) parentType selectionSet)
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (NormalForm.normalizeSelectionSet schema parentType
          (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet))
        output := by
  intro hruntime hagrees
  rw [visitSubfields_completeNormalizeRootSelectionSet_eq_wrapped schema
    resolvers variableValues (NormalForm.operationBoolVars operation)
    depth parentType source selectionSet output]
  exact visitSubfields_flatten_boolCaseWrappers_runtime schema resolvers
    variableValues operation depth parentType source runtimeCase
    (fun boolCase =>
      NormalForm.normalizeSelectionSet schema parentType
        (NormalForm.filterSelectionSetBoolCase boolCase selectionSet))
    output hruntime hagrees

mutual
  def completeValue_filterSelectionSetBoolCase_eq
      (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (operation : Operation) (boolCase : NormalForm.BoolCase)
      (hagrees :
        NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues boolCase (NormalForm.operationBoolVars operation)) :
      ∀ depth parentType selectionSet (value : Execution.Value ObjectRef)
          previous,
        (∀ varName,
          varName ∈ NormalForm.selectionSetBooleanVariables selectionSet ->
            varName ∈
              NormalForm.selectionSetBooleanVariables operation.selectionSet) ->
          completeValue schema resolvers variableValues depth parentType
              (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
              value previous
            =
          completeValue schema resolvers variableValues depth parentType
            selectionSet value previous
    | 0, _parentType, _selectionSet, _value, _previous, _hvars => by
        simp [completeValue]
    | depth + 1, parentType, selectionSet, .null, previous, hvars => by
        simp [completeValue]
    | depth + 1, parentType, selectionSet, .scalar value, previous, hvars => by
        simp [completeValue]
    | depth + 1, parentType, selectionSet, .object runtimeType ref, previous,
        hvars => by
        cases hinclude : schema.typeIncludesObjectBool parentType runtimeType
        · rw [completeValue.eq_def, completeValue.eq_def]
          simp [hinclude]
        · rw [completeValue.eq_def, completeValue.eq_def]
          simp only [hinclude, ↓reduceIte]
          change
            visitSubfields schema resolvers variableValues depth runtimeType
                (Execution.Value.object runtimeType ref)
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
                (match previous with
                | Execution.Response.object _fields => previous
                | _ => Execution.Response.object [])
              =
            visitSubfields schema resolvers variableValues depth runtimeType
                (Execution.Value.object runtimeType ref) selectionSet
                (match previous with
                | Execution.Response.object _fields => previous
                | _ => Execution.Response.object [])
          exact
            visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
              variableValues operation boolCase hagrees depth runtimeType
              (Execution.Value.object runtimeType ref) selectionSet
              (match previous with
              | Execution.Response.object _fields => previous
              | _ => Execution.Response.object [])
              hvars
    | depth + 1, parentType, selectionSet, .list values, previous, hvars => by
        have hfold :
            ∀ (values : List (Execution.Value ObjectRef))
              (previousValues acc : List Execution.Response),
              ((values.foldl
                  (fun (state :
                      List Execution.Response × List Execution.Response)
                      value =>
                    (completeValue schema resolvers variableValues depth
                        parentType
                        (NormalForm.filterSelectionSetBoolCase boolCase
                          selectionSet)
                        value
                        (match state.snd with
                        | [] => Execution.Response.null
                        | previous :: _rest => previous) ::
                        state.fst,
                      match state.snd with
                      | [] => []
                      | _previous :: rest => rest))
                  (acc, previousValues)).fst).reverse
                =
              ((values.foldl
                  (fun (state :
                      List Execution.Response × List Execution.Response)
                      value =>
                    (completeValue schema resolvers variableValues depth
                        parentType selectionSet value
                        (match state.snd with
                        | [] => Execution.Response.null
                        | previous :: _rest => previous) ::
                        state.fst,
                      match state.snd with
                      | [] => []
                      | _previous :: rest => rest))
                  (acc, previousValues)).fst).reverse := by
          intro values
          induction values with
          | nil =>
              intro previousValues acc
              simp
          | cons value rest ih =>
              intro previousValues acc
              have hhead :
                  completeValue schema resolvers variableValues depth
                      parentType
                      (NormalForm.filterSelectionSetBoolCase boolCase
                        selectionSet)
                      value
                      (match previousValues with
                      | [] => Execution.Response.null
                      | previous :: _rest => previous)
                    =
                  completeValue schema resolvers variableValues depth
                    parentType selectionSet value
                    (match previousValues with
                    | [] => Execution.Response.null
                    | previous :: _rest => previous) :=
                completeValue_filterSelectionSetBoolCase_eq schema resolvers
                  variableValues operation boolCase hagrees depth parentType
                  selectionSet value
                  (match previousValues with
                  | [] => Execution.Response.null
                  | previous :: _rest => previous)
                  hvars
              cases previousValues with
              | nil =>
                  simpa [hhead] using
                    ih [] (completeValue schema resolvers variableValues depth
                      parentType selectionSet value Execution.Response.null ::
                      acc)
              | cons previous remainingPrevious =>
                  simpa [hhead] using
                    ih remainingPrevious
                      (completeValue schema resolvers variableValues depth
                        parentType selectionSet value previous :: acc)
        rw [completeValue.eq_def, completeValue.eq_def]
        exact
          congrArg Execution.Response.list
            (hfold values
              (match previous with
              | Execution.Response.list previousValues => previousValues
              | _ => [])
              [])

  def visitSubfields_filterSelectionSetBoolCase_eq
      (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (operation : Operation) (boolCase : NormalForm.BoolCase)
      (hagrees :
        NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues boolCase (NormalForm.operationBoolVars operation)) :
      ∀ depth parentType (source : Execution.Value ObjectRef) selectionSet
          output,
        (∀ varName,
          varName ∈ NormalForm.selectionSetBooleanVariables selectionSet ->
            varName ∈
              NormalForm.selectionSetBooleanVariables operation.selectionSet) ->
          visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
              output
            =
          visitSubfields schema resolvers variableValues depth parentType source
            selectionSet output
    | depth, _parentType, _source, [], output, _hvars => by
        simp [NormalForm.filterSelectionSetBoolCase, visitSubfields]
    | depth, parentType, source, selection :: rest, output, hvars => by
        have hheadVars :
            ∀ varName,
              varName ∈ NormalForm.selectionBooleanVariables selection ->
                varName ∈
                  NormalForm.selectionSetBooleanVariables
                    operation.selectionSet := by
          intro varName hmem
          exact hvars varName
            (by
              simp [NormalForm.selectionSetBooleanVariables, hmem])
        have htailVars :
            ∀ varName,
              varName ∈ NormalForm.selectionSetBooleanVariables rest ->
                varName ∈
                  NormalForm.selectionSetBooleanVariables
                    operation.selectionSet := by
          intro varName hmem
          exact hvars varName
            (by
              simp [NormalForm.selectionSetBooleanVariables, hmem])
        have hhead :
            visitSubfields schema resolvers variableValues depth parentType
                source
                (NormalForm.filterSelectionSetBoolCase boolCase [selection])
                output
              =
            visitSubfields schema resolvers variableValues depth parentType
              source [selection] output := by
          cases selection with
          | field responseName fieldName arguments directives selectionSet =>
              have hdirectiveEq :
                  NormalForm.directivesAllowIn boolCase directives =
                    Execution.selectionDirectivesAllowBool variableValues
                      directives :=
                NormalForm.CompleteNormalization.directivesAllowInCase_eq_execution_of_operationVariables
                  variableValues boolCase operation directives hagrees
                  (by
                    intro varName hmem
                    exact hheadVars varName
                      (by
                        simp [NormalForm.selectionBooleanVariables, hmem]))
              cases hallow :
                  NormalForm.directivesAllowIn boolCase directives
              · have hexec :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives = false := by
                  simpa [hallow] using hdirectiveEq.symm
                simp [NormalForm.filterSelectionSetBoolCase, hallow,
                  visitSubfields]
                rw [visitSelection.eq_def]
                simp [hexec]
              · have hexec :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives = true := by
                  simpa [hallow] using hdirectiveEq.symm
                cases depth with
                | zero =>
                    cases selectionSet with
                    | nil =>
                        simp [NormalForm.filterSelectionSetBoolCase, hallow,
                          visitSubfields, visitSelection, hexec]
                    | cons child children =>
                        cases hfiltered :
                            NormalForm.filterSelectionSetBoolCase boolCase
                              (child :: children) with
                        | nil =>
                            simp [NormalForm.filterSelectionSetBoolCase,
                              hallow, hfiltered, visitSubfields,
                              visitSelection, hexec]
                        | cons filteredChild filteredChildren =>
                            simp [NormalForm.filterSelectionSetBoolCase,
                              hallow, hfiltered, visitSubfields,
                              visitSelection, hexec]
                | succ completionDepth =>
                    have hchildVars :
                        ∀ varName,
                          varName ∈
                              NormalForm.selectionSetBooleanVariables
                                selectionSet ->
                            varName ∈
                              NormalForm.selectionSetBooleanVariables
                                operation.selectionSet := by
                      intro varName hmem
                      exact hheadVars varName
                        (by
                          simp [NormalForm.selectionBooleanVariables, hmem])
                    have hcomplete :
                        completeValue schema resolvers variableValues
                            completionDepth
                            ((schema.fieldReturnType? parentType fieldName).getD
                              fieldName)
                            (NormalForm.filterSelectionSetBoolCase boolCase
                              selectionSet)
                            (resolvers.resolve parentType fieldName arguments
                              source)
                            ((responseObjectField? responseName output).getD
                              Execution.Response.null)
                          =
                        completeValue schema resolvers variableValues
                          completionDepth
                          ((schema.fieldReturnType? parentType fieldName).getD
                            fieldName)
                          selectionSet
                          (resolvers.resolve parentType fieldName arguments
                            source)
                          ((responseObjectField? responseName output).getD
                            Execution.Response.null) :=
                      completeValue_filterSelectionSetBoolCase_eq schema
                        resolvers variableValues operation boolCase hagrees
                        completionDepth
                        ((schema.fieldReturnType? parentType fieldName).getD
                          fieldName)
                        selectionSet
                        (resolvers.resolve parentType fieldName arguments
                          source)
                        ((responseObjectField? responseName output).getD
                          Execution.Response.null)
                        hchildVars
                    cases selectionSet with
                    | nil =>
                        have hempty :
                            Execution.selectionDirectivesAllowBool
                              variableValues [] = true :=
                          NormalForm.selectionDirectivesAllowBool_nil
                            variableValues
                        simp [NormalForm.filterSelectionSetBoolCase, hallow,
                          visitSubfields, visitSelection, hexec, executeField,
                          executableField, hempty]
                    | cons child children =>
                        cases hfiltered :
                            NormalForm.filterSelectionSetBoolCase boolCase
                              (child :: children) with
                        | nil =>
                            rw [hfiltered] at hcomplete
                            have hempty :
                                Execution.selectionDirectivesAllowBool
                                  variableValues [] = true :=
                              NormalForm.selectionDirectivesAllowBool_nil
                                variableValues
                            simpa [NormalForm.filterSelectionSetBoolCase,
                              hallow, hfiltered, visitSubfields,
                              visitSelection, hexec, executeField,
                              executableField, hempty] using
                              congrArg
                                (fun response =>
                                  mergeResponseFieldIntoObject responseName
                                    response output)
                                hcomplete
                        | cons filteredChild filteredChildren =>
                            rw [hfiltered] at hcomplete
                            have hempty :
                                Execution.selectionDirectivesAllowBool
                                  variableValues [] = true :=
                              NormalForm.selectionDirectivesAllowBool_nil
                                variableValues
                            simpa [NormalForm.filterSelectionSetBoolCase,
                              hallow, hfiltered, visitSubfields,
                              visitSelection, hexec, executeField,
                              executableField, hempty] using
                              congrArg
                                (fun response =>
                                  mergeResponseFieldIntoObject responseName
                                    response output)
                                hcomplete
          | inlineFragment typeCondition directives selectionSet =>
              have hdirectiveEq :
                  NormalForm.directivesAllowIn boolCase directives =
                    Execution.selectionDirectivesAllowBool variableValues
                      directives :=
                NormalForm.CompleteNormalization.directivesAllowInCase_eq_execution_of_operationVariables
                  variableValues boolCase operation directives hagrees
                  (by
                    intro varName hmem
                    exact hheadVars varName
                      (by
                        simp [NormalForm.selectionBooleanVariables, hmem]))
              cases hallow :
                  NormalForm.directivesAllowIn boolCase directives
              · have hexec :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives = false := by
                  simpa [hallow] using hdirectiveEq.symm
                cases typeCondition with
                | none =>
                    simp [NormalForm.filterSelectionSetBoolCase, hallow,
                      visitSubfields, visitSelection.eq_def, hexec]
                | some typeCondition =>
                    simp [NormalForm.filterSelectionSetBoolCase, hallow,
                      visitSubfields, visitSelection.eq_def, hexec]
              · have hexec :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives = true := by
                  simpa [hallow] using hdirectiveEq.symm
                have hchildVars :
                    ∀ varName,
                      varName ∈
                          NormalForm.selectionSetBooleanVariables
                            selectionSet ->
                        varName ∈
                          NormalForm.selectionSetBooleanVariables
                            operation.selectionSet := by
                  intro varName hmem
                  exact hheadVars varName
                    (by
                      simp [NormalForm.selectionBooleanVariables, hmem])
                have hchild :
                    visitSubfields schema resolvers variableValues depth
                        parentType source
                        (NormalForm.filterSelectionSetBoolCase boolCase
                          selectionSet)
                        output
                      =
                    visitSubfields schema resolvers variableValues depth
                      parentType source selectionSet output :=
                  visitSubfields_filterSelectionSetBoolCase_eq schema
                    resolvers variableValues operation boolCase hagrees depth
                    parentType source selectionSet output hchildVars
                cases typeCondition with
                | none =>
                    cases hfiltered :
                        NormalForm.filterSelectionSetBoolCase boolCase
                          selectionSet with
                    | nil =>
                        simp [NormalForm.filterSelectionSetBoolCase, hallow,
                          hfiltered, visitSubfields, visitSelection, hexec]
                          at hchild ⊢
                        exact hchild
                    | cons filteredChild filteredChildren =>
                        rw [hfiltered] at hchild
                        have hempty :
                            Execution.selectionDirectivesAllowBool
                              variableValues [] = true :=
                          NormalForm.selectionDirectivesAllowBool_nil
                            variableValues
                        simp [NormalForm.filterSelectionSetBoolCase, hallow,
                          hfiltered, visitSubfields, visitSelection, hexec,
                          hempty] at hchild ⊢
                        exact hchild
                | some typeCondition =>
                    cases happly :
                        Execution.doesFragmentTypeApplyBool schema parentType
                          source typeCondition
                    · cases hfiltered :
                          NormalForm.filterSelectionSetBoolCase boolCase
                            selectionSet with
                      | nil =>
                          simp [NormalForm.filterSelectionSetBoolCase, hallow,
                            hfiltered, visitSubfields, visitSelection, hexec,
                            happly]
                      | cons filteredChild filteredChildren =>
                          simp [NormalForm.filterSelectionSetBoolCase, hallow,
                            hfiltered, visitSubfields, visitSelection, hexec,
                            happly]
                    · cases hfiltered :
                          NormalForm.filterSelectionSetBoolCase boolCase
                            selectionSet with
                      | nil =>
                          simp [NormalForm.filterSelectionSetBoolCase, hallow,
                            hfiltered, visitSubfields, visitSelection, hexec,
                            happly] at hchild ⊢
                          exact hchild
                      | cons filteredChild filteredChildren =>
                          rw [hfiltered] at hchild
                          have hempty :
                              Execution.selectionDirectivesAllowBool
                                variableValues [] = true :=
                            NormalForm.selectionDirectivesAllowBool_nil
                              variableValues
                          simp [NormalForm.filterSelectionSetBoolCase, hallow,
                            hfiltered, visitSubfields, visitSelection, hexec,
                            happly, hempty] at hchild ⊢
                          exact hchild
        rw [NormalForm.CompleteNormalization.filterSelectionSetBoolCase_cons]
        rw [visitSubfields_append]
        rw [hhead]
        simpa [visitSubfields] using
          visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
            variableValues operation boolCase hagrees depth parentType source
            rest
            (visitSubfields schema resolvers variableValues depth parentType
              source [selection] output)
            htailVars
end

theorem visitSubfields_completeNormalizeRootSelectionSet_eq_of_filter_normalization
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSet : List Selection)
    (output : Execution.Response) :
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
    (∀ varName,
      varName ∈ NormalForm.selectionSetBooleanVariables selectionSet ->
        varName ∈
          NormalForm.selectionSetBooleanVariables operation.selectionSet) ->
    visitSubfields schema resolvers variableValues depth parentType source
        (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet)
        output
      =
    visitSubfields schema resolvers variableValues depth parentType source
        (NormalForm.normalizeSelectionSet schema parentType
          (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet))
        output ->
      visitSubfields schema resolvers variableValues depth parentType source
          selectionSet output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (NormalForm.completeNormalizeRootSelectionSet schema
          (NormalForm.operationBoolVars operation) parentType selectionSet)
        output := by
  intro hruntime hagrees hvars hnormalized
  have hfilter :
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet)
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
          selectionSet output :=
    visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
      variableValues operation runtimeCase hagrees depth parentType source
      selectionSet output hvars
  have hcomplete :
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.completeNormalizeRootSelectionSet schema
            (NormalForm.operationBoolVars operation) parentType selectionSet)
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (NormalForm.normalizeSelectionSet schema parentType
          (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet))
        output :=
    visitSubfields_completeNormalizeRootSelectionSet_runtime schema
      resolvers variableValues operation depth parentType source runtimeCase
      selectionSet output hruntime hagrees
  exact hfilter.symm.trans (hnormalized.trans hcomplete.symm)

theorem executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_normalization
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
    NormalForm.operationBoolVarsComplete operation variableValues ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
        visitSubfields schema resolvers variableValues depth operation.rootType
            source
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)
            (Execution.Response.object [])
          =
        visitSubfields schema resolvers variableValues depth operation.rootType
            source
            (NormalForm.normalizeSelectionSet schema operation.rootType
              (NormalForm.filterSelectionSetBoolCase runtimeCase
                operation.selectionSet))
            (Execution.Response.object [])) ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source := by
  intro hcomplete hnormalizeBranch
  rw [executeQueryAtDepth]
  rw [executeQueryAtDepth]
  rw [NormalForm.CompleteNormalization.completeNormalizeOperation_rootSourceAppliesBool]
  cases hroot : Execution.rootSourceAppliesBool schema operation source
  · simp
  · rcases
      NormalForm.CompleteNormalization.operationBoolVarsComplete_caseForVariableValues
        variableValues operation hcomplete with
      ⟨runtimeCase, hruntime, hagrees⟩
    have hvisit :
        visitSubfields schema resolvers variableValues depth operation.rootType
            source operation.selectionSet (Execution.Response.object [])
          =
        visitSubfields schema resolvers variableValues depth operation.rootType
          source
          (NormalForm.completeNormalizeRootSelectionSet schema
            (NormalForm.operationBoolVars operation) operation.rootType
            operation.selectionSet)
          (Execution.Response.object []) :=
      visitSubfields_completeNormalizeRootSelectionSet_eq_of_filter_normalization
        schema resolvers variableValues operation depth operation.rootType
        source runtimeCase operation.selectionSet (Execution.Response.object [])
        hruntime hagrees
        (by
          intro varName hmem
          exact hmem)
        (hnormalizeBranch runtimeCase hruntime hagrees)
    simp [executeRootSelectionSet, NormalForm.completeNormalizeOperation,
      hvisit]

theorem executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_freshPlanNormalizes
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
    NormalForm.operationBoolVarsComplete operation variableValues ->
    (∀ runtimeCase,
      runtimeCase ∈
        NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
      NormalForm.CompleteNormalization.variableValuesAgreeWithCase
        variableValues runtimeCase
        (NormalForm.operationBoolVars operation) ->
        SelectionSetFreshPlanNormalizes schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet)
          (NormalForm.normalizeSelectionSet schema operation.rootType
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet))) ->
      executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source := by
  intro hcomplete hnormalizes
  apply executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_normalization
    schema operation resolvers variableValues (depth + 1) source hcomplete
  intro runtimeCase hruntime hagrees
  exact
    (hnormalizes runtimeCase hruntime hagrees).visitSubfields_eq

theorem responseNamesNodup_tail
    {selection : Selection} {selectionSet : List Selection} :
    NormalForm.responseNamesNodup (selection :: selectionSet) ->
      NormalForm.responseNamesNodup selectionSet := by
  intro hnodup
  unfold NormalForm.responseNamesNodup at hnodup ⊢
  cases selection with
  | field responseName fieldName arguments directives subselections =>
      simpa [Selection.responseName?] using hnodup.tail
  | inlineFragment typeCondition directives subselections =>
      simpa [Selection.responseName?] using hnodup

theorem inlineFragmentTypeConditionsNodup_tail
    {selection : Selection} {selectionSet : List Selection} :
    NormalForm.inlineFragmentTypeConditionsNodup (selection :: selectionSet) ->
      NormalForm.inlineFragmentTypeConditionsNodup selectionSet := by
  intro hnodup
  unfold NormalForm.inlineFragmentTypeConditionsNodup at hnodup ⊢
  cases selection with
  | field responseName fieldName arguments directives subselections =>
      simpa using hnodup
  | inlineFragment typeCondition directives subselections =>
      cases typeCondition with
      | none =>
          simpa using hnodup
      | some typeCondition =>
          simpa using hnodup.tail

theorem selectionSetNonRedundant_tail
    {selection : Selection} {selectionSet : List Selection} :
    NormalForm.selectionSetNonRedundant (selection :: selectionSet) ->
      NormalForm.selectionSetNonRedundant selectionSet := by
  intro hnonRedundant
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant ⊢
  exact ⟨responseNamesNodup_tail hnonRedundant.1,
    inlineFragmentTypeConditionsNodup_tail hnonRedundant.2.1,
    fun selection hselection =>
      hnonRedundant.2.2 selection
        (List.mem_cons_of_mem _ hselection)⟩

theorem selectionSetGroundTyped_tail
    {schema : Schema} {selection : Selection}
    {selectionSet : List Selection} :
    NormalForm.selectionSetGroundTyped schema (selection :: selectionSet) ->
      NormalForm.selectionSetGroundTyped schema selectionSet := by
  intro hground
  unfold NormalForm.selectionSetGroundTyped at hground ⊢
  constructor
  · cases hground.1 with
    | inl hfields =>
        exact Or.inl (fun candidate hcandidate =>
          hfields candidate (List.mem_cons_of_mem _ hcandidate))
    | inr hfragments =>
        exact Or.inr (fun candidate hcandidate =>
          hfragments candidate (List.mem_cons_of_mem _ hcandidate))
  · intro candidate hcandidate
    exact hground.2 candidate (List.mem_cons_of_mem _ hcandidate)

theorem selectionSetNormal_tail
    {schema : Schema} {selection : Selection}
    {selectionSet : List Selection} :
    NormalForm.selectionSetNormal schema (selection :: selectionSet) ->
      NormalForm.selectionSetNormal schema selectionSet := by
  intro hnormal
  exact ⟨selectionSetGroundTyped_tail hnormal.1,
    selectionSetNonRedundant_tail hnormal.2⟩

theorem selectionSetNormal_field_child
    {schema : Schema}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet rest : List Selection} :
    NormalForm.selectionSetNormal schema
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) ->
      NormalForm.selectionSetNormal schema selectionSet := by
  intro hnormal
  unfold NormalForm.selectionSetNormal at hnormal
  rcases hnormal with ⟨hground, hnonRedundant⟩
  unfold NormalForm.selectionSetGroundTyped at hground
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant
  have hselectionGround :
      NormalForm.selectionGroundTyped schema
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    exact hground.2 _ (by simp)
  have hselectionNonRedundant :
      NormalForm.selectionNonRedundant
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    exact hnonRedundant.2.2 _ (by simp)
  unfold NormalForm.selectionGroundTyped at hselectionGround
  unfold NormalForm.selectionNonRedundant at hselectionNonRedundant
  exact ⟨hselectionGround.2, hselectionNonRedundant⟩

theorem selectionSetNormal_inline_child
    {schema : Schema}
    {typeCondition : Option Name} {directives : List DirectiveApplication}
    {selectionSet rest : List Selection} :
    NormalForm.selectionSetNormal schema
        (Selection.inlineFragment typeCondition directives selectionSet ::
          rest) ->
      NormalForm.selectionSetNormal schema selectionSet := by
  intro hnormal
  unfold NormalForm.selectionSetNormal at hnormal
  rcases hnormal with ⟨hground, hnonRedundant⟩
  unfold NormalForm.selectionSetGroundTyped at hground
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant
  have hselectionGround :
      NormalForm.selectionGroundTyped schema
        (Selection.inlineFragment typeCondition directives selectionSet) := by
    exact hground.2 _ (by simp)
  have hselectionNonRedundant :
      NormalForm.selectionNonRedundant
        (Selection.inlineFragment typeCondition directives selectionSet) := by
    exact hnonRedundant.2.2 _ (by simp)
  cases typeCondition with
  | none =>
      unfold NormalForm.selectionGroundTyped at hselectionGround
      unfold NormalForm.selectionNonRedundant at hselectionNonRedundant
      exact ⟨hselectionGround.2, hselectionNonRedundant⟩
  | some typeCondition =>
      unfold NormalForm.selectionGroundTyped at hselectionGround
      unfold NormalForm.selectionNonRedundant at hselectionNonRedundant
      exact ⟨hselectionGround.2.2, hselectionNonRedundant⟩

theorem selectionSetResponseNameFree_of_allFields_responseNamesNodup
    (schema : Schema) (parentType responseName : Name) :
    ∀ selectionSet,
      NormalForm.selectionsAllFields selectionSet ->
      responseName ∉ selectionSet.filterMap Selection.responseName? ->
        NormalForm.selectionSetResponseNameFree schema parentType
          responseName selectionSet
  | [], _hall, _hnotMem => by
      exact NormalForm.selectionSetResponseNameFree_nil schema parentType
        responseName
  | selection :: rest, hall, hnotMem => by
      have hheadField : Selection.isField selection := hall selection (by simp)
      have hrestAll :
          NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have hrestNotMem :
          responseName ∉ rest.filterMap Selection.responseName? := by
        intro hmem
        exact hnotMem (by
          cases selection <;> simp [Selection.responseName?, hmem])
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hfieldNe : fieldResponseName ≠ responseName := by
            intro heq
            exact hnotMem (by simp [Selection.responseName?, heq])
          apply NormalForm.selectionSetResponseNameFree_cons
          · simpa [NormalForm.selectionResponseNameFree] using hfieldNe
          · exact selectionSetResponseNameFree_of_allFields_responseNamesNodup
              schema parentType responseName rest hrestAll hrestNotMem
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

def outputNamesFreeForSelectionSet
    (schema : Schema) (parentType : Name)
    (outputFields : List (Name × Execution.Response))
    (selectionSet : List Selection) : Prop :=
  ∀ responseName, responseName ∈ outputFields.map Prod.fst ->
    NormalForm.selectionSetResponseNameFree schema parentType responseName
      selectionSet

theorem outputNamesFreeForSelectionSet_nil
    (schema : Schema) (parentType : Name)
    (selectionSet : List Selection) :
    outputNamesFreeForSelectionSet schema parentType [] selectionSet := by
  intro responseName hmem
  simp at hmem

theorem outputNamesFreeForSelectionSet_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection}
    {outputFields : List (Name × Execution.Response)} :
    outputNamesFreeForSelectionSet schema parentType outputFields
      (selection :: selectionSet) ->
      outputNamesFreeForSelectionSet schema parentType outputFields
        selectionSet := by
  intro hfree responseName hmem
  exact NormalForm.selectionSetResponseNameFree_tail
    (hfree responseName hmem)

theorem outputNamesFreeForSelectionSet_cons_output
    {schema : Schema} {parentType responseName : Name}
    {response : Execution.Response}
    {outputFields : List (Name × Execution.Response)}
    {selectionSet : List Selection} :
    outputNamesFreeForSelectionSet schema parentType outputFields
      selectionSet ->
    NormalForm.selectionSetResponseNameFree schema parentType responseName
      selectionSet ->
      outputNamesFreeForSelectionSet schema parentType
        (outputFields ++ [(responseName, response)]) selectionSet := by
  intro houtput hresponse candidate hmem
  have hcases :
      candidate ∈ outputFields.map Prod.fst ∨ candidate = responseName := by
    simpa using hmem
  cases hcases with
  | inl hprefix =>
      exact houtput candidate hprefix
  | inr hcandidate =>
      subst candidate
      exact hresponse

theorem responseName_not_mem_output_of_field_head_outputNamesFree
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet rest : List Selection}
    {outputFields : List (Name × Execution.Response)} :
    outputNamesFreeForSelectionSet schema parentType outputFields
      (Selection.field responseName fieldName arguments directives
        selectionSet :: rest) ->
      responseName ∉ outputFields.map Prod.fst := by
  intro houtput hmem
  have hfree := houtput responseName hmem
  have hhead :=
    NormalForm.selectionSetResponseNameFree_head hfree
  simp [NormalForm.selectionResponseNameFree] at hhead

theorem collectFields_responseName_not_mem_of_allFields_responseNameFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.Value ObjectRef)
    (responseName : Name) :
    ∀ selectionSet,
      NormalForm.selectionsAllFields selectionSet ->
      NormalForm.selectionSetDirectiveFree selectionSet ->
      NormalForm.selectionSetResponseNameFree schema parentType responseName
        selectionSet ->
        responseName ∉
          (Execution.collectFields schema variableValues parentType source
            selectionSet).map Prod.fst
  | [], _hall, _hfree, _hresponseFree => by
      simp [Execution.collectFields]
  | Selection.field fieldResponseName fieldName arguments directives
      selectionSet :: rest,
      hall, hfree, hresponseFree => by
      have hheadFree := NormalForm.selectionSetDirectiveFree_head hfree
      have htailFree := NormalForm.selectionSetDirectiveFree_tail hfree
      have htailAll :
          NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate
          (List.mem_cons_of_mem
            (Selection.field fieldResponseName fieldName arguments
              directives selectionSet) hcandidate)
      have htailResponseFree :
          NormalForm.selectionSetResponseNameFree schema parentType
            responseName rest :=
        NormalForm.selectionSetResponseNameFree_tail hresponseFree
      have hfieldNe : fieldResponseName ≠ responseName := by
        have hheadResponseFree :=
          NormalForm.selectionSetResponseNameFree_head hresponseFree
        simpa [NormalForm.selectionResponseNameFree] using hheadResponseFree
      have hdirectives : directives = [] := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.1
      subst directives
      rw [NormalForm.GroundTypeNormalization.collectFields_field_noDirectives]
      intro hmem
      have hcases :=
        (NormalForm.GroundTypeNormalization.mergeExecutableGroups_mem_responseName
          [(fieldResponseName, [{
            parentType := parentType,
            responseName := fieldResponseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }])]
          (Execution.collectFields schema variableValues parentType source
            rest)
          responseName).mp hmem
      cases hcases with
      | inl hhead =>
          simp at hhead
          exact hfieldNe hhead.symm
      | inr htail =>
          exact
            collectFields_responseName_not_mem_of_allFields_responseNameFree
              schema variableValues parentType source responseName
              rest htailAll htailFree htailResponseFree htail
  | Selection.inlineFragment typeCondition directives selectionSet :: rest,
      hall, _hfree, _hresponseFree => by
      have hheadField :
          Selection.isField
            (Selection.inlineFragment typeCondition directives selectionSet) :=
        hall _ (by simp)
      simp [Selection.isField] at hheadField

mutual
  theorem visitSubfields_depth_zero
      (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.Value ObjectRef) :
      ∀ selectionSet output,
        visitSubfields schema resolvers variableValues 0 parentType source
          selectionSet output = output
    | [], output => by
        simp [visitSubfields]
    | selection :: rest, output => by
        simp [visitSubfields,
          visitSelection_depth_zero schema resolvers variableValues parentType
            source selection output,
          visitSubfields_depth_zero schema resolvers variableValues parentType
            source rest output]

  theorem visitSelection_depth_zero
      (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.Value ObjectRef) :
      ∀ selection output,
        visitSelection schema resolvers variableValues 0 parentType source
          selection output = output
    | .field _responseName _fieldName _arguments _directives _selectionSet,
        output => by
        by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues _directives =
              true
        · simp [visitSelection, hallow]
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues
                  _directives =
                false := by
            cases hmatch :
                Execution.selectionDirectivesAllowBool variableValues
                  _directives
            · rfl
            · contradiction
          simp [visitSelection, hfalse]
    | .inlineFragment none directives selectionSet, output => by
        by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives =
              true
        · simp [visitSelection, hallow,
            visitSubfields_depth_zero schema resolvers variableValues
              parentType source selectionSet output]
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues
                  directives =
                false := by
            cases hmatch :
                Execution.selectionDirectivesAllowBool variableValues
                  directives
            · rfl
            · contradiction
          simp [visitSelection, hfalse]
    | .inlineFragment (some typeCondition) directives selectionSet,
        output => by
        by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives =
              true
        · by_cases happly :
              Execution.doesFragmentTypeApplyBool schema parentType source
                typeCondition = true
          · simp [visitSelection, hallow, happly,
              visitSubfields_depth_zero schema resolvers variableValues
                parentType source selectionSet output]
          · have happlyFalse :
                Execution.doesFragmentTypeApplyBool schema parentType source
                    typeCondition =
                  false := by
              cases hmatch :
                  Execution.doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · rfl
              · contradiction
            simp [visitSelection, hallow, happlyFalse]
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues
                  directives =
                false := by
            cases hmatch :
                Execution.selectionDirectivesAllowBool variableValues
                  directives
            · rfl
            · contradiction
          simp [visitSelection, hfalse]
end

theorem executeCollectedFields_depth_zero
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (source : Execution.Value ObjectRef) :
    ∀ groups,
      Execution.executeCollectedFields schema resolvers variableValues 0
        source groups = []
  | [] => by
      simp [Execution.executeCollectedFields]
  | (responseName, fields) :: rest => by
      cases fields with
      | nil =>
          simp [Execution.executeCollectedFields, Execution.executeField,
            executeCollectedFields_depth_zero schema resolvers variableValues
              source rest]
      | cons field fields =>
          simp [Execution.executeCollectedFields, Execution.executeField,
            executeCollectedFields_depth_zero schema resolvers variableValues
              source rest]

theorem executeSelectionSet_depth_zero
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) :
    Execution.executeSelectionSet schema resolvers variableValues 0
      parentType source selectionSet = [] := by
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    executeCollectedFields_depth_zero schema resolvers variableValues source]

theorem visitSubfields_possibleTypeNormalizations_not_mem_eq_self
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (runtimeType : Name) (ref : Option ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      NormalForm.objectTypeNameBool schema objectType = true) ->
    runtimeType ∉ possibleTypes ->
      ∀ output,
        visitSubfields schema resolvers variableValues
            depth runtimeType (Execution.Value.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema possibleTypes selectionSet)
            output
          =
          output := by
  intro hobjects hnotin output
  induction possibleTypes generalizing output with
  | nil =>
      simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
        visitSubfields]
  | cons objectType rest ih =>
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
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
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
            hnormalized]
          exact ih hrestObjects hrestNotin output
      | cons selection restSelection =>
          have hskip :
              Execution.doesFragmentTypeApplyBool schema runtimeType
                (Execution.Value.object runtimeType ref) objectType =
                false :=
            NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false schema
                (ref := ref) hobject hne
          simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
            hnormalized, visitSubfields, visitSelection, hskip]
          exact ih hrestObjects hrestNotin output

theorem visitSubfields_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (runtimeType : Name) (ref : Option ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      NormalForm.objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
    ∀ output,
      visitSubfields schema resolvers variableValues
          depth runtimeType (Execution.Value.object runtimeType ref)
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
            schema possibleTypes selectionSet)
          output
        =
      visitSubfields schema resolvers variableValues
        depth runtimeType (Execution.Value.object runtimeType ref)
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
        output := by
  intro hobjects hnodup hmem output
  induction possibleTypes generalizing output with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hrestSkip :
                visitSubfields schema resolvers variableValues
                    depth runtimeType
                    (Execution.Value.object runtimeType ref)
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet)
                    output
                  =
                output :=
              visitSubfields_possibleTypeNormalizations_not_mem_eq_self
                schema resolvers variableValues depth runtimeType ref rest
                selectionSet hrestObjects hrestNotin output
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized, visitSubfields] using hrestSkip
          · have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hhead =>
                  exact False.elim (heq hhead.symm)
              | inr htail =>
                  exact htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using
              ih hrestObjects hrestNodup hrestMem output
      | cons selection restNormalized =>
          rw [show
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema (objectType :: rest) selectionSet =
                Selection.inlineFragment (some objectType) []
                    (selection :: restNormalized)
                  ::
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet by
            simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized]]
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (Execution.Value.object runtimeType ref) runtimeType =
                  true :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
                schema (ref := ref) hobject
            have hrestSkip :
                ∀ branchOutput,
                  visitSubfields schema resolvers variableValues
                      depth runtimeType
                      (Execution.Value.object runtimeType ref)
                      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                        schema rest selectionSet)
                      branchOutput
                    =
                  branchOutput :=
              visitSubfields_possibleTypeNormalizations_not_mem_eq_self
                schema resolvers variableValues depth runtimeType ref rest
                selectionSet hrestObjects hrestNotin
            simp [visitSubfields, visitSelection, happly,
              Execution.selectionDirectivesAllowBool]
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized, visitSubfields]
              using
                hrestSkip
                  (visitSubfields schema resolvers variableValues depth
                    runtimeType (Execution.Value.object runtimeType ref)
                    restNormalized
                    (visitSelection schema resolvers variableValues depth
                      runtimeType (Execution.Value.object runtimeType ref)
                      selection output))
          · have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hhead =>
                  exact False.elim (heq hhead.symm)
              | inr htail =>
                  exact htail
            have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (Execution.Value.object runtimeType ref) objectType =
                  false :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                schema (ref := ref) hobject heq
            simp [visitSubfields, visitSelection, hskip]
            exact ih hrestObjects hrestNodup hrestMem output

theorem executeSelectionSet_possibleTypeNormalizations_runtime_normalized_branch
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : Option ObjectRef := none)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      NormalForm.objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (Execution.Value.object runtimeType ref)
        (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
          possibleTypes selectionSet)
      =
      Execution.executeSelectionSet schema resolvers variableValues depth
        runtimeType (Execution.Value.object runtimeType ref)
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hobjects hnodup hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hrestEq :
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (Execution.Value.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (Execution.Value.object runtimeType ref)
                  [] := by
              simpa using
                NormalForm.GroundTypeNormalization.executeSelectionSet_append_possibleTypeNormalizations_not_mem
                  schema resolvers variableValues depth runtimeType
                  (ref := ref) rest selectionSet [] hrestObjects hrestNotin
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using hrestEq
          · have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hhead =>
                  exact False.elim (heq hhead.symm)
              | inr htail =>
                  exact htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using ih hrestObjects hrestNodup hrestMem
      | cons selection restNormalized =>
          rw [show
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema (objectType :: rest) selectionSet =
                Selection.inlineFragment (some objectType) []
                    (selection :: restNormalized)
                  ::
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet by
            simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized]]
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (Execution.Value.object runtimeType ref) runtimeType =
                  true :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
                schema (ref := ref) hobject
            rw [
              NormalForm.GroundTypeNormalization.executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                schema resolvers variableValues depth runtimeType runtimeType
                (Execution.Value.object runtimeType ref)
                (selection :: restNormalized)
                (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet)
                (by simpa using happly)]
            rw [
              NormalForm.GroundTypeNormalization.executeSelectionSet_append_possibleTypeNormalizations_not_mem
                schema resolvers variableValues depth runtimeType (ref := ref)
                rest selectionSet (selection :: restNormalized) hrestObjects
                hrestNotin]
            simp [hnormalized]
          · have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (Execution.Value.object runtimeType ref) objectType =
                  false :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                schema (ref := ref) hobject heq
            rw [
              NormalForm.GroundTypeNormalization.executeSelectionSet_inlineFragment_some_directiveFree_skip
                schema resolvers variableValues depth runtimeType objectType
                (Execution.Value.object runtimeType ref)
                (selection :: restNormalized)
                (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet)
                (by simpa using hskip)]
            have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hhead =>
                  exact False.elim (heq hhead.symm)
              | inr htail =>
                  exact htail
            exact ih hrestObjects hrestNodup hrestMem

theorem visitSubfields_possibleTypeNormalizations_eq_spec_of_runtime_normalized
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : Option ObjectRef := none)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      NormalForm.objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
    visitSubfields schema resolvers variableValues depth runtimeType
        (Execution.Value.object runtimeType ref)
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
        (Execution.Response.object [])
      =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (Execution.Value.object runtimeType ref)
          (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)) ->
      visitSubfields schema resolvers variableValues depth runtimeType
          (Execution.Value.object runtimeType ref)
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            possibleTypes selectionSet)
          (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (Execution.Value.object runtimeType ref)
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            possibleTypes selectionSet)) := by
  intro hobjects hnodup hmem hnormalized
  rw [visitSubfields_possibleTypeNormalizations_runtime_branch schema
    resolvers variableValues depth runtimeType ref possibleTypes selectionSet
    hobjects hnodup hmem (Execution.Response.object [])]
  rw [hnormalized]
  rw [executeSelectionSet_possibleTypeNormalizations_runtime_normalized_branch
    schema resolvers variableValues depth runtimeType (ref := ref)
    possibleTypes selectionSet hobjects hnodup hmem]

theorem visitSubfields_getPossibleTypesNormalizations_eq_spec_of_runtime_normalized
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (childType runtimeType : Name)
    (ref : Option ObjectRef := none)
    (selectionSet : List Selection) :
    schema.typeIncludesObjectBool childType runtimeType = true ->
    visitSubfields schema resolvers variableValues depth runtimeType
        (Execution.Value.object runtimeType ref)
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
        (Execution.Response.object [])
      =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (Execution.Value.object runtimeType ref)
          (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)) ->
      visitSubfields schema resolvers variableValues depth runtimeType
          (Execution.Value.object runtimeType ref)
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) selectionSet)
          (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (Execution.Value.object runtimeType ref)
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) selectionSet)) := by
  intro hinclude hnormalized
  have hmem : runtimeType ∈ schema.getPossibleTypes childType :=
    List.contains_iff_mem.mp hinclude
  have hobjects :
      ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
        NormalForm.objectTypeNameBool schema objectType = true := by
    intro objectType hobjectType
    exact NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
      schema
      (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
        hschema childType objectType hobjectType)
  exact
    visitSubfields_possibleTypeNormalizations_eq_spec_of_runtime_normalized
      schema resolvers variableValues depth runtimeType (ref := ref)
      (schema.getPossibleTypes childType) selectionSet hobjects
      (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType)
      hmem hnormalized

theorem visitSubfields_normalizedFieldSubselections_eq_spec_of_runtime
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (childType runtimeType : Name)
    (ref : Option ObjectRef := none)
    (selectionSet : List Selection) :
    schema.typeIncludesObjectBool childType runtimeType = true ->
    visitSubfields schema resolvers variableValues depth runtimeType
        (Execution.Value.object runtimeType ref)
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
        (Execution.Response.object [])
      =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (Execution.Value.object runtimeType ref)
          (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)) ->
      visitSubfields schema resolvers variableValues depth runtimeType
          (Execution.Value.object runtimeType ref)
          (if NormalForm.objectTypeNameBool schema childType then
            NormalForm.normalizeSelectionSet schema childType selectionSet
          else
            NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
              (schema.getPossibleTypes childType) selectionSet)
          (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          runtimeType (Execution.Value.object runtimeType ref)
          (if NormalForm.objectTypeNameBool schema childType then
            NormalForm.normalizeSelectionSet schema childType selectionSet
          else
            NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
              (schema.getPossibleTypes childType) selectionSet)) := by
  intro hinclude hnormalized
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hruntimeEq : runtimeType = childType :=
      NormalForm.GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
        schema hobject hinclude
    subst runtimeType
    simpa [hobject] using hnormalized
  · have hobjectFalse :
        NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    simp [hobjectFalse]
    exact
      visitSubfields_getPossibleTypesNormalizations_eq_spec_of_runtime_normalized
        schema resolvers variableValues hschema depth childType runtimeType
        (ref := ref) selectionSet hinclude hnormalized

def generatedNormalizedFieldChild
    (schema : Schema) (childType : Name)
    (childSelectionSet : List Selection) : Prop :=
  ∃ sourceSelectionSet,
    NormalForm.selectionSetDirectiveFree sourceSelectionSet ∧
    childSelectionSet =
      if NormalForm.objectTypeNameBool schema childType then
        NormalForm.normalizeSelectionSet schema childType sourceSelectionSet
      else
        NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
          (schema.getPossibleTypes childType) sourceSelectionSet

theorem generatedNormalizedFieldChild_selectionSetDirectiveFree
    (schema : Schema) (childType : Name)
    (childSelectionSet : List Selection) :
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      NormalForm.selectionSetDirectiveFree childSelectionSet := by
  intro hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType
            sourceSelectionSet := by
      simpa [hobject] using hchild
    simpa [hchildEq] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
        schema childType sourceSelectionSet hsourceFree
  · have hfalse :
        NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    simpa [hchildEq] using
      NormalForm.GroundTypeNormalization.selectionSetDirectiveFree_possibleTypeNormalizations
        schema (schema.getPossibleTypes childType)
        (selectionSet := sourceSelectionSet)
        (fun objectType _hobjectType =>
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
            schema objectType sourceSelectionSet hsourceFree)

theorem generatedNormalizedFieldChild_selectionSetNormal
    (schema : Schema) (childType : Name)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      NormalForm.selectionSetNormal schema childSelectionSet := by
  intro hschema hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, _hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType
            sourceSelectionSet := by
      simpa [hobject] using hchild
    simpa [hchildEq] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal
        schema hschema childType sourceSelectionSet
  · have hfalse :
        NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    have hground :
        NormalForm.selectionSetGroundTyped schema
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.possibleTypeNormalizations_groundTyped
        schema (schema.getPossibleTypes childType) sourceSelectionSet
        (fun objectType hobjectType =>
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema childType objectType hobjectType)
        (fun objectType _hobjectType =>
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_groundTyped
            schema hschema objectType sourceSelectionSet)
    have hnonRedundant :
        NormalForm.selectionSetNonRedundant
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.possibleTypeNormalizations_nonRedundant
        schema (schema.getPossibleTypes childType) sourceSelectionSet
        (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
          childType)
        (fun objectType _hobjectType =>
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal
            schema hschema objectType sourceSelectionSet).2)
    simpa [hchildEq] using
      (⟨hground, hnonRedundant⟩ :
        NormalForm.selectionSetNormal schema
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet))

theorem collectFields_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : Option ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      NormalForm.objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    runtimeType ∈ possibleTypes ->
      GraphQL.Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ref)
        (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
          possibleTypes selectionSet)
        =
      GraphQL.Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ref)
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hobjects hnodup hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) = [] :=
              NormalForm.GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
                schema variableValues runtimeType (ref := ref) rest
                selectionSet hrestObjects hrestNotin
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized, GraphQL.Execution.collectFields] using hrestCollect
          · have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using ih hrestObjects hrestNodup hrestMem
      | cons selection restNormalized =>
          rw [show
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema (objectType :: rest) selectionSet =
                Selection.inlineFragment (some objectType) []
                  (selection :: restNormalized)
                  :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet by
            simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized]]
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) = [] :=
              NormalForm.GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
                schema variableValues runtimeType (ref := ref) rest
                selectionSet hrestObjects hrestNotin
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                    (.object runtimeType ref) runtimeType =
                  true :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
                schema (ref := ref) hobject
            rw [NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_apply_flatten
              schema variableValues runtimeType runtimeType
              (.object runtimeType ref) (selection :: restNormalized)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema rest selectionSet) happly]
            rw [GraphQL.NormalForm.collectFields_append]
            rw [hrestCollect]
            simp [hnormalized, GraphQL.Execution.mergeExecutableGroups_nil_right]
          · have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                    (.object runtimeType ref) objectType =
                  false :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                schema (ref := ref) hobject heq
            rw [NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
              schema variableValues runtimeType objectType
              (.object runtimeType ref) (selection :: restNormalized)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema rest selectionSet) hskip]
            have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            exact ih hrestObjects hrestNodup hrestMem

theorem selectionSetLookupValid_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    runtimeType ∈ possibleTypes ->
    NormalForm.selectionSetLookupValid schema runtimeType
      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
        possibleTypes selectionSet) ->
      NormalForm.selectionSetLookupValid schema runtimeType
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      intro hlookup
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            simpa [hnormalized] using
              NormalForm.selectionSetLookupValid_nil schema runtimeType
          · have htailLookup :
                NormalForm.selectionSetLookupValid schema runtimeType
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) := by
              simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized] using hlookup
            exact ih htail htailLookup
      | cons selection normalizedRest =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            have hlookupFn :
                ∀ candidate,
                  candidate ∈
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema (runtimeType :: rest) selectionSet ->
                    NormalForm.selectionLookupValid schema runtimeType
                      candidate := by
              simpa [NormalForm.selectionSetLookupValid] using hlookup
            have hheadLookup :
                NormalForm.selectionSetLookupValid schema runtimeType
                  (selection :: normalizedRest) := by
              have hfirst :
                  NormalForm.selectionLookupValid schema runtimeType
                    (Selection.inlineFragment (some runtimeType) []
                      (selection :: normalizedRest)) := by
                exact hlookupFn
                  (Selection.inlineFragment (some runtimeType) []
                    (selection :: normalizedRest))
                  (by
                    simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                      hnormalized])
              simpa [NormalForm.selectionLookupValid] using hfirst
            simpa [hnormalized] using hheadLookup
          · have hlookupFn :
                ∀ candidate,
                  candidate ∈
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema (objectType :: rest) selectionSet ->
                    NormalForm.selectionLookupValid schema runtimeType
                      candidate := by
              simpa [NormalForm.selectionSetLookupValid] using hlookup
            have htailLookup :
              NormalForm.selectionSetLookupValid schema runtimeType
                (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet) := by
              simp [NormalForm.selectionSetLookupValid]
              intro candidate hcandidate
              have hcandidateFull :
                  candidate ∈
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema (objectType :: rest) selectionSet := by
                rw [show
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                        schema (objectType :: rest) selectionSet =
                      Selection.inlineFragment (some objectType) []
                        (selection :: normalizedRest)
                        :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                          schema rest selectionSet by
                  simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                    hnormalized]]
                exact List.mem_cons_of_mem
                  (Selection.inlineFragment (some objectType) []
                    (selection :: normalizedRest)) hcandidate
              exact hlookupFn candidate
                hcandidateFull
            exact ih htail htailLookup

theorem fieldMerge_collectFields_possibleTypeNormalizations_runtime_branch_mem
    (schema : Schema) (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection)
    (scopedField : FieldMerge.ScopedField) :
    runtimeType ∈ possibleTypes ->
    scopedField ∈ FieldMerge.collectFields schema runtimeType
      (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) ->
      scopedField ∈ FieldMerge.collectFields schema runtimeType
        (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
          possibleTypes selectionSet) := by
  intro hmem hscoped
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            simp [hnormalized, FieldMerge.collectFields] at hscoped
          · have htailMem :
                scopedField ∈
                  FieldMerge.collectFields schema runtimeType
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) :=
              ih htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using htailMem
      | cons selection normalizedRest =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            rw [show
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema (runtimeType :: rest) selectionSet =
                  Selection.inlineFragment (some runtimeType) []
                    (selection :: normalizedRest)
                    :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet by
              simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized]]
            simp [FieldMerge.collectFields]
            exact Or.inl (by
              simpa [hnormalized] using hscoped)
          · have htailMem :
                scopedField ∈
                  FieldMerge.collectFields schema runtimeType
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) :=
              ih htail
            rw [show
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema (objectType :: rest) selectionSet =
                  Selection.inlineFragment (some objectType) []
                    (selection :: normalizedRest)
                    :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet by
              simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized]]
            simp [FieldMerge.collectFields]
            exact Or.inr htailMem

theorem fieldsInSetCanMerge_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    runtimeType ∈ possibleTypes ->
    FieldMerge.fieldsInSetCanMerge schema runtimeType
      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
        possibleTypes selectionSet) ->
      FieldMerge.fieldsInSetCanMerge schema runtimeType
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hmem hmerge
  apply FieldMerge.fieldsInSetCanMerge_mono schema runtimeType
    (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
      possibleTypes selectionSet)
    hmerge
  intro scopedField hscoped
  exact
    fieldMerge_collectFields_possibleTypeNormalizations_runtime_branch_mem
      schema runtimeType possibleTypes selectionSet scopedField hmem hscoped

theorem selectionSetImplementationValidInScope_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes -> schema.objectType objectType) ->
    runtimeType ∈ possibleTypes ->
    Validation.selectionSetImplementationValidInScope schema
      variableDefinitions runtimeType
      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
        possibleTypes selectionSet) ->
      Validation.selectionSetImplementationValidInScope schema
        variableDefinitions runtimeType
        (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hobjects hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      intro himplementation
      have hrestObjects :
          ∀ candidate, candidate ∈ rest -> schema.objectType candidate := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            simpa [hnormalized] using
              NormalForm.GroundTypeNormalization.selectionSetImplementationValidInScope_nil
                schema variableDefinitions runtimeType
          · have htailImplementation :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions runtimeType
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) := by
              simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized] using himplementation
            exact ih hrestObjects htail htailImplementation
      | cons selection normalizedRest =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            have hparts :
                Validation.selectionImplementationValid schema
                    variableDefinitions runtimeType
                    (Selection.inlineFragment (some runtimeType) []
                      (selection :: normalizedRest))
                  ∧
                  Validation.selectionSetImplementationValidInScope schema
                    variableDefinitions runtimeType
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) := by
              simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized,
                Validation.selectionSetImplementationValidInScope] using
                himplementation
            have hheadImplementation :
                Validation.selectionImplementationValid schema
                  variableDefinitions runtimeType
                  (Selection.inlineFragment (some runtimeType) []
                    (selection :: normalizedRest)) :=
              hparts.1
            have hoverlap :
                schema.typesOverlapBool runtimeType runtimeType = true :=
              NormalForm.object_typesOverlapBool_self schema
                (hobjects runtimeType (by simp))
            have hbranch :
                Validation.selectionSetImplementationValidInScope schema
                    variableDefinitions runtimeType
                    (selection :: normalizedRest)
                  ∧
                  (∀ objectType,
                    objectType ∈ schema.getPossibleTypes runtimeType ->
                      Validation.selectionSetImplementationValidInScope schema
                        variableDefinitions objectType
                        (selection :: normalizedRest)) := by
              simpa [Validation.selectionImplementationValid] using
                hheadImplementation hoverlap
            simpa [hnormalized] using hbranch.1
          · have htailImplementation :
                Validation.selectionSetImplementationValidInScope schema
                  variableDefinitions runtimeType
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) := by
              have hparts :
                  Validation.selectionImplementationValid schema
                      variableDefinitions runtimeType
                      (Selection.inlineFragment (some objectType) []
                        (selection :: normalizedRest))
                    ∧
                    Validation.selectionSetImplementationValidInScope schema
                      variableDefinitions runtimeType
                      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                        schema rest selectionSet) := by
                simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                  hnormalized,
                  Validation.selectionSetImplementationValidInScope] using
                  himplementation
              exact hparts.2
            exact ih hrestObjects htail htailImplementation

theorem freshPrefixSelectionDerivation_possibleTypeNormalizations_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : Option ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection) :
    (∀ objectType, objectType ∈ possibleTypes ->
      NormalForm.objectTypeNameBool schema objectType = true) ->
    possibleTypes.Nodup ->
    (∀ objectType, objectType ∈ possibleTypes ->
      objectType = runtimeType ->
      FreshPrefixSelectionDerivation schema variableValues runtimeType
        (.object runtimeType ref)
        (NormalForm.normalizeSelectionSet schema objectType selectionSet)) ->
      FreshPrefixSelectionDerivation schema variableValues runtimeType
        (.object runtimeType ref)
        (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
          possibleTypes selectionSet) := by
  intro hobjects hnodup hnormalized
  induction possibleTypes with
  | nil =>
      simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations]
      exact FreshPrefixSelectionDerivation.nil
  | cons objectType rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestDerivation :
          FreshPrefixSelectionDerivation schema variableValues runtimeType
            (.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema rest selectionSet) :=
        ih hrestObjects hparts.2
          (fun candidate hcandidate heq =>
            hnormalized candidate
              (List.mem_cons_of_mem objectType hcandidate) heq)
      cases hnormalizedSet :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
            hnormalizedSet] using hrestDerivation
      | cons selection restSelection =>
          have hhead :
              FreshPrefixSelectionDerivation schema variableValues runtimeType
                (.object runtimeType ref)
                [Selection.inlineFragment (some objectType) []
                  (selection :: restSelection)] :=
            FreshPrefixSelectionDerivation.inlineFragmentSome objectType []
              (selection :: restSelection)
              (by
                intro _hallow happly
                by_cases heq : objectType = runtimeType
                · subst objectType
                  simpa [hnormalizedSet] using
                    hnormalized runtimeType (by simp) rfl
                · have hskip :
                      Execution.doesFragmentTypeApplyBool schema runtimeType
                          (.object runtimeType ref) objectType =
                        false :=
                    NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                      schema (ref := ref) hobject heq
                  rw [hskip] at happly
                  contradiction)
          have hdisjoint :
              GraphQL.NormalForm.executableGroupNamesDisjoint
                (GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  [Selection.inlineFragment (some objectType) []
                    (selection :: restSelection)])
                (GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet)) := by
            by_cases heq : objectType = runtimeType
            · subst objectType
              have hrestNotin : runtimeType ∉ rest := hparts.1
              have hrestCollect :
                  GraphQL.Execution.collectFields schema variableValues
                    runtimeType (.object runtimeType ref)
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) = [] :=
                NormalForm.GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
                  schema variableValues runtimeType (ref := ref) rest
                  selectionSet hrestObjects hrestNotin
              intro responseName _hleft hright
              rw [hrestCollect] at hright
              simp at hright
            · have hheadCollect :
                  GraphQL.Execution.collectFields schema variableValues
                    runtimeType (.object runtimeType ref)
                    [Selection.inlineFragment (some objectType) []
                      (selection :: restSelection)] = [] := by
                rw [NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
                  schema variableValues runtimeType objectType
                  (.object runtimeType ref) (selection :: restSelection) []]
                · simp [GraphQL.Execution.collectFields]
                · exact
                  NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                    schema (ref := ref) hobject heq
              intro responseName hleft _hright
              rw [hheadCollect] at hleft
              simp at hleft
          rw [show
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema (objectType :: rest) selectionSet =
                [Selection.inlineFragment (some objectType) []
                  (selection :: restSelection)] ++
                  NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet by
            simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalizedSet]]
          exact
            FreshPrefixSelectionDerivation.appendDisjoint
              [Selection.inlineFragment (some objectType) []
                (selection :: restSelection)]
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema rest selectionSet)
              hhead hrestDerivation hdisjoint

theorem freshPrefixSelectionDerivation_generatedNormalizedFieldChild_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : Option ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
      FreshPrefixSelectionDerivation schema variableValues childRuntime
        (.object childRuntime ref) childSelectionSet := by
  intro hschema hinclude hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    rw [hchild]
    simp [hobject]
    exact
      FreshPrefixSelectionDerivation.of_allFields_directiveFree_responseNamesNodup
        schema variableValues childType (.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childType sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childType sourceSelectionSet)
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    rw [hchild]
    simp [hfalse]
    apply freshPrefixSelectionDerivation_possibleTypeNormalizations_runtime
      schema variableValues childRuntime ref (schema.getPossibleTypes childType)
      sourceSelectionSet
    · intro objectType hobjectType
      exact NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType schema
        (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
          childType objectType hobjectType)
    · exact
        SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
          childType
    · intro objectType _hobjectType heq
      subst objectType
      exact
        FreshPrefixSelectionDerivation.of_allFields_directiveFree_responseNamesNodup
          schema variableValues childRuntime (.object childRuntime ref)
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet)
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
            schema childRuntime sourceSelectionSet)
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
            schema childRuntime sourceSelectionSet hsourceFree)
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
            schema childRuntime sourceSelectionSet)

theorem generatedNormalizedFieldChild_of_collectFields_field_layer
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.Value ObjectRef)
    (selectionSet : List Selection)
    (hall : NormalForm.selectionsAllFields selectionSet)
    (hfree : NormalForm.selectionSetDirectiveFree selectionSet)
    (hnodup : NormalForm.responseNamesNodup selectionSet)
    (hchildren :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
          childSelectionSet ∈ selectionSet ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          childSelectionSet) :
    ∀ {responseName : Name} {field : Execution.ExecutableField}
      {fields prefixTail : List Execution.ExecutableField},
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet := by
  intro responseName field fields prefixTail hgroup hprefix
  rcases
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_field_mem_prefix_empty
        schema variableValues parentType source selectionSet hall hfree hnodup
        hgroup hprefix with
    ⟨hfieldMem, _hfields, _hprefixTail⟩
  rcases List.mem_map.mp hfieldMem with
    ⟨selection, hselectionMem, hfieldEq⟩
  have hselectionField : Selection.isField selection :=
    hall selection hselectionMem
  cases selection with
  | field selectionResponseName selectionFieldName selectionArguments
      selectionDirectives selectionSet =>
      have hfieldEq' :
          field =
            FreshPrefixSelectionDerivation.executableFieldOfSelection
              parentType
              (Selection.field selectionResponseName selectionFieldName
                selectionArguments selectionDirectives selectionSet) :=
        hfieldEq.symm
      subst field
      exact
        hchildren selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet hselectionMem
  | inlineFragment typeCondition directives selectionSet =>
      simp [Selection.isField] at hselectionField

theorem normalizeSelectionSet_field_child_generated
    (schema : Schema) :
    ∀ parentType selectionSet responseName fieldName arguments directives
      childSelectionSet,
      NormalForm.selectionSetDirectiveFree selectionSet ->
      Selection.field responseName fieldName arguments directives
          childSelectionSet ∈
        NormalForm.normalizeSelectionSet schema parentType selectionSet ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          childSelectionSet := by
  intro parentType selectionSet
  induction parentType, selectionSet using
    NormalForm.normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro responseName fieldName arguments directives childSelectionSet _hfree
        hmem
      simp [NormalForm.normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      intro targetResponseName targetFieldName targetArguments
        targetDirectives childSelectionSet hfree hmem
      have hrestFree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.withoutFieldsWithResponseName schema responseName
              rest) :=
        NormalForm.withoutFieldsWithResponseName_directiveFree schema
          responseName rest (NormalForm.selectionSetDirectiveFree_tail hfree)
      exact hrest targetResponseName targetFieldName targetArguments
        targetDirectives childSelectionSet hrestFree
        (by
          simpa [NormalForm.normalizeSelectionSet, hlookup] using hmem)
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro targetResponseName targetFieldName targetArguments
        targetDirectives childSelectionSet hfree hmem
      have hheadFree :
          NormalForm.selectionDirectiveFree
            (Selection.field responseName fieldName arguments directives
              selectionSet) :=
        NormalForm.selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.1
      subst directives
      have hrestFree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.withoutFieldsWithResponseName schema responseName
              rest) :=
        NormalForm.withoutFieldsWithResponseName_directiveFree schema
          responseName rest (NormalForm.selectionSetDirectiveFree_tail hfree)
      have hmergedFree :
          NormalForm.selectionSetDirectiveFree mergedSubselections := by
        simpa [matching, mergedSubselections] using
          NormalForm.selectionSetDirectiveFree_fieldHead_merged schema
            parentType responseName fieldName arguments selectionSet rest hfree
      simp [NormalForm.normalizeSelectionSet, hlookup,
        NormalForm.normalizedField] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponse, hfield, harguments,
          hdirectives, hchild⟩
        subst targetResponseName
        subst targetFieldName
        subst targetArguments
        subst targetDirectives
        subst childSelectionSet
        have hreturnEq :
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
              =
            returnType := by
          simp [Schema.fieldReturnType?, hlookup, returnType]
        refine ⟨mergedSubselections, hmergedFree, ?_⟩
        rw [hreturnEq]
        simp [returnType, mergedSubselections, matching,
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations]
        rfl
      · exact hrest targetResponseName targetFieldName targetArguments
          targetDirectives childSelectionSet hrestFree htail
  | case4 parentType rest directives selectionSet happend =>
      intro responseName fieldName arguments targetDirectives childSelectionSet
        hfree hmem
      have hheadFree :
          NormalForm.selectionDirectiveFree
            (Selection.inlineFragment none directives selectionSet) :=
        NormalForm.selectionSetDirectiveFree_head hfree
      have hselectionFree :
          NormalForm.selectionSetDirectiveFree selectionSet := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.2
      have htailFree :
          NormalForm.selectionSetDirectiveFree rest :=
        NormalForm.selectionSetDirectiveFree_tail hfree
      have happendFree :
          NormalForm.selectionSetDirectiveFree (selectionSet ++ rest) :=
        NormalForm.selectionSetDirectiveFree_append hselectionFree htailFree
      exact happend responseName fieldName arguments targetDirectives
        childSelectionSet happendFree
        (by simpa [NormalForm.normalizeSelectionSet] using hmem)
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
      intro responseName fieldName arguments targetDirectives childSelectionSet
        hfree hmem
      have hheadFree :
          NormalForm.selectionDirectiveFree
            (Selection.inlineFragment (some typeCondition) directives
              selectionSet) :=
        NormalForm.selectionSetDirectiveFree_head hfree
      have hselectionFree :
          NormalForm.selectionSetDirectiveFree selectionSet := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.2
      have htailFree :
          NormalForm.selectionSetDirectiveFree rest :=
        NormalForm.selectionSetDirectiveFree_tail hfree
      have happendFree :
          NormalForm.selectionSetDirectiveFree (selectionSet ++ rest) :=
        NormalForm.selectionSetDirectiveFree_append hselectionFree htailFree
      exact happend responseName fieldName arguments targetDirectives
        childSelectionSet happendFree
        (by simpa [NormalForm.normalizeSelectionSet, hoverlap] using hmem)
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      intro responseName fieldName arguments targetDirectives childSelectionSet
        hfree hmem
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      have htailFree :
          NormalForm.selectionSetDirectiveFree rest :=
        NormalForm.selectionSetDirectiveFree_tail hfree
      exact hrest responseName fieldName arguments targetDirectives
        childSelectionSet htailFree
        (by simpa [NormalForm.normalizeSelectionSet, hfalse] using hmem)

theorem completeValue_eq_spec_of_child_selectionSet_eq
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) :
    ∀ depth parentType selectionSet (value : Execution.Value ObjectRef),
      (∀ childDepth runtimeType ref,
        childDepth < depth ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          visitSubfields schema resolvers variableValues childDepth runtimeType
              (Execution.Value.object runtimeType ref) selectionSet
              (Execution.Response.object [])
            =
            Execution.Response.object
              (Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.Value.object runtimeType ref) selectionSet)) ->
        completeValue schema resolvers variableValues depth parentType
            selectionSet value Execution.Response.null
          =
          Execution.completeValue schema resolvers variableValues depth
            parentType (selectionSet.map Execution.selectionExecutableField)
            value
  | 0, _parentType, _selectionSet, _value, _hchild => by
      simp [completeValue, Execution.completeValue]
  | depth + 1, parentType, selectionSet, value, hchild => by
      cases value with
      | null =>
          simp [completeValue, Execution.completeValue]
      | scalar value =>
          simp [completeValue, Execution.completeValue]
      | object runtimeType ref =>
          by_cases hinclude :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · simp [completeValue, Execution.completeValue, hinclude]
            simpa [Execution.executeSelectionSet,
              Execution.executeRootSelectionSet] using
              hchild depth runtimeType ref (Nat.lt_succ_self depth)
                hinclude
          · have hfalse :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool parentType runtimeType
              · rfl
              · contradiction
            simp [completeValue, Execution.completeValue, hfalse]
      | list values =>
          let ungroupedComplete :=
            fun value previous =>
              completeValue schema resolvers variableValues depth parentType
                selectionSet value previous
          let specComplete :=
            fun value =>
              Execution.completeValue schema resolvers variableValues depth
                parentType
                (selectionSet.map Execution.selectionExecutableField) value
          have hvalues :
              values.map
                  (fun value =>
                    ungroupedComplete value Execution.Response.null)
                =
                values.map specComplete := by
            apply List.map_congr_left
            intro value hvalue
            exact completeValue_eq_spec_of_child_selectionSet_eq schema
              resolvers variableValues depth parentType selectionSet value
              (by
                intro childDepth runtimeType ref hlt hinclude
                exact hchild childDepth runtimeType ref
                  (Nat.lt_trans hlt (Nat.lt_succ_self depth)) hinclude)
          have hfold :
              ((values.foldl
                (fun (state :
                    List Execution.Response × List Execution.Response)
                    value =>
                  (completeValue schema resolvers variableValues depth
                        parentType selectionSet value
                        (match state.snd with
                        | [] => Execution.Response.null
                        | previous :: _rest => previous) ::
                      state.fst,
                    match state.snd with
                    | [] => []
                    | _previous :: rest => rest))
                ([], [])).fst).reverse =
                values.map (fun value =>
                  ungroupedComplete value Execution.Response.null) := by
            simpa [ungroupedComplete] using
              foldlCompleteValues_no_previous_eq_map
                (ObjectRef := ObjectRef) ungroupedComplete values []
          simpa [completeValue, Execution.completeValue, specComplete] using
            congrArg Execution.Response.list (hfold.trans hvalues)

theorem visitSubfields_eq_spec_append_of_allFields
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (childReady : Name -> List Selection -> Prop)
    (hchild :
      ∀ childDepth childType runtimeType ref childSelectionSet,
        childDepth < depth ->
        schema.typeIncludesObjectBool childType runtimeType = true ->
        childReady childType childSelectionSet ->
        NormalForm.selectionSetNormal schema childSelectionSet ->
        NormalForm.selectionSetDirectiveFree childSelectionSet ->
          visitSubfields schema resolvers variableValues childDepth runtimeType
              (Execution.Value.object runtimeType ref) childSelectionSet
              (Execution.Response.object [])
            =
            Execution.Response.object
              (Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.Value.object runtimeType ref)
                childSelectionSet)) :
    ∀ selectionSet outputFields,
      NormalForm.selectionsAllFields selectionSet ->
      NormalForm.selectionSetDirectiveFree selectionSet ->
      NormalForm.selectionSetNormal schema selectionSet ->
      outputNamesFreeForSelectionSet schema parentType outputFields
        selectionSet ->
      (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
          childSelectionSet ∈ selectionSet ->
          childReady
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            childSelectionSet) ->
        visitSubfields schema resolvers variableValues depth parentType source
            selectionSet (Execution.Response.object outputFields)
          =
        Execution.Response.object
          (outputFields ++
            Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source selectionSet)
  | [], outputFields, _hall, _hfree, _hnormal, _houtput, _hchildren => by
      simp [visitSubfields, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet, Execution.collectFields,
        Execution.executeCollectedFields]
  | Selection.field responseName fieldName arguments directives selectionSet
      :: rest,
      outputFields, hall, hfree, hnormal, houtput, hchildren => by
      cases depth with
      | zero =>
          simp [visitSubfields_depth_zero schema resolvers variableValues
            parentType source
            (Selection.field responseName fieldName arguments directives
              selectionSet :: rest)
            (Execution.Response.object outputFields),
            executeSelectionSet_depth_zero schema resolvers variableValues
              parentType source
              (Selection.field responseName fieldName arguments directives
                selectionSet :: rest)]
      | succ depth' =>
          have hheadFree := NormalForm.selectionSetDirectiveFree_head hfree
          have htailFree := NormalForm.selectionSetDirectiveFree_tail hfree
          have hdirectives : directives = [] := by
            simpa [NormalForm.selectionDirectiveFree] using hheadFree.1
          subst directives
          have htailAll :
              NormalForm.selectionsAllFields rest := by
            intro candidate hcandidate
            exact hall candidate
              (List.mem_cons_of_mem
                (Selection.field responseName fieldName arguments []
                  selectionSet) hcandidate)
          have htailNormal :
              NormalForm.selectionSetNormal schema rest :=
            selectionSetNormal_tail hnormal
          have hchildNormal :
              NormalForm.selectionSetNormal schema selectionSet :=
            selectionSetNormal_field_child hnormal
          have hchildFree :
              NormalForm.selectionSetDirectiveFree selectionSet := by
            simpa [NormalForm.selectionDirectiveFree] using hheadFree.2
          let childType :=
            (schema.fieldReturnType? parentType fieldName).getD fieldName
          have hchildReady :
              childReady childType selectionSet :=
            hchildren responseName fieldName arguments [] selectionSet
              (by simp)
          have hfieldNotOutput :
              responseName ∉ outputFields.map Prod.fst :=
            responseName_not_mem_output_of_field_head_outputNamesFree
              houtput
          have hpreviousNone :
              responseObjectField? responseName
                  (Execution.Response.object outputFields) =
                none :=
            responseObjectField?_eq_none_of_not_mem hfieldNotOutput
          let executable :=
            executableField parentType responseName fieldName arguments
              selectionSet
          let resolved :=
            resolvers.resolve parentType fieldName arguments source
          have hcomplete :
              completeValue schema resolvers variableValues depth' childType
                  selectionSet resolved Execution.Response.null
                =
              Execution.completeValue schema resolvers variableValues depth'
                childType (selectionSet.map Execution.selectionExecutableField)
                resolved :=
            completeValue_eq_spec_of_child_selectionSet_eq schema resolvers
              variableValues depth' childType selectionSet resolved
              (by
                intro childDepth runtimeType ref hlt hinclude
                exact hchild childDepth childType runtimeType ref selectionSet
                  (Nat.lt_succ_of_lt hlt) hinclude hchildReady hchildNormal
                  hchildFree)
          have htailResponseFree :
              NormalForm.selectionSetResponseNameFree schema parentType
                responseName rest := by
            have hresponseNodup : NormalForm.responseNamesNodup
                (Selection.field responseName fieldName arguments []
                  selectionSet :: rest) := by
              have hnormalUnfold := hnormal
              unfold NormalForm.selectionSetNormal at hnormalUnfold
              have hnonRedundant := hnormalUnfold.2
              unfold NormalForm.selectionSetNonRedundant at hnonRedundant
              exact hnonRedundant.1
            unfold NormalForm.responseNamesNodup at hresponseNodup
            have hnotMem :
                responseName ∉ rest.filterMap Selection.responseName? := by
              simpa [Selection.responseName?] using
                (List.nodup_cons.mp hresponseNodup).1
            exact selectionSetResponseNameFree_of_allFields_responseNamesNodup
              schema parentType responseName rest htailAll hnotMem
          have hnotInRestCollect :
              responseName ∉
                (Execution.collectFields schema variableValues parentType
                  source rest).map Prod.fst :=
            collectFields_responseName_not_mem_of_allFields_responseNameFree
              schema variableValues parentType source responseName rest
              htailAll htailFree htailResponseFree
          have htailOutput :
              outputNamesFreeForSelectionSet schema parentType
                (outputFields ++ [(responseName,
                  Execution.completeValue schema resolvers variableValues
                    depth' childType
                    (selectionSet.map Execution.selectionExecutableField)
                    resolved)]) rest := by
            apply outputNamesFreeForSelectionSet_cons_output
            · exact outputNamesFreeForSelectionSet_tail houtput
            · exact htailResponseFree
          have htail :=
            visitSubfields_eq_spec_append_of_allFields schema resolvers
              variableValues (depth' + 1) parentType source childReady
              hchild rest (outputFields ++ [(responseName,
                Execution.completeValue schema resolvers variableValues
                  depth' childType
                  (selectionSet.map Execution.selectionExecutableField)
                resolved)])
              htailAll htailFree htailNormal htailOutput
              (by
                intro tailResponseName tailFieldName tailArguments
                  tailDirectives tailSelectionSet htailMem
                exact hchildren tailResponseName tailFieldName tailArguments
                  tailDirectives tailSelectionSet
                  (List.mem_cons_of_mem
                    (Selection.field responseName fieldName arguments []
                      selectionSet)
                    htailMem))
          have hspecSingleton :
              Execution.completeValue schema resolvers variableValues depth'
                  childType
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := selectionSet
                  }]
                  resolved
                =
              Execution.completeValue schema resolvers variableValues depth'
                childType (selectionSet.map Execution.selectionExecutableField)
                resolved :=
            NormalForm.completeValue_singleton_selectionSet_eq schema
              resolvers variableValues depth' childType
              {
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              selectionSet resolved
          have hvisitHead :
              visitSelection schema resolvers variableValues (depth' + 1)
                  parentType source
                  (Selection.field responseName fieldName arguments []
                    selectionSet)
                  (Execution.Response.object outputFields)
                =
              Execution.Response.object
                (outputFields ++ [(responseName,
                  Execution.completeValue schema resolvers variableValues
                    depth' childType
                    (selectionSet.map Execution.selectionExecutableField)
                    resolved)]) := by
            simp [visitSelection, Execution.selectionDirectivesAllowBool,
              executeField, executableField, hpreviousNone,
              mergeResponseFieldIntoObject,
              mergeResponseField_eq_append_of_not_mem, hfieldNotOutput,
              hcomplete, resolved, childType]
          simp [visitSubfields, hvisitHead]
          rw [htail]
          simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
            NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
              schema variableValues parentType source responseName fieldName
              arguments selectionSet rest hnotInRestCollect,
            Execution.executeCollectedFields, Execution.executeField]
          exact hspecSingleton.symm
  | Selection.inlineFragment typeCondition directives selectionSet :: rest,
      outputFields, hall, _hfree, _hnormal, _houtput, _hchildren => by
      have hheadField :
          Selection.isField
            (Selection.inlineFragment typeCondition directives selectionSet) :=
        hall _ (by simp)
      simp [Selection.isField] at hheadField

theorem visitSubfields_eq_spec_of_allFields
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection)
    (hchild :
      ∀ childDepth childType runtimeType ref childSelectionSet,
        childDepth < depth ->
        schema.typeIncludesObjectBool childType runtimeType = true ->
        NormalForm.selectionSetNormal schema childSelectionSet ->
        NormalForm.selectionSetDirectiveFree childSelectionSet ->
          visitSubfields schema resolvers variableValues childDepth runtimeType
              (Execution.Value.object runtimeType ref) childSelectionSet
              (Execution.Response.object [])
            =
            Execution.Response.object
              (Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.Value.object runtimeType ref)
                childSelectionSet)) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetNormal schema selectionSet ->
      visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source selectionSet) := by
  intro hall hfree hnormal
  simpa using
    visitSubfields_eq_spec_append_of_allFields schema resolvers
      variableValues depth parentType source (fun _ _ => True)
      (by
        intro childDepth childType runtimeType ref childSelectionSet hlt
          hinclude _hready
        exact hchild childDepth childType runtimeType ref childSelectionSet hlt
          hinclude)
      selectionSet []
      hall hfree hnormal
      (outputNamesFreeForSelectionSet_nil schema parentType selectionSet)
      (by
        intro responseName fieldName arguments directives childSelectionSet hmem
        exact True.intro)

theorem generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : Option ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
    ∀ {responseName : Name} {field : Execution.ExecutableField}
      {fields prefixTail : List Execution.ExecutableField},
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues childRuntime
          (.object childRuntime ref) childSelectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet := by
  intro hschema hinclude hgenerated responseName field fields prefixTail hgroup
    hprefix
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType sourceSelectionSet := by
      simpa [hobject] using hchild
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childType
            (.object childType ref)
            (NormalForm.normalizeSelectionSet schema childType
              sourceSelectionSet) := by
      simpa [hchildEq] using hgroup
    exact
      generatedNormalizedFieldChild_of_collectFields_field_layer
        schema variableValues childType (.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childType sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childType sourceSelectionSet)
        (fun responseName fieldName arguments directives grandchildSelectionSet
            hmem =>
          normalizeSelectionSet_field_child_generated schema childType
            sourceSelectionSet responseName fieldName arguments directives
            grandchildSelectionSet hsourceFree hmem)
        hgroup' hprefix
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
            (.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) := by
      have hgroupPossible :
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues childRuntime
              (.object childRuntime ref)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema (schema.getPossibleTypes childType)
                sourceSelectionSet) := by
        simpa [hchildEq] using hgroup
      simpa [hcollect] using hgroupPossible
    exact
      generatedNormalizedFieldChild_of_collectFields_field_layer
        schema variableValues childRuntime (.object childRuntime ref)
        (NormalForm.normalizeSelectionSet schema childRuntime
          sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childRuntime sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childRuntime sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childRuntime sourceSelectionSet)
        (fun responseName fieldName arguments directives grandchildSelectionSet
            hmem =>
          normalizeSelectionSet_field_child_generated schema childRuntime
            sourceSelectionSet responseName fieldName arguments directives
            grandchildSelectionSet hsourceFree hmem)
        hgroup' hprefix

theorem collectFields_generatedNormalizedFieldChild_prefix_empty
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : Option ObjectRef)
    (childSelectionSet : List Selection) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
    ∀ {responseName : Name} {field : Execution.ExecutableField}
      {fields prefixTail : List Execution.ExecutableField},
      (responseName, field :: fields) ∈
        GraphQL.Execution.collectFields schema variableValues childRuntime
          (.object childRuntime ref) childSelectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        fields = [] ∧ prefixTail = [] := by
  intro hschema hinclude hgenerated responseName field fields prefixTail hgroup
    hprefix
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType sourceSelectionSet := by
      simpa [hobject] using hchild
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childType
            (.object childType ref)
            (NormalForm.normalizeSelectionSet schema childType
              sourceSelectionSet) := by
      simpa [hchildEq] using hgroup
    exact
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
        schema variableValues childType (.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childType sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childType sourceSelectionSet)
        hgroup' hprefix
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
            (.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) := by
      have hgroupPossible :
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues childRuntime
              (.object childRuntime ref)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema (schema.getPossibleTypes childType)
                sourceSelectionSet) := by
        simpa [hchildEq] using hgroup
      simpa [hcollect] using hgroupPossible
    exact
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
        schema variableValues childRuntime (.object childRuntime ref)
        (NormalForm.normalizeSelectionSet schema childRuntime sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childRuntime sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childRuntime sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childRuntime sourceSelectionSet)
        hgroup' hprefix

theorem collectFields_fieldNormal_childLocalFacts_object
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues)
    (parentType runtimeType : Name)
    (ref : Option ObjectRef)
    (selectionSet : List Selection)
    (responseName childRuntime : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    ScopedParentRuntimeApplies schema runtimeType parentType ->
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    NormalForm.selectionSetLookupValid schema parentType selectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      parentType selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    NormalForm.selectionsAllFields selectionSet ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues parentType
        (.object runtimeType ref) selectionSet ->
    schema.typeIncludesObjectBool
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      childRuntime = true ->
      NormalForm.selectionSetLookupValid schema childRuntime field.selectionSet
        ∧
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime field.selectionSet
        ∧
        (∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            field.selectionSet) := by
  intro hschema hparentRuntime hvalid hlookupValid himplementation hmerge
    hall hgroup hinclude
  have hcompatible :
      ∀ candidate, candidate ∈ field :: ([] : List Execution.ExecutableField) ->
        ∀ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType
            selectionSet ->
          ScopedFieldMatchesExecutableIdentity scopedField candidate ->
          ScopedFieldRuntimeApplies schema runtimeType scopedField ->
            schema.typeIncludesObjectBool scopedField.outputType.namedType
              childRuntime = true := by
    intro candidate hcandidate scopedField hscopedMem hmatch _hruntime
    have hcandidateEq : candidate = field := by
      simpa using hcandidate
    subst candidate
    have hparents :
        CollectedGroupsParent parentType
          (GraphQL.Execution.collectFields schema variableValues parentType
            (.object runtimeType ref) selectionSet) :=
      collectFields_parent schema variableValues parentType
        (.object runtimeType ref) selectionSet
    have hfieldParent : field.parentType = parentType :=
      hparents responseName (field :: fields) hgroup field (by simp)
    have hscopedParent : scopedField.parentType = parentType :=
      FreshPrefixSelectionDerivation.fieldMerge_collectFields_parent_of_allFields
        schema parentType selectionSet scopedField hall hscopedMem
    have hparent : field.parentType = scopedField.parentType :=
      hfieldParent.trans hscopedParent.symm
    have houtput :
        scopedField.outputType.namedType =
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName) :=
      FreshPrefixSelectionDerivation.scopedField_outputType_eq_fieldReturnType_of_identity_match
        schema variableDefinitions parentType selectionSet scopedField field
        hvalid hscopedMem hparent hmatch
    simpa [houtput] using hinclude
  rcases
      collectFields_group_prefix_mergedFieldSelectionSet_childLocalFacts_object
        schema variableDefinitions variableValues parentType parentType
        runtimeType ref selectionSet responseName childRuntime field fields
        ([] : List Execution.ExecutableField) hschema hparentRuntime hvalid
        hlookupValid himplementation hmerge hgroup
        (by
          intro candidate hcandidate
          cases hcandidate)
        hcompatible with
    ⟨hchildLookup, hchildImplementation, hchildMerge⟩
  exact ⟨
    by simpa [GraphQL.Execution.mergedFieldSelectionSet] using hchildLookup,
    by simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildImplementation,
    by
      intro objectType
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        hchildMerge objectType⟩

theorem collectFields_generatedNormalizedFieldChild_childLocalFacts
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : Option ObjectRef)
    (childSelectionSet : List Selection)
    (responseName grandchildRuntime : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField) :
    SchemaWellFormedness.schemaWellFormed schema ->
    schema.typeIncludesObjectBool childType childRuntime = true ->
    generatedNormalizedFieldChild schema childType childSelectionSet ->
    NormalForm.selectionSetLookupValid schema childRuntime childSelectionSet ->
    Validation.selectionSetImplementationValidInScope schema variableDefinitions
      childRuntime childSelectionSet ->
    (∀ objectType,
      FieldMerge.fieldsInSetCanMerge schema objectType childSelectionSet) ->
    (responseName, field :: fields) ∈
      GraphQL.Execution.collectFields schema variableValues childRuntime
        (.object childRuntime ref) childSelectionSet ->
    schema.typeIncludesObjectBool
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      grandchildRuntime = true ->
      NormalForm.selectionSetLookupValid schema grandchildRuntime
          field.selectionSet
        ∧
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions grandchildRuntime field.selectionSet
        ∧
        (∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            field.selectionSet) := by
  intro hschema hinclude hgenerated hlookupValid himplementation hmerge
    hgroup hgrandchild
  have hchildObject : schema.objectType childRuntime :=
    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
      childType childRuntime (List.contains_iff_mem.mp hinclude)
  have hparentRuntime : ScopedParentRuntimeApplies schema childRuntime childRuntime :=
    NormalForm.object_typeIncludesObjectBool_self schema hchildObject
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType sourceSelectionSet := by
      simpa [hobject] using hchild
    have hall :
        NormalForm.selectionsAllFields childSelectionSet := by
      simpa [hchildEq] using
        NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet
    have hvalid :
        Validation.selectionSetValid schema variableDefinitions childType
          childSelectionSet :=
      NormalForm.GroundTypeNormalization.selectionSetValid_of_allFields_implementationValidInScope
        schema variableDefinitions childType childSelectionSet hall
        himplementation
    exact
      collectFields_fieldNormal_childLocalFacts_object schema
        variableDefinitions variableValues childType childType ref
        childSelectionSet responseName grandchildRuntime field fields hschema
        hparentRuntime hvalid hlookupValid himplementation (hmerge childType)
        hall hgroup hgrandchild
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
    have hobjectTypes :
        ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
          schema.objectType objectType := by
      intro objectType hobjectType
      exact
        SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
          childType objectType hobjectType
    have hpossibleNodup :
        (schema.getPossibleTypes childType).Nodup :=
      SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType
    have hcollect :
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) := by
      have hgroupPossible :
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues childRuntime
              (.object childRuntime ref)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema (schema.getPossibleTypes childType)
                sourceSelectionSet) := by
        simpa [hchildEq] using hgroup
      simpa [hcollect] using hgroupPossible
    have hlookupPossible :
        NormalForm.selectionSetLookupValid schema childRuntime
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) := by
      simpa [hchildEq] using hlookupValid
    have hlookupBranch :
        NormalForm.selectionSetLookupValid schema childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      selectionSetLookupValid_possibleTypeNormalizations_runtime_branch
        schema childRuntime (schema.getPossibleTypes childType)
        sourceSelectionSet hpossibleMem hlookupPossible
    have himplementationPossible :
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) := by
      simpa [hchildEq] using himplementation
    have himplementationBranch :
        Validation.selectionSetImplementationValidInScope schema
          variableDefinitions childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      selectionSetImplementationValidInScope_possibleTypeNormalizations_runtime_branch
        schema variableDefinitions childRuntime
        (schema.getPossibleTypes childType) sourceSelectionSet hobjectTypes
        hpossibleMem himplementationPossible
    have hmergePossible :
        FieldMerge.fieldsInSetCanMerge schema childRuntime
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) := by
      simpa [hchildEq] using hmerge childRuntime
    have hmergeBranch :
        FieldMerge.fieldsInSetCanMerge schema childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      fieldsInSetCanMerge_possibleTypeNormalizations_runtime_branch schema
        childRuntime (schema.getPossibleTypes childType) sourceSelectionSet
        hpossibleMem hmergePossible
    have hall :
        NormalForm.selectionsAllFields
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
        schema childRuntime sourceSelectionSet
    have hvalid :
        Validation.selectionSetValid schema variableDefinitions childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.selectionSetValid_of_allFields_implementationValidInScope
        schema variableDefinitions childRuntime
        (NormalForm.normalizeSelectionSet schema childRuntime
          sourceSelectionSet) hall himplementationBranch
    exact
      collectFields_fieldNormal_childLocalFacts_object schema
        variableDefinitions variableValues childRuntime childRuntime ref
        (NormalForm.normalizeSelectionSet schema childRuntime
          sourceSelectionSet)
        responseName grandchildRuntime field fields hschema hparentRuntime
        hvalid hlookupBranch himplementationBranch hmergeBranch hall hgroup'
        hgrandchild

theorem visitSubfields_eq_spec_of_allFields_with_childReady
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection)
    (childReady : Name -> List Selection -> Prop)
    (hchild :
      ∀ childDepth childType runtimeType ref childSelectionSet,
        childDepth < depth ->
        schema.typeIncludesObjectBool childType runtimeType = true ->
        childReady childType childSelectionSet ->
        NormalForm.selectionSetNormal schema childSelectionSet ->
        NormalForm.selectionSetDirectiveFree childSelectionSet ->
          visitSubfields schema resolvers variableValues childDepth runtimeType
              (Execution.Value.object runtimeType ref) childSelectionSet
              (Execution.Response.object [])
            =
            Execution.Response.object
              (Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.Value.object runtimeType ref)
                childSelectionSet)) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetNormal schema selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ selectionSet ->
        childReady
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          childSelectionSet) ->
      visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source selectionSet) := by
  intro hall hfree hnormal hchildren
  simpa using
    visitSubfields_eq_spec_append_of_allFields schema resolvers
      variableValues depth parentType source childReady hchild
      selectionSet [] hall hfree hnormal
      (outputNamesFreeForSelectionSet_nil schema parentType selectionSet)
      hchildren

theorem executeRootSelectionSet_eq_spec_of_allFieldsNormal
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection)
    (childReady : Name -> List Selection -> Prop)
    (hchild :
      ∀ childDepth childType runtimeType ref childSelectionSet,
        childDepth < depth ->
        schema.typeIncludesObjectBool childType runtimeType = true ->
        childReady childType childSelectionSet ->
        NormalForm.selectionSetNormal schema childSelectionSet ->
        NormalForm.selectionSetDirectiveFree childSelectionSet ->
          visitSubfields schema resolvers variableValues childDepth runtimeType
              (Execution.Value.object runtimeType ref) childSelectionSet
              (Execution.Response.object [])
            =
            Execution.Response.object
              (Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.Value.object runtimeType ref)
                childSelectionSet)) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetNormal schema selectionSet ->
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
  intro hall hfree hnormal hchildren
  have hvisit :=
    visitSubfields_eq_spec_of_allFields_with_childReady schema resolvers
      variableValues depth parentType source selectionSet childReady hchild
      hall hfree hnormal hchildren
  simp [executeRootSelectionSet]
  rw [hvisit]
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]

theorem executeQueryAtDepth_eq_spec_of_allFieldsNormal
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef)
    (childReady : Name -> List Selection -> Prop)
    (hchild :
      ∀ childDepth childType runtimeType ref childSelectionSet,
        childDepth < depth ->
        schema.typeIncludesObjectBool childType runtimeType = true ->
        childReady childType childSelectionSet ->
        NormalForm.selectionSetNormal schema childSelectionSet ->
        NormalForm.selectionSetDirectiveFree childSelectionSet ->
          visitSubfields schema resolvers variableValues childDepth runtimeType
              (Execution.Value.object runtimeType ref) childSelectionSet
              (Execution.Response.object [])
            =
            Execution.Response.object
              (Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType
                (Execution.Value.object runtimeType ref)
                childSelectionSet)) :
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
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
  intro hall hfree hnormal hchildren
  have hroot :=
    executeRootSelectionSet_eq_spec_of_allFieldsNormal schema resolvers
    variableValues depth operation.rootType source operation.selectionSet
    childReady hchild hall hfree hnormal hchildren
  cases hrootApplies :
      Execution.rootSourceAppliesBool schema operation source
  · simp [executeQueryAtDepth, Execution.executeQueryAtDepth, hrootApplies]
  · simp [executeQueryAtDepth, Execution.executeQueryAtDepth, hrootApplies,
      hroot]

theorem visitSubfields_normalizeSelectionSet_eq_spec
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ depth parentType (source : Execution.Value ObjectRef) selectionSet,
      NormalForm.selectionSetDirectiveFree selectionSet ->
        visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.normalizeSelectionSet schema parentType selectionSet)
            (Execution.Response.object [])
          =
        Execution.Response.object
          (Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (NormalForm.normalizeSelectionSet schema parentType selectionSet)) := by
  intro depth
  induction depth using Nat.strongRecOn with
  | ind depth ih =>
      intro parentType source selectionSet hfree
      apply visitSubfields_eq_spec_of_allFields_with_childReady
        (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (depth := depth) (parentType := parentType) (source := source)
        (selectionSet := NormalForm.normalizeSelectionSet schema parentType
          selectionSet)
        (childReady := generatedNormalizedFieldChild schema)
      · intro childDepth childType runtimeType ref childSelectionSet hlt
          hinclude hready _hnormal _hchildFree
        rcases hready with
          ⟨sourceSelectionSet, hsourceFree, hchildEq⟩
        subst childSelectionSet
        exact
          visitSubfields_normalizedFieldSubselections_eq_spec_of_runtime
            schema resolvers variableValues hschema childDepth
            childType runtimeType (ref := ref) sourceSelectionSet
            hinclude
            (ih childDepth hlt runtimeType
              (Execution.Value.object runtimeType ref) sourceSelectionSet
              hsourceFree)
      · exact
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
            schema parentType selectionSet
      · exact
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
            schema parentType selectionSet hfree
      · exact
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal
            schema hschema parentType selectionSet
      · intro responseName fieldName arguments directives childSelectionSet
          hmem
        exact normalizeSelectionSet_field_child_generated schema parentType
          selectionSet responseName fieldName arguments directives
          childSelectionSet hfree hmem

theorem visitSubfields_normalizeSelectionSet_eq_of_source_eq_spec
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (parentType : Name) (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) :
    NormalForm.objectTypeNameBool schema parentType = true ->
    (∃ runtimeType ref,
      source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true) ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetSemanticsReady schema parentType selectionSet ->
    FieldMerge.fieldsInSetCanMerge schema parentType selectionSet ->
    visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (Execution.Response.object [])
      =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source selectionSet) ->
      visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (Execution.Response.object [])
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (NormalForm.normalizeSelectionSet schema parentType selectionSet)
        (Execution.Response.object []) := by
  intro hobject hsource hfree hready hmerge hsourceSpec
  have hnormalizedSpec :
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.normalizeSelectionSet schema parentType selectionSet)
          (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (NormalForm.normalizeSelectionSet schema parentType selectionSet)) :=
    visitSubfields_normalizeSelectionSet_eq_spec schema resolvers
      variableValues hschema depth parentType source selectionSet hfree
  have hspecPreserved :
      Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source
          (NormalForm.normalizeSelectionSet schema parentType selectionSet)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source selectionSet :=
    NormalForm.GroundTypeNormalization.normalizeSelectionSet_executeSelectionSet
      schema resolvers variableValues hschema depth parentType source
      selectionSet hobject hsource hfree hready hmerge
  calc
    visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (Execution.Response.object [])
      =
        Execution.Response.object
          (Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source selectionSet) := hsourceSpec
    _ =
        Execution.Response.object
          (Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (NormalForm.normalizeSelectionSet schema parentType selectionSet)) := by
          rw [hspecPreserved]
    _ =
        visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.normalizeSelectionSet schema parentType selectionSet)
          (Execution.Response.object []) := hnormalizedSpec.symm

theorem executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
      visitSubfields schema resolvers variableValues depth operation.rootType
          source
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet)
          (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet))) ->
      executeQueryAtDepth schema resolvers variableValues operation depth source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth
        source := by
  intro hschema hcomplete hobject hsource hfree hready hmerge hsourceSpec
  apply executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_normalization
    schema operation resolvers variableValues depth source hcomplete
  intro runtimeCase hruntime hagrees
  exact
    visitSubfields_normalizeSelectionSet_eq_of_source_eq_spec schema resolvers
      variableValues hschema depth operation.rootType source
      (NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet)
      hobject hsource (hfree runtimeCase hruntime hagrees)
      (hready runtimeCase hruntime hagrees)
      (hmerge runtimeCase hruntime hagrees)
      (hsourceSpec runtimeCase hruntime hagrees)

theorem executeQueryAtDepth_completeNormalizeOperation_eq_of_filter_recursiveGroupedStates
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
  exact (hstates runtimeCase hruntime hagrees).visitSubfields_eq_spec

theorem visitSubfields_eq_spec_of_generatedNormalFields
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (parentType : Name)
    (source : Execution.Value ObjectRef)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetNormal schema selectionSet ->
    (∀ responseName fieldName arguments directives childSelectionSet,
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ selectionSet ->
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          childSelectionSet) ->
      visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (Execution.Response.object [])
        =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source selectionSet) := by
  intro hall hfree hnormal hchildren
  apply visitSubfields_eq_spec_of_allFields_with_childReady
    (schema := schema) (resolvers := resolvers)
    (variableValues := variableValues) (depth := depth)
    (parentType := parentType) (source := source)
    (selectionSet := selectionSet)
    (childReady := generatedNormalizedFieldChild schema)
  · intro childDepth childType runtimeType ref childSelectionSet _hlt
      hinclude hready _hchildNormal _hchildFree
    rcases hready with ⟨sourceSelectionSet, hsourceFree, hchildEq⟩
    subst childSelectionSet
    exact
      visitSubfields_normalizedFieldSubselections_eq_spec_of_runtime
        schema resolvers variableValues hschema childDepth childType
        runtimeType (ref := ref) sourceSelectionSet hinclude
        (visitSubfields_normalizeSelectionSet_eq_spec schema resolvers
          variableValues hschema childDepth runtimeType
          (Execution.Value.object runtimeType ref) sourceSelectionSet
          hsourceFree)
  · exact hall
  · exact hfree
  · exact hnormal
  · exact hchildren

theorem executeQueryAtDepth_eq_spec_of_generatedNormalOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
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
  intro hschema hall hfree hnormal hchildren
  apply executeQueryAtDepth_eq_spec_of_allFieldsNormal
    (schema := schema) (operation := operation) (resolvers := resolvers)
    (variableValues := variableValues) (depth := depth) (source := source)
    (childReady := generatedNormalizedFieldChild schema)
  · intro childDepth childType runtimeType ref childSelectionSet _hlt
      hinclude hready _hchildNormal _hchildFree
    rcases hready with ⟨sourceSelectionSet, hsourceFree, hchildEq⟩
    subst childSelectionSet
    exact
      visitSubfields_normalizedFieldSubselections_eq_spec_of_runtime
        schema resolvers variableValues hschema childDepth childType
        runtimeType (ref := ref) sourceSelectionSet hinclude
        (visitSubfields_normalizeSelectionSet_eq_spec schema resolvers
          variableValues hschema childDepth runtimeType
          (Execution.Value.object runtimeType ref) sourceSelectionSet
          hsourceFree)
  · exact hall
  · exact hfree
  · exact hnormal
  · exact hchildren

theorem executeQueryAtDepth_normalizeOperation_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
    (depth : Nat) (source : Execution.Value ObjectRef) :
    executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet ->
    executeQueryAtDepth schema resolvers variableValues operation depth source =
      Execution.executeQueryAtDepth schema resolvers variableValues operation
        depth source := by
  intro hroot
  cases hrootApplies :
      Execution.rootSourceAppliesBool schema operation source
  · simp [executeQueryAtDepth, Execution.executeQueryAtDepth, hrootApplies]
  · simp [executeQueryAtDepth, Execution.executeQueryAtDepth, hrootApplies,
      hroot]

theorem executeRootSelectionSet_completeNormalizeOperation_eq_spec_of_runtime_body
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef)
    (runtimeCase : NormalForm.BoolCase) :
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
    visitSubfields schema resolvers variableValues depth operation.rootType
        source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet))
        (Execution.Response.object [])
      =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.normalizeSelectionSet schema operation.rootType
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet))) ->
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
      Execution.executeSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet)) := by
    simp [executeRootSelectionSet, NormalForm.completeNormalizeOperation]
    rw [visitSubfields_completeNormalizeRootSelectionSet_runtime schema
      resolvers variableValues operation depth operation.rootType source
      runtimeCase operation.selectionSet (Execution.Response.object [])
      hruntime hagrees]
    rw [hbody]
  have hspec :
      Execution.executeRootSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        operation.rootType source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet)) := by
    simpa [Execution.executeSelectionSet,
      NormalForm.completeNormalizeOperation] using
      NormalForm.CompleteNormalization.executeSelectionSet_completeNormalizeRootSelectionSet_runtime
        schema resolvers variableValues operation depth operation.rootType
        source runtimeCase operation.selectionSet hruntime hagrees
  exact hungrouped.trans hspec.symm

theorem executeQueryAtDepth_completeNormalizeOperation_eq_spec_of_runtime_body
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef)
    (runtimeCase : NormalForm.BoolCase) :
    runtimeCase ∈
      NormalForm.allBoolCases (NormalForm.operationBoolVars operation) ->
    NormalForm.CompleteNormalization.variableValuesAgreeWithCase
      variableValues runtimeCase
      (NormalForm.operationBoolVars operation) ->
    visitSubfields schema resolvers variableValues depth operation.rootType
        source
        (NormalForm.normalizeSelectionSet schema operation.rootType
          (NormalForm.filterSelectionSetBoolCase runtimeCase
            operation.selectionSet))
        (Execution.Response.object [])
      =
      Execution.Response.object
        (Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (NormalForm.normalizeSelectionSet schema operation.rootType
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet))) ->
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
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
    schema operation resolvers variableValues depth source runtimeCase
    hruntime hagrees
  have hfilteredFree :
      NormalForm.selectionSetDirectiveFree
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet) :=
    NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
      schema runtimeCase operation.selectionSet
  exact visitSubfields_eq_spec_of_generatedNormalFields schema resolvers
    variableValues hschema depth operation.rootType source
    (NormalForm.normalizeSelectionSet schema operation.rootType
      (NormalForm.filterSelectionSetBoolCase runtimeCase
        operation.selectionSet))
    (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
      schema operation.rootType
      (NormalForm.filterSelectionSetBoolCase runtimeCase
        operation.selectionSet))
    (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
      schema operation.rootType
      (NormalForm.filterSelectionSetBoolCase runtimeCase
        operation.selectionSet) hfilteredFree)
    (NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal
      schema hschema operation.rootType
      (NormalForm.filterSelectionSetBoolCase runtimeCase
        operation.selectionSet))
    (by
      intro responseName fieldName arguments directives childSelectionSet hmem
      exact normalizeSelectionSet_field_child_generated schema
        operation.rootType
        (NormalForm.filterSelectionSetBoolCase runtimeCase
          operation.selectionSet)
        responseName fieldName arguments directives childSelectionSet
        hfilteredFree hmem)

theorem specExecution_eq_ungroupedExecution_of_completeNormalizeOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
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

theorem executeQueryAtDepth_completeNormalizeOperation_depth_zero
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (source : Execution.Value ObjectRef) :
      executeQueryAtDepth schema resolvers variableValues operation 0 source
        =
      executeQueryAtDepth schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) 0 source := by
  unfold executeQueryAtDepth
  rw [NormalForm.CompleteNormalization.completeNormalizeOperation_rootSourceAppliesBool]
  cases hroot : Execution.rootSourceAppliesBool schema operation source
  · simp
  · simp [executeRootSelectionSet,
      visitSubfields_depth_zero schema resolvers variableValues]

theorem executeQueryAtDepth_completeNormalizeOperation_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
    NormalForm.CompleteNormalization.completeNormalizationSemanticsPreserved
      schema operation hschema hvalid resolvers variableValues depth source
      hcomplete
  exact hcompleteUngrouped.trans hcompleteSpec.symm

theorem completeNormalizationPreservesUngroupedExecutionSemantics
    (schema : Schema) (operation : Operation) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues depth (source : Execution.Value ObjectRef),
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

theorem completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
    (depth : Nat) (source : Execution.Value ObjectRef)
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
    (depth : Nat) (source : Execution.Value ObjectRef)
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
        hroot hcollect hflat hcollected hcompatible happend)
      hschema hvalid hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef)
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
    (depth : Nat) (source : Execution.Value ObjectRef)
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
    (depth : Nat) (source : Execution.Value ObjectRef)
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
    (depth : Nat) (source : Execution.Value ObjectRef)
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
    (depth : Nat) (source : Execution.Value ObjectRef)
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
    (depth : Nat) (source : Execution.Value ObjectRef)
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
        variableValues depth (source : Execution.Value ObjectRef),
        NormalForm.operationBoolVarsComplete operation variableValues ->
          executeQueryAtDepth schema resolvers variableValues operation
              depth source
            =
          executeQueryAtDepth schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth
            source)
      ↔
      (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
        variableValues depth (source : Execution.Value ObjectRef),
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
      variableValues depth (source : Execution.Value ObjectRef),
      NormalForm.operationBoolVarsComplete operation variableValues ->
        executeQueryAtDepth schema resolvers variableValues operation
            depth source
          =
        Execution.executeQueryAtDepth schema resolvers variableValues operation
          depth source) ->
      ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
        variableValues depth (source : Execution.Value ObjectRef),
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
    (depth : Nat) (source : Execution.Value ObjectRef) :
    SchemaWellFormedness.schemaWellFormed schema ->
    Validation.operationDefinitionValid schema operation ->
    NormalForm.operationBoolVarsComplete operation variableValues ->
    NormalForm.selectionsAllFields operation.selectionSet ->
    NormalForm.operationDirectiveFree operation ->
    NormalForm.operationNormal schema operation ->
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
  intro hschema hvalid hcomplete hall hfree hnormal hchildren
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete
  exact executeQueryAtDepth_eq_spec_of_generatedNormalOperation schema
    operation resolvers variableValues depth source hschema hall hfree hnormal
    hchildren

theorem completeNormalizationPreservesUngroupedExecution_of_normalizeOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
    (depth : Nat) (source : Execution.Value ObjectRef) :
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
    NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation
      schema operation hschema hvalid hfree resolvers variableValues depth
      source
  exact hcompleteUngrouped.trans hgroundSpec.symm

end ExecutionUngrouped
end Algorithms

end GraphQL
