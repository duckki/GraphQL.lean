import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection
import GraphQL.Execution.ResolverValue

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

local instance : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem mergeResponseField_null_of_lookup_null
    (responseName : Name) :
    ∀ fields : List (Name × ResponseValue),
      lookupResponseField? responseName fields = some .null ->
        mergeResponseField responseName .null fields = fields
  | [], hlookup => by
      simp [lookupResponseField?] at hlookup
  | (fieldResponseName, response) :: rest, hlookup => by
      by_cases h : fieldResponseName == responseName
      · simp [lookupResponseField?, h] at hlookup
        subst response
        simp [mergeResponseField, mergeResponse, h]
      · simp [lookupResponseField?, mergeResponseField, h] at hlookup ⊢
        exact mergeResponseField_null_of_lookup_null responseName rest hlookup

theorem responseObjectField?_append_singleton_null_of_not_mem
    (responseName : Name) :
    ∀ fields : List (Name × ResponseValue),
      responseName ∉ fields.map Prod.fst ->
        responseObjectField? responseName
            (.object (fields ++ [(responseName, .null)])) =
          some .null
  | [], _hfresh => by
      simp [responseObjectField?, lookupResponseField?]
  | (fieldResponseName, response) :: rest, hfresh => by
      have hhead : (fieldResponseName == responseName) = false := by
        cases h : fieldResponseName == responseName
        · exact rfl
        · exfalso
          exact hfresh (by simp [beq_iff_eq.mp h])
      have hrest : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hfresh (by simp [hmem])
      have htail :
          lookupResponseField? responseName
              (rest ++ [(responseName, .null)]) =
            some .null := by
        simpa [responseObjectField?] using
          responseObjectField?_append_singleton_null_of_not_mem responseName
            rest hrest
      simp [responseObjectField?, lookupResponseField?, hhead, htail]

def groupedFieldVisitResult (responseName : Name) :
    Result (List (Name × ResponseValue)) -> ResponseValue × VisitStatus
  | .error errors => (.object [(responseName, .null)], .error errors)
  | .ok (fields, errors) => (.object fields, visitOk errors)

def ExecutableFieldsMergedRaw
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (_resolved : Option (ResolverValue ObjectIdentity)) : Prop :=
  visitSubfields schema resolvers variableValues (depth + 1)
    parentType source (executableFieldSelections (field :: fields))
    (.object []) =
  groupedFieldVisitResult responseName
    (GraphQL.Execution.executeField schema resolvers variableValues
      (depth + 1) source responseName (field :: fields))

theorem ExecutableFieldsMergedResponse_of_raw
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity)) :
    ExecutableFieldsMergedRaw schema resolvers variableValues depth
      parentType source responseName field fields resolved ->
    ExecutableFieldsMergedResponse schema resolvers variableValues depth
      parentType source responseName field fields resolved := by
  intro hraw
  unfold ExecutableFieldsMergedRaw at hraw
  unfold ExecutableFieldsMergedResponse executeRootSelectionSet
  rw [hraw]
  cases hspec :
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields) with
  | error errors =>
      simp [groupedFieldVisitResult]
  | ok result =>
      rcases result with ⟨completedFields, errors⟩
      simp [groupedFieldVisitResult, visitOk]

theorem mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult
    (responseName : Name) (completed : Result ResponseValue) :
    mergeResponseFieldResult responseName completed (.object []) =
      groupedFieldVisitResult responseName
        (GraphQL.Execution.singleFieldResult responseName completed) := by
  cases completed with
  | error errors =>
      simp [mergeResponseFieldResult, groupedFieldVisitResult,
        GraphQL.Execution.singleFieldResult, resultValueOrNull, resultStatus,
        mergeResponseFieldIntoObject, mergeResponseField]
  | ok result =>
      rcases result with ⟨value, errors⟩
      simp [mergeResponseFieldResult, groupedFieldVisitResult,
        GraphQL.Execution.singleFieldResult, resultValueOrNull, resultStatus,
        mergeResponseFieldIntoObject, mergeResponseField, visitOk]

theorem groupedFieldVisitResult_singleFieldResult_combine_neutral
    (responseName : Name)
    (leftCompleted rightCompleted combinedCompleted : Result ResponseValue)
    (hright : resultStatus rightCompleted = visitOk)
    (hcombine :
      GraphQL.Execution.Result.combine mergeResponse leftCompleted
        rightCompleted = combinedCompleted) :
    let left :=
      groupedFieldVisitResult responseName
        (GraphQL.Execution.singleFieldResult responseName leftCompleted)
    let right := mergeResponseFieldResult responseName rightCompleted left.fst
    (right.fst, combineVisitStatus left.snd right.snd) =
      groupedFieldVisitResult responseName
        (GraphQL.Execution.singleFieldResult responseName
          combinedCompleted) := by
  cases leftCompleted with
  | error prefixErrors =>
      cases rightCompleted with
      | error laterErrors =>
          simp [resultStatus, visitOk] at hright
      | ok laterResult =>
          rcases laterResult with ⟨laterValue, laterErrors⟩
          cases laterErrors with
          | zero =>
              cases hcombine
              cases laterValue <;> dsimp <;> simp [groupedFieldVisitResult,
                GraphQL.Execution.singleFieldResult,
                mergeResponseFieldResult, mergeResponseFieldIntoObject,
                mergeResponseField, mergeResponse, resultValueOrNull, resultStatus,
                combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, visitOk]
          | succ laterErrors =>
              simp [resultStatus, visitOk] at hright
  | ok prefixResult =>
      rcases prefixResult with ⟨prefixValue, prefixErrors⟩
      cases rightCompleted with
      | error laterErrors =>
          simp [resultStatus, visitOk] at hright
      | ok laterResult =>
          rcases laterResult with ⟨laterValue, laterErrors⟩
          cases laterErrors with
          | zero =>
              cases hcombine
              dsimp
              simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]
          | succ laterErrors =>
              simp [resultStatus, visitOk] at hright

theorem completeValue_object_append_eq_visitSubfields_append_result
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : Option ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true) :
    completeValue schema resolvers variableValues (childDepth + 1)
      (.named parentType) (firstSelectionSet ++ secondSelectionSet)
      (.object runtimeType identity) none =
    let firstResult :=
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) firstSelectionSet (.object [])
    let secondResult :=
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) secondSelectionSet firstResult.fst
    catchVisitBubbleAsNull secondResult.fst
      (combineVisitStatus firstResult.snd secondResult.snd) := by
  simp [completeValue, hincludes, reuseOrCreateObject?]
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    childDepth runtimeType (.object runtimeType identity) firstSelectionSet
    secondSelectionSet (.object [])]

def VisitSubfieldsErrorNeutral
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (current : ResponseValue) : Prop :=
  (visitSubfields schema resolvers variableValues depth parentType source
    selectionSet current).snd = visitOk

theorem resultValueOrNull_nonNullCompletion
    (completed : Result ResponseValue) :
    resultValueOrNull (nonNullCompletion completed) =
      resultValueOrNull completed := by
  cases completed with
  | error errors =>
      simp [nonNullCompletion, resultValueOrNull]
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;> cases errors <;>
        simp [nonNullCompletion, resultValueOrNull]

theorem resultStatus_nonNullCompletion_eq_ok_of_status_eq_ok_of_nonNull
    (completed : Result ResponseValue)
    (hstatus : resultStatus completed = visitOk)
    (hnonNull : resultValueOrNull completed ≠ .null) :
    resultStatus (nonNullCompletion completed) = visitOk := by
  cases completed with
  | error errors =>
      simp [resultStatus, visitOk] at hstatus
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;> cases errors <;>
        simp [resultStatus, visitOk, resultValueOrNull, nonNullCompletion]
          at hstatus hnonNull ⊢

theorem resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (inner : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    (hstatus :
      resultStatus
        (completeResolvedValue schema resolvers variableValues depth inner
          selectionSet resolved previous?) =
      visitOk)
    (hnonNull :
      resultValueOrNull
        (completeResolvedValue schema resolvers variableValues depth inner
          selectionSet resolved previous?) ≠
      .null) :
    resultStatus
      (completeResolvedValue schema resolvers variableValues depth
        (.nonNull inner) selectionSet resolved previous?) =
    visitOk := by
  cases hreuse :
      reusablePreviousValue? schema (.nonNull inner) previous? with
  | some previous =>
      simp [completeResolvedValue, hreuse, resultStatus, visitOk]
  | none =>
      simpa [completeResolvedValue, hreuse] using
        resultStatus_nonNullCompletion_eq_ok_of_status_eq_ok_of_nonNull
          (completeResolvedValue schema resolvers variableValues depth inner
            selectionSet resolved previous?)
          hstatus hnonNull

theorem resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (inner : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    (hnonNull :
      resultValueOrNull
        (completeResolvedValue schema resolvers variableValues depth inner
          selectionSet resolved previous?) ≠
      .null) :
    resultValueOrNull
      (completeResolvedValue schema resolvers variableValues depth
        (.nonNull inner) selectionSet resolved previous?) ≠
    .null := by
  cases hinner :
      completeResolvedValue schema resolvers variableValues depth inner
        selectionSet resolved previous? with
  | error errors =>
      simp [resultValueOrNull, hinner] at hnonNull
  | ok result =>
      rcases result with ⟨value, errors⟩
      have hvalue : value ≠ .null := by
        intro hnull
        exact hnonNull (by
          simp [resultValueOrNull, hinner, hnull])
      have hwrapped :=
        completeResolvedValue_nonNull_ok_of_inner_ok
          schema resolvers variableValues depth inner selectionSet resolved
          previous? value errors hinner hvalue
      simpa [resultValueOrNull, hwrapped] using hvalue

mutual
  theorem specCompleteValue_eq_of_no_object
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) :
      ∀ (depth : Nat) (fieldType : TypeRef)
        (fields otherFields : List ExecutableField)
        (resolved : ResolverValue ObjectIdentity),
        fieldType.isCompositeBool schema = false ->
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth fieldType fields resolved =
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth fieldType otherFields resolved
    | 0, fieldType, fields, otherFields, resolved, _hno => by
        simp [GraphQL.Execution.completeValue]
    | depth + 1, .named typeName, fields, otherFields, resolved, hno => by
        cases resolved with
        | null =>
            simp [GraphQL.Execution.completeValue]
        | scalar value =>
            simp [GraphQL.Execution.completeValue]
        | object runtimeType identity =>
            have hincludes :
                schema.typeIncludesObjectBool typeName runtimeType = false := by
              cases hlookup : schema.lookupType typeName with
              | none =>
                  simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
                    hlookup]
              | some typeDefinition =>
                  cases typeDefinition <;>
                    simp [TypeRef.isCompositeBool, TypeRef.namedType,
                      Schema.typeIncludesObjectBool,
                      Schema.getPossibleTypes, hlookup] at hno ⊢
            simp [GraphQL.Execution.completeValue, hincludes]
        | list values =>
            simp [GraphQL.Execution.completeValue]
    | depth + 1, .list inner, fields, otherFields, resolved, hno => by
        cases resolved with
        | null =>
            simp [GraphQL.Execution.completeValue]
        | scalar value =>
            simp [GraphQL.Execution.completeValue]
        | object runtimeType identity =>
            simp [GraphQL.Execution.completeValue]
        | list values =>
            have hinner :
                inner.isCompositeBool schema = false := by
              simpa [TypeRef.isCompositeBool] using hno
            have hlist :=
              specCompleteValueList_eq_of_no_object schema resolvers
                variableValues depth inner fields otherFields values hinner
            simp [GraphQL.Execution.completeValue, hlist]
    | depth + 1, .nonNull inner, fields, otherFields, resolved, hno => by
        have hinner :
            inner.isCompositeBool schema = false := by
          simpa [TypeRef.isCompositeBool] using hno
        have hvalue :=
          specCompleteValue_eq_of_no_object schema resolvers variableValues
            (depth + 1) inner fields otherFields resolved hinner
        simp [GraphQL.Execution.completeValue, hvalue]
  termination_by depth fieldType _fields _otherFields resolved _hno =>
    (depth, 0, sizeOf fieldType, sizeOf resolved)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem specCompleteValueList_eq_of_no_object
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) :
      ∀ (depth : Nat) (itemType : TypeRef)
        (fields otherFields : List ExecutableField)
        (values : List (ResolverValue ObjectIdentity)),
        itemType.isCompositeBool schema = false ->
          GraphQL.Execution.completeValueList schema resolvers variableValues
            depth itemType fields values =
          GraphQL.Execution.completeValueList schema resolvers variableValues
            depth itemType otherFields values
    | depth, itemType, fields, otherFields, [], _hno => by
        simp [GraphQL.Execution.completeValueList]
    | depth, itemType, fields, otherFields, value :: values, hno => by
        have hhead :=
          specCompleteValue_eq_of_no_object schema resolvers variableValues
            depth itemType fields otherFields value hno
        have htail :=
          specCompleteValueList_eq_of_no_object schema resolvers variableValues
            depth itemType fields otherFields values hno
        simp [GraphQL.Execution.completeValueList, hhead, htail]
  termination_by depth itemType _fields _otherFields values _hno =>
    (depth, 1, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

theorem resultValueOrNull_catchVisitBubbleAsNull
    (value : ResponseValue) (status : VisitStatus) :
    resultValueOrNull (catchVisitBubbleAsNull value status) =
      match status with
      | .error _errors => .null
      | .ok _result => value := by
  cases status with
  | error errors =>
      simp [catchVisitBubbleAsNull, resultValueOrNull]
  | ok result =>
      rcases result with ⟨unitValue, errors⟩
      cases unitValue
      simp [catchVisitBubbleAsNull, resultValueOrNull]

theorem completeValue_object_append_result_of_absorbs_errorNeutral
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : Option ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true)
    (habsorbs :
      ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) firstSelectionSet (.object []))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) secondSelectionSet
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) firstSelectionSet (.object [])).fst))
    (herrors :
      VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
        runtimeType (.object runtimeType identity) secondSelectionSet
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) firstSelectionSet (.object [])).fst) :
    let first :=
        completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) firstSelectionSet (.object runtimeType identity)
          none
    GraphQL.Execution.Result.combine mergeResponse first
        (completeResolvedValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) secondSelectionSet (.object runtimeType identity)
          (some (resultValueOrNull first))) =
      completeValue schema resolvers variableValues (childDepth + 1)
        (.named parentType) (firstSelectionSet ++ secondSelectionSet)
        (.object runtimeType identity) none := by
  rw [completeValue_object_append_eq_visitSubfields_append_result schema
    resolvers variableValues childDepth parentType runtimeType identity
    firstSelectionSet secondSelectionSet hincludes]
  unfold ResponseAbsorbs at habsorbs
  unfold VisitSubfieldsErrorNeutral at herrors
  have hparentComposite :
      (TypeRef.named parentType).isCompositeBool schema = true := by
    cases hlookup : schema.lookupType parentType with
    | none =>
        simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
          at hincludes
    | some typeDefinition =>
        cases typeDefinition <;>
          simp [TypeRef.isCompositeBool, TypeRef.namedType,
            Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
            at hincludes ⊢
  cases hfirst :
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) firstSelectionSet (.object []) with
  | mk firstOutput firstStatus =>
      cases hsecond :
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) secondSelectionSet firstOutput with
      | mk secondOutput secondStatus =>
          simp [hfirst, hsecond] at habsorbs herrors
          cases firstStatus with
          | error firstErrors =>
              simp [completeResolvedValue_previous_null, completeValue, reuseOrCreateObject?, hincludes, hfirst, resultValueOrNull, hsecond, herrors, catchVisitBubbleAsNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk, mergeResponse]
          | ok firstStatusResult =>
              rcases firstStatusResult with ⟨unitValue, firstErrors⟩
              cases unitValue
              obtain ⟨firstFields, hfirstFields⟩ :=
                visitSubfields_preserves_object schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  firstSelectionSet []
              rw [hfirst] at hfirstFields
              simp at hfirstFields
              subst firstOutput
              simp [completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateObject?, hincludes, hparentComposite, hfirst, resultValueOrNull, hsecond, herrors, habsorbs, catchVisitBubbleAsNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]

theorem resultStatus_completeValue_object_append_second_of_errorNeutral
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : Option ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes :
      schema.typeIncludesObjectBool parentType runtimeType = true)
    (herrors :
      VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
        runtimeType (.object runtimeType identity) secondSelectionSet
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) firstSelectionSet (.object [])).fst) :
    let first :=
        completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) firstSelectionSet (.object runtimeType identity)
          none
    resultStatus
        (completeResolvedValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) secondSelectionSet (.object runtimeType identity)
          (some (resultValueOrNull first))) =
      visitOk := by
  unfold VisitSubfieldsErrorNeutral at herrors
  have hparentComposite :
      (TypeRef.named parentType).isCompositeBool schema = true := by
    cases hlookup : schema.lookupType parentType with
    | none =>
        simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
          at hincludes
    | some typeDefinition =>
        cases typeDefinition <;>
          simp [TypeRef.isCompositeBool, TypeRef.namedType,
            Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
            at hincludes ⊢
  cases hfirst :
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) firstSelectionSet (.object []) with
  | mk firstOutput firstStatus =>
      simp [hfirst] at herrors
      cases firstStatus with
      | error firstErrors =>
          simp [completeResolvedValue_previous_null, completeValue, reuseOrCreateObject?, hincludes, hfirst, resultValueOrNull, catchVisitBubbleAsNull, resultStatus, visitOk]
      | ok firstStatusResult =>
          rcases firstStatusResult with ⟨unitValue, firstErrors⟩
          cases unitValue
          obtain ⟨firstFields, hfirstFields⟩ :=
            visitSubfields_preserves_object schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              firstSelectionSet []
          rw [hfirst] at hfirstFields
          simp at hfirstFields
          subst firstOutput
          simp [completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateObject?, hincludes, hparentComposite, hfirst, resultValueOrNull, catchVisitBubbleAsNull, herrors, resultStatus, visitOk]

theorem completeValue_named_group_append_one_result_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet prefixFields }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (prefixFields ++ [later]) }
              initial := .object [] }) :
    GraphQL.Execution.Result.combine mergeResponse
      (GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved)
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some (resultValueOrNull
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              (.named parentType) prefixFields resolved)))) =
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      (.named parentType) (prefixFields ++ [later]) resolved := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues prefixFields depth parentType resolved hprefixChildren
  have hextended :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved
      hchildren
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine]
  | succ childDepth =>
      cases resolved with
      | null =>
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse]
      | scalar value =>
            by_cases hcomposite :
                (TypeRef.named parentType).isCompositeBool schema = true
            · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, hcomposite]
            · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, hcomposite]
      | list values =>
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hslice :
                GraphQL.Execution.Result.combine mergeResponse
                    (completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                      (.object runtimeType identity) none)
                  (completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull
                        (completeValue schema resolvers variableValues
                          (childDepth + 1) (.named parentType)
                          (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                          (.object runtimeType identity) none)))) =
                completeValue schema resolvers variableValues (childDepth + 1)
                    (.named parentType)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (prefixFields ++ [later]))
                    (.object runtimeType identity) none := by
              calc
                GraphQL.Execution.Result.combine mergeResponse
                      (completeValue schema resolvers variableValues
                        (childDepth + 1) (.named parentType)
                        (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                        (.object runtimeType identity) none)
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                        (some (resultValueOrNull
                          (completeValue schema resolvers variableValues
                            (childDepth + 1) (.named parentType)
                            (GraphQL.Execution.mergedFieldSelectionSet
                              prefixFields)
                            (.object runtimeType identity) none)))) =
                  completeValue schema resolvers variableValues (childDepth + 1)
                      (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
                        later.selectionSet)
                      (.object runtimeType identity) none := by
                    exact
                      completeValue_object_append_result_of_absorbs_errorNeutral
                        schema resolvers variableValues childDepth parentType
                        runtimeType identity
                        (GraphQL.Execution.mergedFieldSelectionSet
                          prefixFields)
                        later.selectionSet hincludes
                        (hobjects childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth))
                        (herrors childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth))
                _ =
                  completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet
                        (prefixFields ++ [later]))
                      (.object runtimeType identity) none := by
                    rw [hmergedAppend]
            rw [← hprefix]
            rw [← hextended]
            exact hslice
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, hnotIncludes, resultValueOrNull, GraphQL.Execution.Result.combine, completeResolvedValue_previous_null]

theorem resultStatus_completeValue_named_group_append_second_eq_ok
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet prefixFields }
              initial := .object [] })
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))) :
    resultStatus
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some (resultValueOrNull
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              (.named parentType) prefixFields resolved)))) =
      visitOk := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues prefixFields depth parentType resolved hprefixChildren
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk, hcomposite]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, resultStatus, visitOk, hcomposite]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hrightLocal :=
              resultStatus_completeValue_object_append_second_of_errorNeutral
                schema resolvers variableValues childDepth parentType
                runtimeType identity
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                later.selectionSet hincludes
                (herrors childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth))
            dsimp at hrightLocal
            rw [hprefix] at hrightLocal
            exact hrightLocal
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, resultStatus, visitOk]

theorem completeValue_named_group_append_one_result_eq_spec_of_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet prefixFields }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (prefixFields ++ [later]) }
              initial := .object [] }) :
    GraphQL.Execution.Result.combine mergeResponse
      (GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved)
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some (resultValueOrNull
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              (.named parentType) prefixFields resolved)))) =
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      (.named parentType) (prefixFields ++ [later]) resolved := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues prefixFields depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hprefixChildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  have hextended :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hchildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, hcomposite]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, hcomposite]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hslice :
                GraphQL.Execution.Result.combine mergeResponse
                    (completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                      (.object runtimeType identity) none)
                  (completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull
                        (completeValue schema resolvers variableValues
                          (childDepth + 1) (.named parentType)
                          (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                          (.object runtimeType identity) none)))) =
                completeValue schema resolvers variableValues (childDepth + 1)
                    (.named parentType)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (prefixFields ++ [later]))
                    (.object runtimeType identity) none := by
              calc
                GraphQL.Execution.Result.combine mergeResponse
                      (completeValue schema resolvers variableValues
                        (childDepth + 1) (.named parentType)
                        (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                        (.object runtimeType identity) none)
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                        (some (resultValueOrNull
                          (completeValue schema resolvers variableValues
                            (childDepth + 1) (.named parentType)
                            (GraphQL.Execution.mergedFieldSelectionSet
                              prefixFields)
                            (.object runtimeType identity) none)))) =
                  completeValue schema resolvers variableValues (childDepth + 1)
                      (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
                        later.selectionSet)
                      (.object runtimeType identity) none := by
                    exact
                      completeValue_object_append_result_of_absorbs_errorNeutral
                        schema resolvers variableValues childDepth parentType
                        runtimeType identity
                        (GraphQL.Execution.mergedFieldSelectionSet
                          prefixFields)
                        later.selectionSet hincludes
                        (hobjects childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth)
                          ValueContainsObject.here)
                        (herrors childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth)
                          ValueContainsObject.here)
                _ =
                  completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet
                        (prefixFields ++ [later]))
                      (.object runtimeType identity) none := by
                    rw [hmergedAppend]
            rw [← hprefix]
            rw [← hextended]
            exact hslice
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, GraphQL.Execution.Result.combine]

theorem resultStatus_completeValue_named_group_append_second_eq_ok_of_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool parentType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet prefixFields }
              initial := .object [] })
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))) :
    resultStatus
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some (resultValueOrNull
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              (.named parentType) prefixFields resolved)))) =
      visitOk := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues prefixFields depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hprefixChildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk, hcomposite]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, resultStatus, visitOk, hcomposite]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hrightLocal :=
              resultStatus_completeValue_object_append_second_of_errorNeutral
                schema resolvers variableValues childDepth parentType
                runtimeType identity
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                later.selectionSet hincludes
                (herrors childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth) ValueContainsObject.here)
            dsimp at hrightLocal
            rw [hprefix] at hrightLocal
            exact hrightLocal
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, resultStatus, visitOk]

theorem completeValueList_head_eq_completeResolvedValue_of_composite
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectIdentity) (previous : ResponseValue)
    (hitemComposite : itemType.isCompositeBool schema = true) :
    (match (some previous : Option ResponseValue) with
    | some .null => .ok (.null, 0)
    | _ =>
        completeValue schema resolvers variableValues depth itemType
          selectionSet value (some previous)) =
      completeResolvedValue schema resolvers variableValues depth itemType
        selectionSet value (some previous) := by
  induction itemType generalizing previous with
  | named typeName =>
      cases previous <;>
        unfold completeResolvedValue <;>
        simp [reusablePreviousValue?, hitemComposite]
  | list inner ih =>
      cases previous <;>
        unfold completeResolvedValue <;>
        simp [reusablePreviousValue?, hitemComposite]
  | nonNull inner ih =>
      have hinnerComposite : inner.isCompositeBool schema = true := by
        simpa [TypeRef.isCompositeBool] using hitemComposite
      cases previous with
      | null =>
          unfold completeResolvedValue
          simp [reusablePreviousValue?]
      | scalar previousValue =>
          cases depth with
          | zero =>
              have hinner :=
                ih (ResponseValue.scalar previousValue) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, outOfFuel,
                nonNullCompletion, ← hinner]
          | succ childDepth =>
              have hinner :=
                ih (ResponseValue.scalar previousValue) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, nonNullCompletion, ← hinner]
      | object fields =>
          cases depth with
          | zero =>
              have hinner := ih (ResponseValue.object fields) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, outOfFuel,
                nonNullCompletion, ← hinner]
          | succ childDepth =>
              have hinner := ih (ResponseValue.object fields) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, nonNullCompletion, ← hinner]
      | list values =>
          cases depth with
          | zero =>
              have hinner := ih (ResponseValue.list values) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, outOfFuel,
                nonNullCompletion, ← hinner]
          | succ childDepth =>
              have hinner := ih (ResponseValue.list values) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, nonNullCompletion, ← hinner]

theorem resultStatus_completeValueList_append_second_eq_ok_of_each
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (hitemComposite : itemType.isCompositeBool schema = true)
    (hstatus :
      ∀ value : ResolverValue ObjectIdentity,
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth itemType prefixFields value)))) =
          visitOk) :
    ∀ values : List (ResolverValue ObjectIdentity),
      match
        GraphQL.Execution.completeValueList schema resolvers variableValues
          depth itemType prefixFields values
      with
      | .error _errors => True
      | .ok (previousValues, _errors) =>
          resultStatus
            (completeValueList schema resolvers variableValues depth itemType
              later.selectionSet values previousValues) =
            visitOk := by
  intro values
  induction values with
  | nil =>
      simp [GraphQL.Execution.completeValueList, completeValueList,
        resultStatus, visitOk]
  | cons value rest ih =>
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have hheadStatus :
                  resultStatus
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value (some headValue)) =
                  visitOk := by
                simpa [hhead, resultValueOrNull] using hstatus value
              have htailStatus : resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                simpa [htail] using ih
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    .ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hstatusList :
                                  resultStatus
                                    (Result.combine List.cons
                                      (match
                                        (some headValue : Option ResponseValue)
                                      with
                                      | some .null =>
                                          Except.ok (ResponseValue.null, 0)
                                      | _ =>
                                          completeValue schema resolvers
                                            variableValues depth itemType
                                            later.selectionSet value
                                            (some headValue))
                                      (Except.ok (rightTailValues, 0))) =
                                    visitOk := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  resultStatus, visitOk]
                              simpa [GraphQL.Execution.completeValueList,
                                completeValueList, hhead, htail,
                                hrightTail, Result.combine,
                                GraphQL.Execution.Result.combine,
                                resultStatus, visitOk] using hstatusList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus
                  | succ rightHeadErrors =>
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus

theorem resultStatus_completeValueList_append_second_eq_ok_of_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField) :
    ∀ values : List (ResolverValue ObjectIdentity),
      itemType.isCompositeBool schema = true ->
      (∀ value,
        value ∈ values ->
          resultStatus
              (completeResolvedValue schema resolvers variableValues depth itemType
                later.selectionSet value
                (some (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers variableValues
                    depth itemType prefixFields value)))) =
            visitOk) ->
      match
        GraphQL.Execution.completeValueList schema resolvers variableValues
          depth itemType prefixFields values
      with
      | .error _errors => True
      | .ok (previousValues, _errors) =>
          resultStatus
            (completeValueList schema resolvers variableValues depth itemType
              later.selectionSet values previousValues) =
            visitOk
  | [], _hitemComposite, _hstatus => by
      simp [GraphQL.Execution.completeValueList, completeValueList,
        resultStatus, visitOk]
  | value :: rest, hitemComposite, hstatus => by
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have hheadStatus :
                  resultStatus
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value (some headValue)) =
                  visitOk := by
                simpa [hhead, resultValueOrNull] using
                  hstatus value (by simp)
              have htailStatus : resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                have htailStatusRaw :=
                  resultStatus_completeValueList_append_second_eq_ok_of_mem
                    schema resolvers variableValues depth itemType prefixFields
                    later rest hitemComposite
                    (by
                      intro restValue hmem
                      exact hstatus restValue (by simp [hmem]))
                simpa [htail] using htailStatusRaw
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    .ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hstatusList :
                                  resultStatus
                                    (Result.combine List.cons
                                      (match
                                        (some headValue : Option ResponseValue)
                                      with
                                      | some .null =>
                                          Except.ok (ResponseValue.null, 0)
                                      | _ =>
                                          completeValue schema resolvers
                                            variableValues depth itemType
                                            later.selectionSet value
                                            (some headValue))
                                      (Except.ok (rightTailValues, 0))) =
                                    visitOk := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  resultStatus, visitOk]
                              simpa [GraphQL.Execution.completeValueList,
                                completeValueList, hhead, htail,
                                hrightTail, Result.combine,
                                GraphQL.Execution.Result.combine,
                                resultStatus, visitOk] using hstatusList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus
                  | succ rightHeadErrors =>
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus

theorem completeValueList_append_result_eq_spec_of_each
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (hitemComposite : itemType.isCompositeBool schema = true)
    (happend :
      ∀ value : ResolverValue ObjectIdentity,
        GraphQL.Execution.Result.combine mergeResponse
          (GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value)
          (completeResolvedValue schema resolvers variableValues depth itemType
            later.selectionSet value
            (some (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues
                depth itemType prefixFields value)))) =
        GraphQL.Execution.completeValue schema resolvers variableValues
          depth itemType (prefixFields ++ [later]) value)
    (hstatus :
      ∀ value : ResolverValue ObjectIdentity,
        resultStatus
          (completeResolvedValue schema resolvers variableValues depth itemType
            later.selectionSet value
            (some (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues
                depth itemType prefixFields value)))) =
          visitOk) :
    ∀ values : List (ResolverValue ObjectIdentity),
      GraphQL.Execution.Result.combine mergeResponseLists
        (GraphQL.Execution.completeValueList schema resolvers variableValues
          depth itemType prefixFields values)
        (match
          GraphQL.Execution.completeValueList schema resolvers variableValues
            depth itemType prefixFields values
        with
        | .error _errors => .ok ([], 0)
        | .ok (previousValues, _errors) =>
            completeValueList schema resolvers variableValues depth itemType
              later.selectionSet values previousValues) =
      GraphQL.Execution.completeValueList schema resolvers variableValues
        depth itemType (prefixFields ++ [later]) values := by
  intro values
  induction values with
  | nil =>
      simp [GraphQL.Execution.completeValueList, completeValueList,
        GraphQL.Execution.Result.combine, mergeResponseLists]
  | cons value rest ih =>
      have hheadAppend := happend value
      have hheadStatus :
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth itemType prefixFields value)))) =
          visitOk :=
        hstatus value
      have hrestStatus :=
        resultStatus_completeValueList_append_second_eq_ok_of_each schema
          resolvers variableValues depth itemType prefixFields later
          hitemComposite hstatus rest
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          .error tailErrors := by
                        simpa [htail, GraphQL.Execution.Result.combine] using
                          ih.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          GraphQL.Execution.Result.combine mergeResponseLists
                            (.ok (tailValues, tailErrors))
                            (completeValueList schema resolvers variableValues
                              depth itemType later.selectionSet rest tailValues) := by
                        simpa [htail] using ih.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          have htailStatus' :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues depth itemType
                                  later.selectionSet rest tailValues) =
                              visitOk := by
                            simpa [htail] using hrestStatus
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              simp [GraphQL.Execution.completeValueList, hhead,
                                htail, hheadAppend', htailAppend',
                                hrightTail, Result.combine,
                                GraphQL.Execution.Result.combine]
                          | succ rightTailErrors =>
                              have htailStatus' :
                                  resultStatus
                                    (completeValueList schema resolvers
                                      variableValues depth itemType
                                      later.selectionSet rest tailValues) =
                                  visitOk := by
                                simpa [htail] using hrestStatus
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  .error tailErrors := by
                simpa [htail, GraphQL.Execution.Result.combine] using ih.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have htailStatus' :
                  resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                simpa [htail] using hrestStatus
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  GraphQL.Execution.Result.combine mergeResponseLists
                    (.ok (tailValues, tailErrors))
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) := by
                simpa [htail] using ih.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    Except.ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hcombinedList :
                                  GraphQL.Execution.Result.combine
                                      mergeResponseLists
                                      (Except.ok
                                        (headValue :: tailValues,
                                          headErrors + tailErrors))
                                      (Result.combine List.cons
                                        (match
                                          (some headValue : Option ResponseValue)
                                        with
                                        | some .null =>
                                            Except.ok (ResponseValue.null, 0)
                                        | _ =>
                                            completeValue schema resolvers
                                              variableValues depth itemType
                                              later.selectionSet value
                                              (some headValue))
                                        (Except.ok (rightTailValues, 0))) =
                                    Except.ok
                                      (mergeResponse headValue rightHeadValue ::
                                        mergeResponseLists tailValues
                                          rightTailValues,
                                        headErrors + tailErrors) := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  mergeResponseLists]
                              simpa [GraphQL.Execution.completeValueList,
                                completeValueList, hhead, htail, hrightTail,
                                hheadAppend', htailAppend', Result.combine,
                                GraphQL.Execution.Result.combine] using
                                hcombinedList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'

theorem completeValueList_append_result_eq_spec_of_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField) :
    ∀ values : List (ResolverValue ObjectIdentity),
      itemType.isCompositeBool schema = true ->
      (∀ value,
        value ∈ values ->
          GraphQL.Execution.Result.combine mergeResponse
            (GraphQL.Execution.completeValue schema resolvers variableValues
              depth itemType prefixFields value)
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth itemType prefixFields value)))) =
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType (prefixFields ++ [later]) value) ->
      (∀ value,
        value ∈ values ->
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth itemType prefixFields value)))) =
            visitOk) ->
      GraphQL.Execution.Result.combine mergeResponseLists
        (GraphQL.Execution.completeValueList schema resolvers variableValues
          depth itemType prefixFields values)
        (match
          GraphQL.Execution.completeValueList schema resolvers variableValues
            depth itemType prefixFields values
        with
        | .error _errors => .ok ([], 0)
        | .ok (previousValues, _errors) =>
            completeValueList schema resolvers variableValues depth itemType
              later.selectionSet values previousValues) =
      GraphQL.Execution.completeValueList schema resolvers variableValues
        depth itemType (prefixFields ++ [later]) values
  | [], _hitemComposite, _happend, _hstatus => by
      simp [GraphQL.Execution.completeValueList, completeValueList,
        GraphQL.Execution.Result.combine, mergeResponseLists]
  | value :: rest, hitemComposite, happend, hstatus => by
      have hheadAppend := happend value (by simp)
      have hheadStatus :
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth itemType prefixFields value)))) =
          visitOk :=
        hstatus value (by simp)
      have htailAppendAll :=
        completeValueList_append_result_eq_spec_of_mem schema resolvers
          variableValues depth itemType prefixFields later rest
          hitemComposite
          (by
            intro restValue hmem
            exact happend restValue (by simp [hmem]))
          (by
            intro restValue hmem
            exact hstatus restValue (by simp [hmem]))
      have hrestStatus :=
        resultStatus_completeValueList_append_second_eq_ok_of_mem schema
          resolvers variableValues depth itemType prefixFields later rest
          hitemComposite
          (by
            intro restValue hmem
            exact hstatus restValue (by simp [hmem]))
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          .error tailErrors := by
                        simpa [htail, GraphQL.Execution.Result.combine] using
                          htailAppendAll.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          GraphQL.Execution.Result.combine mergeResponseLists
                            (.ok (tailValues, tailErrors))
                            (completeValueList schema resolvers variableValues
                              depth itemType later.selectionSet rest tailValues) := by
                        simpa [htail] using htailAppendAll.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          have htailStatus' :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues depth itemType
                                  later.selectionSet rest tailValues) =
                              visitOk := by
                            simpa [htail] using hrestStatus
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              simp [GraphQL.Execution.completeValueList, hhead,
                                htail, hheadAppend', htailAppend',
                                hrightTail, Result.combine,
                                GraphQL.Execution.Result.combine]
                          | succ rightTailErrors =>
                              have htailStatus' :
                                  resultStatus
                                    (completeValueList schema resolvers
                                      variableValues depth itemType
                                      later.selectionSet rest tailValues) =
                                  visitOk := by
                                simpa [htail] using hrestStatus
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  .error tailErrors := by
                simpa [htail, GraphQL.Execution.Result.combine] using
                  htailAppendAll.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have htailStatus' :
                  resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                simpa [htail] using hrestStatus
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  GraphQL.Execution.Result.combine mergeResponseLists
                    (.ok (tailValues, tailErrors))
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) := by
                simpa [htail] using htailAppendAll.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    Except.ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hcombinedList :
                                  GraphQL.Execution.Result.combine
                                      mergeResponseLists
                                      (Except.ok
                                        (headValue :: tailValues,
                                          headErrors + tailErrors))
                                      (Result.combine List.cons
                                        (match
                                          (some headValue : Option ResponseValue)
                                        with
                                        | some .null =>
                                            Except.ok (ResponseValue.null, 0)
                                        | _ =>
                                            completeValue schema resolvers
                                              variableValues depth itemType
                                              later.selectionSet value
                                              (some headValue))
                                        (Except.ok (rightTailValues, 0))) =
                                    Except.ok
                                      (mergeResponse headValue rightHeadValue ::
                                        mergeResponseLists tailValues
                                          rightTailValues,
                                        headErrors + tailErrors) := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  mergeResponseLists]
                              simpa [GraphQL.Execution.completeValueList,
                                completeValueList, hhead, htail, hrightTail,
                                hheadAppend', htailAppend', Result.combine,
                                GraphQL.Execution.Result.combine] using
                                hcombinedList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'

theorem completeValue_group_append_one_result_eq_spec_and_status
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (fieldType : TypeRef) :
    ∀ (depth : Nat) (resolved : ResolverValue ObjectIdentity)
      (prefixFields : List ExecutableField) (later : ExecutableField),
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool fieldType.namedType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet prefixFields }
              initial := .object [] }) ->
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object [])))) ->
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          ValueContainsObject resolved runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))) ->
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool fieldType.namedType runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (prefixFields ++ [later]) }
              initial := .object [] }) ->
          GraphQL.Execution.Result.combine mergeResponse
            (GraphQL.Execution.completeValue schema resolvers variableValues
              depth fieldType prefixFields resolved)
            (completeResolvedValue schema resolvers variableValues depth fieldType
              later.selectionSet resolved
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldType prefixFields resolved)))) =
        GraphQL.Execution.completeValue schema resolvers variableValues depth
          fieldType (prefixFields ++ [later]) resolved
        ∧
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth fieldType
              later.selectionSet resolved
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldType prefixFields resolved)))) =
          visitOk ∧
        (resultValueOrNull
            (GraphQL.Execution.completeValue schema resolvers variableValues
              depth fieldType prefixFields resolved) ≠ .null ->
            resultValueOrNull
              (completeResolvedValue schema resolvers variableValues depth fieldType
                later.selectionSet resolved
                (some (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers
                  variableValues depth fieldType prefixFields resolved)))) ≠
            .null) := by
  induction fieldType with
  | named typeName =>
      intro depth resolved prefixFields later hprefixChildren hobjects herrors
        hchildren
      constructor
      · exact completeValue_named_group_append_one_result_eq_spec_of_contained schema
          resolvers variableValues depth typeName resolved prefixFields later
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hprefixChildren childDepth runtimeType identity hlt
              hcontains
              (by simpa using hincludes))
          hobjects herrors
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hchildren childDepth runtimeType identity hlt
              hcontains
              (by simpa using hincludes))
      · constructor
        · exact resultStatus_completeValue_named_group_append_second_eq_ok_of_contained
            schema resolvers variableValues depth typeName resolved prefixFields
            later
            (by
              intro childDepth runtimeType identity hlt hcontains hincludes
              exact hprefixChildren childDepth runtimeType identity hlt
                hcontains
                (by simpa using hincludes))
            herrors
        · intro hprefixNonNull
          cases depth with
          | zero =>
              cases resolved <;>
                simp [GraphQL.Execution.completeValue, outOfFuel,
                  resultValueOrNull] at hprefixNonNull
          | succ childDepth =>
              cases resolved with
              | null =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | scalar value =>
                  by_cases hcomposite :
                      (TypeRef.named typeName).isCompositeBool schema = true
                  · simp [GraphQL.Execution.completeValue, resultValueOrNull,
                      hcomposite] at hprefixNonNull
                  · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, hcomposite]
              | list values =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | object runtimeType identity =>
                  by_cases hincludes :
                      schema.typeIncludesObjectBool typeName runtimeType = true
                  · have hrightStatus :
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            (childDepth + 1) (.named typeName)
                            later.selectionSet (.object runtimeType identity)
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema
                                resolvers variableValues (childDepth + 1)
                                (.named typeName) prefixFields
                                (.object runtimeType identity))))) =
                        visitOk :=
                      resultStatus_completeValue_named_group_append_second_eq_ok_of_contained
                        schema resolvers variableValues (childDepth + 1)
                        typeName (.object runtimeType identity) prefixFields
                        later
                        (by
                          intro childDepth' runtimeType' identity' hlt
                            hcontains hincludes'
                          exact hprefixChildren childDepth' runtimeType'
                            identity' hlt hcontains
                            (by simpa using hincludes'))
                        herrors
                    cases hprevious :
                        resultValueOrNull
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues (childDepth + 1) (.named typeName)
                            prefixFields (.object runtimeType identity)) with
                    | null =>
                        exact False.elim (hprefixNonNull hprevious)
                    | scalar previousValue =>
                        cases hcompleted :
                            GraphQL.Execution.executeCollectedFields schema
                              resolvers variableValues childDepth
                              (.object runtimeType identity)
                              (GraphQL.Execution.collectFields schema
                                variableValues runtimeType
                                (.object runtimeType identity)
                                (GraphQL.Execution.mergedFieldSelectionSet
                                  prefixFields)) with
                        | error prefixErrors =>
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                        | ok prefixResult =>
                            rcases prefixResult with
                              ⟨prefixOutput, prefixErrors⟩
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                    | object previousFields =>
                        obtain ⟨outputFields, hvisited⟩ :=
                          visitSubfields_preserves_object schema resolvers
                            variableValues childDepth runtimeType
                            (.object runtimeType identity)
                            later.selectionSet previousFields
                        have hstatus' :
                            (visitSubfields schema resolvers variableValues
                              childDepth runtimeType
                              (.object runtimeType identity)
                              later.selectionSet
                              (.object previousFields)).snd =
                            visitOk := by
                          have hprefixEq :
                              completeValue schema resolvers variableValues
                                (childDepth + 1) (.named typeName)
                                  (GraphQL.Execution.mergedFieldSelectionSet
                                    prefixFields)
                                  (.object runtimeType identity) none =
                              GraphQL.Execution.completeValue schema resolvers
                                variableValues (childDepth + 1)
                                (.named typeName) prefixFields
                                (.object runtimeType identity) :=
                            completeValue_group_eq_spec_of_contained_child_states
                              schema resolvers variableValues prefixFields
                              (childDepth + 1) typeName
                              (.object runtimeType identity)
                              (by
                                intro childDepth' runtimeType' identity' hlt
                                  hcontains hincludes'
                                exact hprefixChildren childDepth' runtimeType'
                                  identity' hlt hcontains
                                  (by simpa using hincludes'))
                          have hprefixPrev :
                              resultValueOrNull
                                (completeValue schema resolvers variableValues
                                  (childDepth + 1) (.named typeName)
                                    (GraphQL.Execution.mergedFieldSelectionSet
                                      prefixFields)
                                    (.object runtimeType identity) none) =
                              .object previousFields := by
                            rw [hprefixEq]
                            exact hprevious
                          cases hfirst :
                              visitSubfields schema resolvers variableValues
                                childDepth runtimeType
                                (.object runtimeType identity)
                                (GraphQL.Execution.mergedFieldSelectionSet
                                  prefixFields)
                                (.object []) with
                          | mk firstOutput firstStatus =>
                              cases firstStatus with
                              | error firstErrors =>
                                  simp [completeValue, hincludes,
                                    reuseOrCreateObject?, hfirst,
                                    catchVisitBubbleAsNull, resultValueOrNull]
                                    at hprefixPrev
                              | ok firstStatusResult =>
                                  rcases firstStatusResult with
                                    ⟨unitValue, firstErrors⟩
                                  cases unitValue
                                  have hfirstOutput :
                                      firstOutput = .object previousFields := by
                                    simpa [completeValue, hincludes,
                                      reuseOrCreateObject?, hfirst,
                                      catchVisitBubbleAsNull,
                                      resultValueOrNull]
                                      using hprefixPrev
                                  have herrors' :=
                                    herrors childDepth runtimeType identity
                                      (Nat.lt_succ_self childDepth)
                                      ValueContainsObject.here
                                  unfold VisitSubfieldsErrorNeutral at herrors'
                                  simpa [hfirst, hfirstOutput] using herrors'
                        have hparentComposite :
                            (TypeRef.named typeName).isCompositeBool schema =
                              true := by
                          cases hlookup : schema.lookupType typeName with
                          | none =>
                              simp [Schema.typeIncludesObjectBool,
                                Schema.getPossibleTypes, hlookup] at hincludes
                          | some typeDefinition =>
                              cases typeDefinition <;>
                                simp [TypeRef.isCompositeBool,
                                  TypeRef.namedType,
                                  Schema.typeIncludesObjectBool,
                                  Schema.getPossibleTypes, hlookup]
                                  at hincludes ⊢
                        simp [completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateObject?, hincludes, hparentComposite, hvisited, hstatus', resultValueOrNull, catchVisitBubbleAsNull, visitOk]
                    | list previousValues =>
                        cases hcompleted :
                            GraphQL.Execution.executeCollectedFields schema
                              resolvers variableValues childDepth
                              (.object runtimeType identity)
                              (GraphQL.Execution.collectFields schema
                                variableValues runtimeType
                                (.object runtimeType identity)
                                (GraphQL.Execution.mergedFieldSelectionSet
                                  prefixFields)) with
                        | error prefixErrors =>
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                        | ok prefixResult =>
                            rcases prefixResult with
                              ⟨prefixOutput, prefixErrors⟩
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                  · have hnotIncludes :
                        schema.typeIncludesObjectBool typeName runtimeType =
                          false := by
                      cases h :
                          schema.typeIncludesObjectBool typeName runtimeType <;>
                        simp [h] at hincludes ⊢
                    simp [GraphQL.Execution.completeValue, hnotIncludes,
                      resultValueOrNull] at hprefixNonNull
  | list inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects herrors
        hchildren
      constructor
      · cases depth with
          | zero =>
            cases resolved <;>
              simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine]
          | succ childDepth =>
            cases resolved with
            | null =>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse]
            | scalar value =>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
            | object runtimeType identity =>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
            | list values =>
                have hvalueAppend :
                    ∀ value : ResolverValue ObjectIdentity,
                    value ∈ values ->
                      GraphQL.Execution.Result.combine mergeResponse
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner prefixFields value)
                        (completeResolvedValue schema resolvers variableValues
                          childDepth inner later.selectionSet value
                          (some (resultValueOrNull
                            (GraphQL.Execution.completeValue schema resolvers
                              variableValues childDepth inner prefixFields
                              value)))) =
                      GraphQL.Execution.completeValue schema resolvers
                        variableValues childDepth inner (prefixFields ++ [later])
                        value := by
                  intro value hmem
                  exact (ih childDepth value prefixFields later
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hprefixChildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact hobjects childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact herrors childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hchildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))).left
                have hvalueStatus :
                    ∀ value : ResolverValue ObjectIdentity,
                    value ∈ values ->
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues
                          childDepth inner later.selectionSet value
                          (some (resultValueOrNull
                            (GraphQL.Execution.completeValue schema resolvers
                              variableValues childDepth inner prefixFields
                          value)))) =
                        visitOk := by
                  intro value hmem
                  exact (ih childDepth value prefixFields later
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hprefixChildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact hobjects childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact herrors childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hchildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))).right.left
                cases hcontains : inner.isCompositeBool schema with
                | false =>
                    have happendedPrefix :
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner
                          (prefixFields ++ [later]) values =
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner prefixFields values :=
                      specCompleteValueList_eq_of_no_object schema resolvers
                        variableValues childDepth inner (prefixFields ++ [later])
                        prefixFields values hcontains
                    cases hprefixList :
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner prefixFields values with
                    | error prefixErrors =>
                        have happended :
                            GraphQL.Execution.completeValueList schema
                              resolvers variableValues childDepth inner
                              (prefixFields ++ [later]) values =
                            .error prefixErrors := by
                          rw [happendedPrefix, hprefixList]
                        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefixList, happended, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                    | ok prefixResult =>
                        rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                        have happended :
                            GraphQL.Execution.completeValueList schema
                              resolvers variableValues childDepth inner
                              (prefixFields ++ [later]) values =
                            .ok (prefixValues, prefixErrors) := by
                          rw [happendedPrefix, hprefixList]
                        have hprefixReady :
                            ∀ response, response ∈ prefixValues ->
                              ResponseMergeReady response :=
                          specCompleteValueList_values_ready schema resolvers
                            variableValues childDepth inner prefixFields values
                            prefixValues prefixErrors hprefixList
                        have hself :
                            mergeResponseLists prefixValues prefixValues =
                              prefixValues :=
                          mergeResponseLists_self_of_ready prefixValues
                            hprefixReady
                        have houterContains :
                            (TypeRef.list inner).isCompositeBool schema =
                              false := by
                          simpa [TypeRef.isCompositeBool,
                            TypeRef.namedType] using hcontains
                        simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, hprefixList, happended, houterContains, hself, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                | true =>
                    have hlistAppend :=
                      completeValueList_append_result_eq_spec_of_mem schema
                        resolvers variableValues childDepth inner prefixFields
                        later values hcontains hvalueAppend hvalueStatus
                    cases hprefixList :
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner prefixFields values with
                    | error prefixErrors =>
                        have happended :
                            GraphQL.Execution.completeValueList schema resolvers
                              variableValues childDepth inner
                              (prefixFields ++ [later]) values =
                            .error prefixErrors := by
                          have hcombined := hlistAppend
                          simp [hprefixList, GraphQL.Execution.Result.combine]
                            at hcombined
                          simpa using hcombined.symm
                        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefixList, happended, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                    | ok prefixResult =>
                        rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                        have hlistStatus :=
                          resultStatus_completeValueList_append_second_eq_ok_of_mem
                            schema resolvers variableValues childDepth inner
                            prefixFields later values hcontains hvalueStatus
                        have hrightStatus :
                            resultStatus
                              (completeValueList schema resolvers
                                variableValues childDepth inner
                                later.selectionSet values prefixValues) =
                            visitOk := by
                          simpa [hprefixList] using hlistStatus
                        cases hrightList :
                            completeValueList schema resolvers variableValues
                              childDepth inner later.selectionSet values
                              prefixValues with
                        | error rightErrors =>
                            simp [hrightList, resultStatus, visitOk]
                              at hrightStatus
                        | ok rightResult =>
                            rcases rightResult with ⟨rightValues, rightErrors⟩
                            cases rightErrors with
                            | zero =>
                                have happended :
                                    GraphQL.Execution.completeValueList schema
                                      resolvers variableValues childDepth inner
                                      (prefixFields ++ [later]) values =
                                    .ok (mergeResponseLists prefixValues
                                      rightValues, prefixErrors) := by
                                  simpa [hprefixList, hrightList,
                                    GraphQL.Execution.Result.combine]
                                    using hlistAppend.symm
                                have houterContains :
                                    (TypeRef.list inner).isCompositeBool
                                        schema =
                                      true := by
                                  simpa [TypeRef.isCompositeBool,
                                    TypeRef.namedType] using hcontains
                                simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateList?, hprefixList, hrightList, happended, resultValueOrNull, houterContains, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                            | succ rightErrors =>
                                simp [hrightList, resultStatus, visitOk]
                                  at hrightStatus
      · constructor
        · cases depth with
          | zero =>
              cases resolved <;>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk]
          | succ childDepth =>
              cases resolved with
              | null =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
              | scalar value =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
              | object runtimeType identity =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
              | list values =>
                  have hvalueStatus :
                      ∀ value : ResolverValue ObjectIdentity,
                      value ∈ values ->
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            childDepth inner later.selectionSet value
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema resolvers
                                variableValues childDepth inner prefixFields
                            value)))) =
                          visitOk := by
                    intro value hmem
                    exact (ih childDepth value prefixFields later
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hprefixChildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact hobjects childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact herrors childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hchildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))).right.left
                  cases hcontains : inner.isCompositeBool schema with
                  | false =>
                      have houterContains :
                          (TypeRef.list inner).isCompositeBool schema =
                            false := by
                        simpa [TypeRef.isCompositeBool,
                          TypeRef.namedType] using hcontains
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields
                            values <;>
                        simp [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, reusablePreviousValue?, houterContains, hprefixList, resultValueOrNull, resultStatus, visitOk, catchBubbleAsNull]
                  | true =>
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                      | error prefixErrors =>
                          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefixList, resultValueOrNull, resultStatus, visitOk, catchBubbleAsNull]
                      | ok prefixResult =>
                          rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                          have hlistStatus :=
                            resultStatus_completeValueList_append_second_eq_ok_of_mem
                              schema resolvers variableValues childDepth inner
                              prefixFields later values hcontains hvalueStatus
                          have hrightStatus :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues childDepth inner
                                  later.selectionSet values prefixValues) =
                              visitOk := by
                            simpa [hprefixList] using hlistStatus
                          cases hrightList :
                              completeValueList schema resolvers variableValues
                                childDepth inner later.selectionSet values
                                prefixValues with
                          | error rightErrors =>
                              simp [hrightList, resultStatus, visitOk]
                                at hrightStatus
                          | ok rightResult =>
                              rcases rightResult with
                                ⟨rightValues, rightErrors⟩
                              cases rightErrors with
                              | zero =>
                                  have houterContains :
                                      (TypeRef.list inner).isCompositeBool
                                          schema =
                                        true := by
                                    simpa [TypeRef.isCompositeBool,
                                      TypeRef.namedType] using hcontains
                                  simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateList?, houterContains, hprefixList, hrightList, resultValueOrNull, resultStatus, visitOk, catchBubbleAsNull]
                              | succ rightErrors =>
                                  simp [hrightList, resultStatus, visitOk]
                                    at hrightStatus
        · intro hprefixNonNull
          cases depth with
          | zero =>
              cases resolved <;>
                simp [GraphQL.Execution.completeValue, outOfFuel,
                  resultValueOrNull] at hprefixNonNull
          | succ childDepth =>
              cases resolved with
              | null =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | scalar value =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | object runtimeType identity =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | list values =>
                  have hvalueStatus :
                      ∀ value : ResolverValue ObjectIdentity,
                      value ∈ values ->
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            childDepth inner later.selectionSet value
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema resolvers
                                variableValues childDepth inner prefixFields
                            value)))) =
                          visitOk := by
                    intro value hmem
                    exact (ih childDepth value prefixFields later
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hprefixChildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact hobjects childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact herrors childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hchildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))).right.left
                  cases hcontains : inner.isCompositeBool schema with
                  | false =>
                      have houterContains :
                          (TypeRef.list inner).isCompositeBool schema =
                            false := by
                        simpa [TypeRef.isCompositeBool,
                          TypeRef.namedType] using hcontains
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields
                            values with
                      | error prefixErrors =>
                          simp [GraphQL.Execution.completeValue, hprefixList, resultValueOrNull, catchBubbleAsNull]
                            at hprefixNonNull
                      | ok prefixResult =>
                          rcases prefixResult with
                            ⟨prefixValues, prefixErrors⟩
                          simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, houterContains, hprefixList, resultValueOrNull, catchBubbleAsNull]
                  | true =>
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                      | error prefixErrors =>
                          simp [GraphQL.Execution.completeValue, hprefixList, resultValueOrNull, catchBubbleAsNull]
                            at hprefixNonNull
                      | ok prefixResult =>
                          rcases prefixResult with
                            ⟨prefixValues, prefixErrors⟩
                          have hlistStatus :=
                            resultStatus_completeValueList_append_second_eq_ok_of_mem
                              schema resolvers variableValues childDepth inner
                              prefixFields later values hcontains hvalueStatus
                          have hrightStatus :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues childDepth inner
                                  later.selectionSet values prefixValues) =
                              visitOk := by
                            simpa [hprefixList] using hlistStatus
                          cases hrightList :
                              completeValueList schema resolvers variableValues
                                childDepth inner later.selectionSet values
                                prefixValues with
                          | error rightErrors =>
                              simp [hrightList, resultStatus, visitOk]
                                at hrightStatus
                          | ok rightResult =>
                              rcases rightResult with
                                ⟨rightValues, rightErrors⟩
                              cases rightErrors with
                              | zero =>
                                  have houterContains :
                                      (TypeRef.list inner).isCompositeBool
                                          schema =
                                        true := by
                                    simpa [TypeRef.isCompositeBool,
                                      TypeRef.namedType] using hcontains
                                  simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateList?, houterContains, hprefixList, hrightList, resultValueOrNull, catchBubbleAsNull]
                              | succ rightErrors =>
                                  simp [hrightList, resultStatus, visitOk]
                                    at hrightStatus
  | nonNull inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects herrors
        hchildren
      cases depth with
      | zero =>
            constructor <;>
              cases resolved <;>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk, GraphQL.Execution.Result.combine]
      | succ depth =>
          have hinner :=
            ih (depth + 1) resolved prefixFields later
              (by
                intro childDepth runtimeType identity hlt hcontains hincludes
                exact hprefixChildren childDepth runtimeType identity hlt
                  hcontains
                  (by simpa using hincludes))
              hobjects herrors
              (by
                intro childDepth runtimeType identity hlt hcontains hincludes
                exact hchildren childDepth runtimeType identity hlt
                  hcontains
                  (by simpa using hincludes))
          rcases hinner with ⟨hcombine, hstatus, hnonnull⟩
          constructor
          · cases hprefix :
              GraphQL.Execution.completeValue schema resolvers variableValues
                (depth + 1) inner prefixFields resolved with
            | error prefixErrors =>
                cases hright :
                    completeResolvedValue schema resolvers variableValues
                      (depth + 1) inner later.selectionSet resolved
                      (some (resultValueOrNull
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues (depth + 1) inner prefixFields
                          resolved))) with
                | error rightErrors =>
                    have hrightStatus :
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            (depth + 1) inner later.selectionSet resolved
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema
                                resolvers variableValues (depth + 1) inner
                                prefixFields resolved)))) =
                        visitOk := hstatus
                    simp [hright, resultStatus, visitOk] at hrightStatus
                | ok rightResult =>
                    rcases rightResult with ⟨rightValue, rightErrors⟩
                    cases rightErrors with
                    | zero =>
                        have hright' :
                            completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some .null) =
                            .ok (rightValue, 0) := by
                          simpa [hprefix, resultValueOrNull,
                            completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar, reusablePreviousValue?]
                            using hright
                        have happended :
                            GraphQL.Execution.completeValue schema resolvers
                              variableValues (depth + 1) inner
                              (prefixFields ++ [later]) resolved =
                            .error prefixErrors := by
                          have hcombined := hcombine
                          simp [hprefix, hright', resultValueOrNull,
                            GraphQL.Execution.Result.combine] at hcombined
                          simpa using hcombined.symm
                        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine]
                    | succ rightErrors =>
                        have hrightStatus :
                            resultStatus
                              (completeResolvedValue schema resolvers variableValues
                                (depth + 1) inner later.selectionSet resolved
                                (some (resultValueOrNull
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (depth + 1)
                                    inner prefixFields resolved)))) =
                            visitOk := hstatus
                        simp [hright, resultStatus, visitOk] at hrightStatus
            | ok prefixResult =>
                rcases prefixResult with ⟨prefixValue, prefixErrors⟩
                cases hright :
                    completeResolvedValue schema resolvers variableValues
                      (depth + 1) inner later.selectionSet resolved
                      (some (resultValueOrNull
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues (depth + 1) inner prefixFields
                          resolved))) with
                | error rightErrors =>
                    have hrightStatus :
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            (depth + 1) inner later.selectionSet resolved
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema
                                resolvers variableValues (depth + 1) inner
                                prefixFields resolved)))) =
                        visitOk := hstatus
                    simp [hright, resultStatus, visitOk] at hrightStatus
                | ok rightResult =>
                    rcases rightResult with ⟨rightValue, rightErrors⟩
                    cases rightErrors with
                    | zero =>
                        have hright' :
                            completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some prefixValue) =
                            .ok (rightValue, 0) := by
                          simpa [hprefix, resultValueOrNull,
                            completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar, reusablePreviousValue?]
                            using hright
                        have happended :
                            GraphQL.Execution.completeValue schema resolvers
                              variableValues (depth + 1) inner
                              (prefixFields ++ [later]) resolved =
                            .ok (mergeResponse prefixValue rightValue,
                              prefixErrors) := by
                          have hcombined := hcombine
                          simp [hprefix, hright', resultValueOrNull,
                            GraphQL.Execution.Result.combine] at hcombined
                          simpa using hcombined.symm
                        cases prefixValue with
                        | null =>
                            cases rightValue <;>
                                simp [completeResolvedValue_previous_null] at hright'
                            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                        | scalar prefixScalar =>
                            have hrightNonNullRaw :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues (depth + 1)
                                        inner prefixFields resolved)))) ≠
                                .null :=
                              hnonnull (by
                                simp [hprefix, resultValueOrNull])
                            have hrightNonNull :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved (some (.scalar prefixScalar))) ≠
                                .null :=
                              by
                                simpa [hprefix, resultValueOrNull]
                                  using hrightNonNullRaw
                            have hwrapped :
                                completeResolvedValue schema resolvers variableValues
                                  (depth + 1) inner.nonNull later.selectionSet
                                  resolved (some (.scalar prefixScalar)) =
                                .ok (rightValue, 0) :=
                              have hrightValueNonNull : rightValue ≠ .null := by
                                intro hnull
                                exact hrightNonNull (by
                                  simp [hright', hnull, resultValueOrNull])
                              completeResolvedValue_nonNull_ok_of_inner_ok
                                schema resolvers variableValues (depth + 1)
                                inner later.selectionSet resolved
                                (some (.scalar prefixScalar)) rightValue 0
                                hright' hrightValueNonNull
                            cases rightValue with
                            | null =>
                                exact False.elim (by
                                  have hrightValueNonNull : ResponseValue.null ≠ .null := by
                                    intro hnull
                                    exact hrightNonNull (by
                                      simp [hright', resultValueOrNull])
                                  exact hrightValueNonNull rfl)
                            | scalar rightScalar =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | object rightFields =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | list rightValues =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                        | object prefixFieldsValue =>
                            have hrightNonNullRaw :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues (depth + 1)
                                        inner prefixFields resolved)))) ≠
                                .null :=
                              hnonnull (by
                                simp [hprefix, resultValueOrNull])
                            have hrightNonNull :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved (some (.object prefixFieldsValue))) ≠
                                .null :=
                              by
                                simpa [hprefix, resultValueOrNull]
                                  using hrightNonNullRaw
                            have hwrapped :
                                completeResolvedValue schema resolvers variableValues
                                  (depth + 1) inner.nonNull later.selectionSet
                                  resolved (some (.object prefixFieldsValue)) =
                                .ok (rightValue, 0) :=
                              have hrightValueNonNull : rightValue ≠ .null := by
                                intro hnull
                                exact hrightNonNull (by
                                  simp [hright', hnull, resultValueOrNull])
                              completeResolvedValue_nonNull_ok_of_inner_ok
                                schema resolvers variableValues (depth + 1)
                                inner later.selectionSet resolved
                                (some (.object prefixFieldsValue)) rightValue 0
                                hright' hrightValueNonNull
                            cases rightValue with
                            | null =>
                                exact False.elim (by
                                  have hrightValueNonNull : ResponseValue.null ≠ .null := by
                                    intro hnull
                                    exact hrightNonNull (by
                                      simp [hright', resultValueOrNull])
                                  exact hrightValueNonNull rfl)
                            | scalar rightScalar =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | object rightFields =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | list rightValues =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                        | list prefixValues =>
                            have hrightNonNullRaw :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues (depth + 1)
                                        inner prefixFields resolved)))) ≠
                                .null :=
                              hnonnull (by
                                simp [hprefix, resultValueOrNull])
                            have hrightNonNull :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved (some (.list prefixValues))) ≠
                                .null :=
                              by
                                simpa [hprefix, resultValueOrNull]
                                  using hrightNonNullRaw
                            have hwrapped :
                                completeResolvedValue schema resolvers variableValues
                                  (depth + 1) inner.nonNull later.selectionSet
                                  resolved (some (.list prefixValues)) =
                                .ok (rightValue, 0) :=
                              have hrightValueNonNull : rightValue ≠ .null := by
                                intro hnull
                                exact hrightNonNull (by
                                  simp [hright', hnull, resultValueOrNull])
                              completeResolvedValue_nonNull_ok_of_inner_ok
                                schema resolvers variableValues (depth + 1)
                                inner later.selectionSet resolved
                                (some (.list prefixValues)) rightValue 0
                                hright' hrightValueNonNull
                            cases rightValue with
                            | null =>
                                exact False.elim (by
                                  have hrightValueNonNull : ResponseValue.null ≠ .null := by
                                    intro hnull
                                    exact hrightNonNull (by
                                      simp [hright', resultValueOrNull])
                                  exact hrightValueNonNull rfl)
                            | scalar rightScalar =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | object rightFields =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | list rightValues =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                    | succ rightErrors =>
                        have hrightStatus :
                            resultStatus
                              (completeResolvedValue schema resolvers variableValues
                                (depth + 1) inner later.selectionSet resolved
                                (some (resultValueOrNull
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (depth + 1)
                                    inner prefixFields resolved)))) =
                            visitOk := hstatus
                        simp [hright, resultStatus, visitOk] at hrightStatus
          · constructor
            · cases hprefix :
                GraphQL.Execution.completeValue schema resolvers variableValues
                  (depth + 1) inner prefixFields resolved with
              | error prefixErrors =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, resultValueOrNull, resultStatus, nonNullCompletion, visitOk]
              | ok prefixResult =>
                  rcases prefixResult with ⟨prefixValue, prefixErrors⟩
                  cases prefixValue with
                  | null =>
                      simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, resultValueOrNull, resultStatus, nonNullCompletion, visitOk]
                  | scalar prefixScalar =>
                      have hrightStatus :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.scalar prefixScalar))) =
                          visitOk := by
                        simpa [hprefix, resultValueOrNull] using hstatus
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.scalar prefixScalar))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion, resultStatus, visitOk]
                        using
                          resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.scalar prefixScalar))
                            hrightStatus hrightNonNull
                  | object prefixFieldsValue =>
                      have hrightStatus :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.object prefixFieldsValue))) =
                          visitOk := by
                        simpa [hprefix, resultValueOrNull] using hstatus
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.object prefixFieldsValue))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using
                          resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.object prefixFieldsValue))
                            hrightStatus hrightNonNull
                  | list prefixValues =>
                      have hrightStatus :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.list prefixValues))) =
                          visitOk := by
                        simpa [hprefix, resultValueOrNull] using hstatus
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.list prefixValues))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using
                          resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.list prefixValues))
                            hrightStatus hrightNonNull
            · intro hprefixNonNull
              cases hprefix :
                  GraphQL.Execution.completeValue schema resolvers variableValues
                    (depth + 1) inner prefixFields resolved with
              | error prefixErrors =>
                  simp [GraphQL.Execution.completeValue, hprefix, resultValueOrNull, nonNullCompletion]
                    at hprefixNonNull
              | ok prefixResult =>
                  rcases prefixResult with ⟨prefixValue, prefixErrors⟩
                  cases prefixValue with
                  | null =>
                      simp [GraphQL.Execution.completeValue, hprefix, resultValueOrNull, nonNullCompletion]
                        at hprefixNonNull
                  | scalar prefixScalar =>
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.scalar prefixScalar))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      have hproject :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner.nonNull later.selectionSet
                              resolved (some (.scalar prefixScalar))) ≠
                          .null := by
                        exact
                          resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.scalar prefixScalar)) hrightNonNull
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using hproject
                  | object prefixFieldsValue =>
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.object prefixFieldsValue))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      have hproject :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner.nonNull later.selectionSet
                              resolved (some (.object prefixFieldsValue))) ≠
                          .null := by
                        exact
                          resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.object prefixFieldsValue)) hrightNonNull
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using hproject
                  | list prefixValues =>
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.list prefixValues))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      have hproject :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner.nonNull later.selectionSet
                              resolved (some (.list prefixValues))) ≠
                          .null := by
                        exact
                          resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.list prefixValues)) hrightNonNull
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using hproject

theorem resultValueOrNull_executeField_depth_zero_none
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) :
    resultValueOrNull
      (executeField schema resolvers variableValues 0 source none field) =
    .null := by
  cases hlookup : schema.lookupField field.parentType field.fieldName with
      | none =>
          simp [executeField, hlookup, resultValueOrNull]
      | some fieldDefinition =>
          cases hresolve :
              resolvers.resolve field.parentType field.fieldName field.arguments
                source with
          | none =>
              rcases fieldDefinition with ⟨fdName, fdOutput, fdArgs⟩
              cases fdOutput <;>
                simp [executeField, hlookup, hresolve, reusablePreviousValue?, handleFieldError, resultValueOrNull]
          | some resolved =>
              simp [executeField, hlookup, hresolve, reusablePreviousValue?, completeValue, outOfFuel, resultValueOrNull]

theorem visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] }) :
    visitSubfields schema resolvers variableValues (depth + 1) parentType
      source (executableFieldSelections [field]) (.object []) =
    groupedFieldVisitResult responseName
      (GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field]) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      dsimp at hfieldResponse hfieldParent hresolve hchildren ⊢
      subst fieldResponseName
      subst fieldParent
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
      | some fieldDefinition =>
          cases resolved with
          | none =>
              simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
          | some resolvedValue =>
              have hcomplete :
                  completeValue schema resolvers variableValues depth
                    fieldDefinition.outputType selectionSet resolvedValue
                    none =
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth fieldDefinition.outputType
                    [executableField parentType responseName fieldName arguments
                      selectionSet]
                    resolvedValue :=
                completeValue_single_field_eq_spec_of_guarded_child_states
                  schema resolvers variableValues
                  (executableField parentType responseName fieldName arguments
                    selectionSet)
                  fieldDefinition.outputType depth resolvedValue
                  (by
                    intro childDepth runtimeType identity hlt hincludes
                    exact hchildren childDepth runtimeType identity hlt
                      (by
                        simpa [Schema.fieldReturnType?, hlookup] using
                          hincludes))
              rw [show
                  executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet }] =
                    [executableFieldSelection
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet }] by
                rfl]
              simp [visitSubfields, visitSelection, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult, hcomplete]

theorem visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] }) :
    visitSubfields schema resolvers variableValues (depth + 1) parentType
      source (executableFieldSelections [field]) (.object []) =
    groupedFieldVisitResult responseName
      (GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field]) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      dsimp at hfieldResponse hfieldParent hresolve hchildren ⊢
      subst fieldResponseName
      subst fieldParent
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
      | some fieldDefinition =>
          cases resolved with
          | none =>
              simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
          | some resolvedValue =>
              have hcomplete :
                    completeValue schema resolvers variableValues depth
                      fieldDefinition.outputType selectionSet resolvedValue
                      none =
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth fieldDefinition.outputType
                    [executableField parentType responseName fieldName arguments
                      selectionSet]
                    resolvedValue :=
                completeValue_single_field_eq_spec_of_contained_child_states
                  schema resolvers variableValues
                  (executableField parentType responseName fieldName arguments
                    selectionSet)
                  fieldDefinition.outputType depth resolvedValue
                  (by
                    intro childDepth runtimeType identity hlt hcontains
                      hincludes
                    exact hchildren childDepth runtimeType identity hlt
                      hcontains
                      (by
                        simpa [Schema.fieldReturnType?, hlookup] using
                          hincludes))
              rw [show
                  executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet }] =
                    [executableFieldSelection
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet }] by
                rfl]
              simp [visitSubfields, visitSelection, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult, hcomplete]

theorem ExecutableFieldsMergedRaw_single_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] }) :
    ExecutableFieldsMergedRaw schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedRaw
  simpa using
    visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_guarded_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedRaw_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hchildren :
      ∀ childDepth runtimeType (identity : Option ObjectIdentity),
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] }) :
    ExecutableFieldsMergedRaw schema resolvers variableValues depth
      parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedRaw
  simpa using
    visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_contained_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem visitSubfields_executableFieldSelections_existing_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) :
    ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
      (∀ field, field ∈ fields -> field.responseName = responseName) ->
      (∀ field, field ∈ fields ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition) ->
      responseObjectField? responseName (.object outputFields) = some .null ->
        visitSubfields schema resolvers variableValues (depth + 1)
          parentType source
          (executableFieldSelections fields) (.object outputFields) =
        (.object outputFields, visitOk)
  | [], outputFields, _hresponse, _hlookups, _hlookup => by
      simp [visitSubfields, executableFieldSelections, visitOk]
  | field :: rest, outputFields, hresponse, hlookups, hlookup => by
      have hfieldResponse : field.responseName = responseName :=
        hresponse field (by simp)
      rcases hlookups field (by simp) with ⟨fieldDefinition, hfieldLookup⟩
      have hrestResponse :
          ∀ restField, restField ∈ rest ->
            restField.responseName = responseName := by
        intro restField hmem
        exact hresponse restField (by simp [hmem])
      have hrestLookups :
          ∀ restField, restField ∈ rest ->
            ∃ fieldDefinition, schema.lookupField parentType
              restField.fieldName = some fieldDefinition := by
        intro restField hmem
        exact hlookups restField (by simp [hmem])
      have hmerge :
          mergeResponseField responseName .null outputFields = outputFields :=
        mergeResponseField_null_of_lookup_null responseName outputFields
          (by simpa [responseObjectField?] using hlookup)
      have hhead :
          visitSelection schema resolvers variableValues (depth + 1)
            parentType source
            (executableFieldSelection field) (.object outputFields) =
          (.object outputFields, visitOk) := by
        cases field with
        | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
            dsimp [executableFieldSelection] at hfieldResponse hfieldLookup ⊢
            subst fieldResponseName
            simp [visitSelection, selectionDirectivesAllowBool_empty, hlookup, executeField, executableField, hfieldLookup, reusablePreviousValue?_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, hmerge, resultValueOrNull, resultStatus, visitOk]
      have hrest :=
        visitSubfields_executableFieldSelections_existing_null schema
          resolvers variableValues depth parentType source responseName rest
          outputFields hrestResponse hrestLookups hlookup
      rw [show executableFieldSelections (field :: rest) =
          executableFieldSelection field :: executableFieldSelections rest by
        rfl]
      simp [visitSubfields, hhead, hrest]

theorem visitSubfields_executableFieldSelections_completion_zero_same_response_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (rest : List ExecutableField)
    (outputFields : List (Name × ResponseValue))
    (hresponse :
      ∀ candidate, candidate ∈ field :: rest ->
        candidate.responseName = responseName)
    (hrestLookups :
      ∀ candidate, candidate ∈ rest ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition)
    (hfresh : responseName ∉ outputFields.map Prod.fst) :
    visitSubfields schema resolvers variableValues 1 parentType source
      (executableFieldSelections (field :: rest)) (.object outputFields) =
    let fieldResult :=
      executeField schema resolvers variableValues 0 source none
        (executableField parentType responseName field.fieldName field.arguments
          field.selectionSet)
    (.object (outputFields ++ [(responseName, .null)]),
      resultStatus fieldResult) := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hrestResponse :
      ∀ restField, restField ∈ rest ->
        restField.responseName = responseName := by
    intro restField hmem
    exact hresponse restField (by simp [hmem])
  let fieldResult :=
    executeField schema resolvers variableValues 0 source none
      (executableField parentType responseName field.fieldName field.arguments
        field.selectionSet)
  have hlookupFresh :
      responseObjectField? responseName (.object outputFields) = none :=
    responseObjectField?_none_of_not_mem responseName outputFields hfresh
  have hvalueNull : resultValueOrNull fieldResult = .null := by
    dsimp [fieldResult]
    exact
      resultValueOrNull_executeField_depth_zero_none schema resolvers variableValues
        source
        (executableField parentType responseName field.fieldName field.arguments
          field.selectionSet)
  have hmerge :
      mergeResponseField responseName (resultValueOrNull fieldResult)
          outputFields =
        outputFields ++ [(responseName, .null)] := by
    rw [hvalueNull]
    exact mergeResponseField_of_not_mem responseName .null outputFields hfresh
  have hhead :
      visitSelection schema resolvers variableValues 1 parentType source
        (executableFieldSelection field) (.object outputFields) =
      (.object (outputFields ++ [(responseName, .null)]),
        resultStatus fieldResult) := by
    cases field with
    | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
        dsimp [executableFieldSelection] at hfieldResponse ⊢
        subst fieldResponseName
        have hmerge' :
            mergeResponseField responseName
                (resultValueOrNull
                    (executeField schema resolvers variableValues 0 source
                      none
                    { parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet }))
                outputFields =
              outputFields ++ [(responseName, .null)] := by
          simpa [fieldResult, executableField] using hmerge
        dsimp [fieldResult]
        simp [visitSelection, selectionDirectivesAllowBool_empty, hlookupFresh, mergeResponseFieldResult, mergeResponseFieldIntoObject, hmerge', executableField]
  have hlookupNull :
      responseObjectField? responseName
          (.object (outputFields ++ [(responseName, .null)])) =
        some .null :=
    responseObjectField?_append_singleton_null_of_not_mem responseName
      outputFields hfresh
  have hrest :=
    visitSubfields_executableFieldSelections_existing_null schema resolvers
      variableValues 0 parentType source responseName rest
      (outputFields ++ [(responseName, .null)]) hrestResponse hrestLookups
      hlookupNull
  rw [show executableFieldSelections (field :: rest) =
      executableFieldSelection field :: executableFieldSelections rest by
    rfl]
  simp [visitSubfields, hhead, hrest, fieldResult]

theorem completeValue_previous_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (selectionSet : List Selection) (value : ResolverValue ObjectIdentity) :
    completeValue schema resolvers variableValues (fuel + 1) fieldType selectionSet
      value (some .null) = .ok (.null, 0) := by
  simp [completeValue]

theorem visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (resolvedValue : ResolverValue ObjectIdentity) (previous : ResponseValue)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hresolve :
      resolvers.resolve parentType fieldName arguments source =
        some resolvedValue) :
    visitSubfields schema resolvers variableValues (completionDepth + 1 + 1)
      parentType source
      (executableFieldSelections
        [{ parentType := parentType
           responseName := responseName
           fieldName := fieldName
           arguments := arguments
           selectionSet := selectionSet }])
      (.object [(responseName, previous)]) =
    mergeResponseFieldResult responseName
      (completeResolvedValue schema resolvers variableValues (completionDepth + 1)
        fieldDefinition.outputType selectionSet resolvedValue (some previous))
      (.object [(responseName, previous)]) := by
  have hexec :
      executeField schema resolvers variableValues (completionDepth + 1)
          source (some previous)
          { parentType := parentType
            responseName := responseName
            fieldName := fieldName
            arguments := arguments
            selectionSet := selectionSet } =
      completeResolvedValue schema resolvers variableValues (completionDepth + 1)
        fieldDefinition.outputType selectionSet resolvedValue (some previous) :=
    executeField_resolved_eq_completeResolvedValue schema resolvers
      variableValues completionDepth source
      { parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := selectionSet }
      fieldDefinition resolvedValue previous hlookup hresolve
  cases previous with
  | null =>
      simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk, combineVisitStatus, GraphQL.Execution.Result.combine, hexec]
  | scalar value =>
      cases hcomplete :
          completeResolvedValue schema resolvers variableValues
            (completionDepth + 1) fieldDefinition.outputType selectionSet
            resolvedValue (some (ResponseValue.scalar value)) with
      | error errors =>
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, resultStatus, visitOk, combineVisitStatus, GraphQL.Execution.Result.combine, hexec, hcomplete]
      | ok completeResult =>
          rcases completeResult with ⟨completeValue, completeErrors⟩
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, resultStatus, visitOk, combineVisitStatus, GraphQL.Execution.Result.combine, hexec, hcomplete]
  | object fields =>
      simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, hexec]
  | list values =>
      simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, hexec]

theorem ExecutableFieldsMergedRaw_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hprefixResponses :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups :
      ∀ candidate, candidate ∈ fields ++ [later] ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition)
    (hresolveFirst :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ValueContainsObject resolved runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object [])))
    (hchildren :
        ∀ childDepth runtimeType identity,
          childDepth < depth ->
          ValueContainsObject resolved runtimeType identity ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            runtimeType = true ->
            ExecutionStateEquivalent
              { window :=
                { schema := schema
                  resolvers := resolvers
                  variableValues := variableValues
                  depth := childDepth
                  parentType := runtimeType
                  source := .object runtimeType identity
                  selectionSet :=
                    GraphQL.Execution.mergedFieldSelectionSet
                      ((field :: fields) ++ [later]) }
                initial := .object [] }) :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
    unfold ExecutableFieldsMergedRaw at hprefixRaw ⊢
    cases depth with
    | zero =>
        have hextendedResponses :
            ∀ candidate, candidate ∈ field :: (fields ++ [later]) ->
              candidate.responseName = responseName := by
          intro candidate hmem
          simp at hmem
          rcases hmem with hhead | htail
          · subst candidate
            exact hfieldResponse
          · rcases htail with hprefix | hlater
            · exact hprefixResponses candidate (by simp [hprefix])
            · subst candidate
              exact hlaterResponse
        have hextendedVisit :
            visitSubfields schema resolvers variableValues 1 parentType source
              (executableFieldSelections (field :: (fields ++ [later])))
              (.object []) =
            let fieldResult :=
              executeField schema resolvers variableValues 0 source none
                (executableField parentType responseName field.fieldName
                  field.arguments field.selectionSet)
            (.object [(responseName, .null)], resultStatus fieldResult) :=
          visitSubfields_executableFieldSelections_completion_zero_same_response_fresh
            schema resolvers variableValues parentType source responseName field
            (fields ++ [later]) [] hextendedResponses htailLookups (by simp)
        rw [hextendedVisit]
        cases field with
        | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
            dsimp at hfieldResponse hfieldParent hresolveFirst ⊢
            subst fieldResponseName
            subst fieldParent
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [GraphQL.Execution.executeField, executeField, groupedFieldVisitResult, executableField, hlookup, resultStatus]
            | some fieldDefinition =>
                cases resolved with
                | none =>
                    cases fieldDefinition with
                    | mk definitionName outputType definitionArguments =>
                        cases outputType <;>
                          simp [GraphQL.Execution.executeField, executeField, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, executableField, hlookup, hresolveFirst, reusablePreviousValue?, handleFieldError, resultStatus, visitOk]
                | some resolvedValue =>
                    simp [GraphQL.Execution.executeField, executeField, GraphQL.Execution.completeValue, completeValue, outOfFuel, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, executableField, hlookup, hresolveFirst, reusablePreviousValue?, resultStatus]
    | succ childDepth =>
        cases field with
        | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
            cases later with
            | mk laterParent laterResponseName laterFieldName laterArguments
                laterSelectionSet =>
                dsimp at hfieldResponse hlaterResponse hfieldParent
                dsimp at hlaterParent hfieldName hresolveFirst hresolveLater
                dsimp at hprefixResponses hprefixChildren hobjects herrors
                dsimp at hchildren hprefixRaw ⊢
                subst fieldResponseName
                subst laterResponseName
                subst fieldParent
                subst laterParent
                subst laterFieldName
                have hselectionAppend :
                    executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          (fields ++
                            [{ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := laterArguments
                               selectionSet := laterSelectionSet }])) =
                    executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields) ++
                    executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := laterArguments
                         selectionSet := laterSelectionSet }] := by
                  simp [executableFieldSelections]
                rw [hselectionAppend]
                rw [visitSubfields_append_equivalence schema resolvers
                  variableValues (childDepth + 2) parentType source
                  (executableFieldSelections
                    ({ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := arguments
                       selectionSet := selectionSet } ::
                      fields))
                  (executableFieldSelections
                    [{ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := laterArguments
                       selectionSet := laterSelectionSet }])
                  (.object [])]
                rw [hprefixRaw]
                have hlaterResponseAll :
                    ∀ (candidate : ExecutableField),
                      candidate ∈
                          ([{ parentType := parentType
                              responseName := responseName
                              fieldName := fieldName
                              arguments := laterArguments
                              selectionSet := laterSelectionSet }] :
                            List ExecutableField) ->
                        candidate.responseName = responseName := by
                  intro candidate hmem
                  simp at hmem
                  subst candidate
                  rfl
                have htailNull :
                    visitSubfields schema resolvers variableValues
                      (childDepth + 2) parentType source
                      (executableFieldSelections
                        [{ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := laterArguments
                           selectionSet := laterSelectionSet }])
                      (.object [(responseName, .null)]) =
                    (.object [(responseName, .null)], visitOk) :=
                  visitSubfields_executableFieldSelections_existing_null
                    schema resolvers variableValues (childDepth + 1)
                    parentType source responseName
                    [{ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := laterArguments
                       selectionSet := laterSelectionSet }]
                    [(responseName, .null)] hlaterResponseAll
                    (by
                      intro candidate hmem
                      simp at hmem
                      subst candidate
                      exact htailLookups
                        { parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := laterArguments
                          selectionSet := laterSelectionSet }
                        (by simp))
                    (by simp [responseObjectField?, lookupResponseField?])
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [GraphQL.Execution.executeField, hlookup, groupedFieldVisitResult, htailNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]
                | some fieldDefinition =>
                    cases resolved with
                    | none =>
                        cases fieldDefinition with
                        | mk definitionName outputType definitionArguments =>
                            cases outputType <;>
                              simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, handleFieldError, htailNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]
                    | some resolvedValue =>
                        cases fieldDefinition with
                        | mk definitionName outputType definitionArguments =>
                            cases outputType with
                            | named typeName =>
                                cases resolvedValue with
                                | null =>
                                    simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk, GraphQL.Execution.completeValue, htailNull]
                                | scalar value =>
                                    by_cases hcomposite :
                                        (TypeRef.named typeName).isCompositeBool
                                            schema =
                                          true
                                    · simp [GraphQL.Execution.executeField, visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, executableField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, resultStatus, visitOk, GraphQL.Execution.completeValue, reusablePreviousValue?, hcomposite]
                                    · simp [GraphQL.Execution.executeField, visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, executableField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, resultStatus, visitOk, GraphQL.Execution.completeValue, reusablePreviousValue?, hcomposite]
                                | object runtimeType identity =>
                                    have hspecAppend :
                                        GraphQL.Execution.Result.combine
                                          mergeResponse
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.named typeName)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            (.object runtimeType identity))
                                          (completeResolvedValue schema resolvers
                                            variableValues (childDepth + 1)
                                            (.named typeName)
                                            laterSelectionSet
                                            (.object runtimeType identity)
                                            (some (resultValueOrNull
                                              (GraphQL.Execution.completeValue
                                                schema resolvers variableValues
                                                (childDepth + 1)
                                                (.named typeName)
                                                ({ parentType := parentType
                                                   responseName := responseName
                                                   fieldName := fieldName
                                                   arguments := arguments
                                                   selectionSet := selectionSet } ::
                                                  fields)
                                                (.object runtimeType identity))))) =
                                        GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.named typeName)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            (fields ++
                                              [{ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := laterArguments
                                                 selectionSet :=
                                                   laterSelectionSet }]))
                                          (.object runtimeType identity) :=
                                      completeValue_named_group_append_one_result_eq_spec_of_contained
                                        schema resolvers variableValues
                                        (childDepth + 1) typeName
                                        (.object runtimeType identity)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        { parentType := parentType
                                          responseName := responseName
                                          fieldName := fieldName
                                          arguments := laterArguments
                                          selectionSet := laterSelectionSet }
                                        (by
                                          intro childDepth' runtimeType' identity'
                                            hlt hcontains hincludes
                                          exact hprefixChildren childDepth'
                                            runtimeType' identity' hlt
                                            (by simpa [resolvedValueOrNull] using
                                              hcontains)
                                            (by
                                              simpa [Schema.fieldReturnType?,
                                                hlookup] using hincludes))
                                        (by
                                          intro childDepth' runtimeType' identity'
                                            hlt hcontains
                                          exact hobjects childDepth'
                                            runtimeType' identity' hlt
                                            (by simpa [resolvedValueOrNull] using
                                              hcontains))
                                        (by
                                          intro childDepth' runtimeType' identity'
                                            hlt hcontains
                                          exact herrors childDepth'
                                            runtimeType' identity' hlt
                                            (by simpa [resolvedValueOrNull] using
                                              hcontains))
                                        (by
                                          intro childDepth' runtimeType' identity'
                                            hlt hcontains hincludes
                                          exact hchildren childDepth'
                                            runtimeType' identity' hlt
                                            (by simpa [resolvedValueOrNull] using
                                              hcontains)
                                            (by
                                              simpa [Schema.fieldReturnType?,
                                                hlookup] using hincludes))
                                    have hprefixLocal :
                                        completeValue schema resolvers
                                          variableValues (childDepth + 1)
                                          (.named typeName)
                                          (GraphQL.Execution.mergedFieldSelectionSet
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                          fields))
                                          (.object runtimeType identity)
                                          none =
                                        GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.named typeName)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          (.object runtimeType identity) :=
                                      completeValue_group_eq_spec_of_contained_child_states
                                        schema resolvers variableValues
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        (childDepth + 1) typeName
                                        (.object runtimeType identity)
                                        (by
                                          intro childDepth' runtimeType' identity'
                                            hlt hcontains hincludes
                                          exact hprefixChildren childDepth'
                                            runtimeType' identity' hlt
                                            (by simpa [resolvedValueOrNull] using
                                              hcontains)
                                            (by
                                              simpa [Schema.fieldReturnType?,
                                                hlookup] using hincludes))
                                    have hrightNeutral :
                                        resultStatus
                                          (completeResolvedValue schema resolvers
                                            variableValues (childDepth + 1)
                                            (.named typeName)
                                            laterSelectionSet
                                            (.object runtimeType identity)
                                            (some (resultValueOrNull
                                              (GraphQL.Execution.completeValue
                                                schema resolvers variableValues
                                                (childDepth + 1)
                                                (.named typeName)
                                                ({ parentType := parentType
                                                   responseName := responseName
                                                   fieldName := fieldName
                                                   arguments := arguments
                                                   selectionSet := selectionSet } ::
                                                  fields)
                                                (.object runtimeType identity))))) =
                                          visitOk := by
                                      by_cases hincludes :
                                          schema.typeIncludesObjectBool typeName
                                            runtimeType = true
                                      · have hrightLocal :=
                                          resultStatus_completeValue_object_append_second_of_errorNeutral
                                            schema resolvers variableValues
                                            childDepth typeName runtimeType
                                            identity
                                            (GraphQL.Execution.mergedFieldSelectionSet
                                              ({ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := arguments
                                                 selectionSet := selectionSet } ::
                                                fields))
                                            laterSelectionSet hincludes
                                            (herrors childDepth runtimeType
                                              identity
                                              (Nat.lt_succ_self childDepth)
                                              (by
                                                simp [resolvedValueOrNull,
                                                  ValueContainsObject.here]))
                                        dsimp at hrightLocal
                                        rw [hprefixLocal] at hrightLocal
                                        exact hrightLocal
                                      · have hnotIncludes :
                                            schema.typeIncludesObjectBool
                                              typeName runtimeType = false := by
                                          cases h :
                                              schema.typeIncludesObjectBool
                                                typeName runtimeType <;>
                                            simp [h] at hincludes ⊢
                                        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, resultStatus, visitOk]
                                    have htailVisit :
                                        visitSubfields schema resolvers
                                          variableValues (childDepth + 2)
                                          parentType source
                                          (executableFieldSelections
                                            [{ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := laterArguments
                                               selectionSet :=
                                                 laterSelectionSet }])
                                          (groupedFieldVisitResult responseName
                                            (GraphQL.Execution.singleFieldResult
                                              responseName
                                              (GraphQL.Execution.completeValue
                                                schema resolvers variableValues
                                                (childDepth + 1)
                                                (.named typeName)
                                                ({ parentType := parentType
                                                   responseName := responseName
                                                   fieldName := fieldName
                                                   arguments := arguments
                                                   selectionSet := selectionSet } ::
                                                  fields)
                                                (.object runtimeType identity)))).fst =
                                        mergeResponseFieldResult responseName
                                          (completeResolvedValue schema resolvers
                                            variableValues (childDepth + 1)
                                            (.named typeName)
                                            laterSelectionSet
                                            (.object runtimeType identity)
                                            (some (resultValueOrNull
                                              (GraphQL.Execution.completeValue
                                                schema resolvers variableValues
                                                (childDepth + 1)
                                                (.named typeName)
                                                ({ parentType := parentType
                                                   responseName := responseName
                                                   fieldName := fieldName
                                                   arguments := arguments
                                                   selectionSet := selectionSet } ::
                                                  fields)
                                                (.object runtimeType identity)))))
                                          (groupedFieldVisitResult responseName
                                            (GraphQL.Execution.singleFieldResult
                                              responseName
                                              (GraphQL.Execution.completeValue
                                                schema resolvers variableValues
                                                (childDepth + 1)
                                                (.named typeName)
                                                ({ parentType := parentType
                                                   responseName := responseName
                                                   fieldName := fieldName
                                                   arguments := arguments
                                                   selectionSet := selectionSet } ::
                                                  fields)
                                                (.object runtimeType identity)))).fst := by
                                      cases hprefixCompleted :
                                          GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.named typeName)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            (.object runtimeType identity) with
                                      | error prefixErrors =>
                                          simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, htailNull, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk]
                                      | ok prefixResult =>
                                          rcases prefixResult with
                                            ⟨prefixValue, prefixErrors⟩
                                          have hlaterVisit :=
                                            visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
                                              schema resolvers variableValues
                                              childDepth parentType
                                              source responseName fieldName
                                              laterArguments laterSelectionSet
                                              { name := definitionName
                                                outputType := .named typeName
                                                arguments :=
                                                  definitionArguments }
                                              (.object runtimeType identity)
                                              prefixValue hlookup
                                              hresolveLater
                                          simpa [hprefixCompleted,
                                            groupedFieldVisitResult,
                                            GraphQL.Execution.singleFieldResult]
                                            using hlaterVisit
                                    have hcombined :=
                                      groupedFieldVisitResult_singleFieldResult_combine_neutral
                                        responseName
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.named typeName)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          (.object runtimeType identity))
                                        (completeResolvedValue schema resolvers
                                          variableValues (childDepth + 1)
                                          (.named typeName)
                                          laterSelectionSet
                                          (.object runtimeType identity)
                                          (some (resultValueOrNull
                                            (GraphQL.Execution.completeValue
                                              schema resolvers variableValues
                                              (childDepth + 1)
                                              (.named typeName)
                                              ({ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := arguments
                                                 selectionSet := selectionSet } ::
                                                fields)
                                              (.object runtimeType identity)))))
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.named typeName)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            (fields ++
                                              [{ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := laterArguments
                                                 selectionSet :=
                                                   laterSelectionSet }]))
                                          (.object runtimeType identity))
                                        hrightNeutral hspecAppend
                                    simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult] at htailVisit hcombined ⊢
                                    rw [htailVisit]
                                    exact hcombined
                                | list values =>
                                    simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk, GraphQL.Execution.completeValue, htailNull]
                            | list inner =>
                                have happend :=
                                  completeValue_group_append_one_result_eq_spec_and_status
                                    schema resolvers variableValues (.list inner)
                                    (childDepth + 1) resolvedValue
                                    ({ parentType := parentType
                                       responseName := responseName
                                       fieldName := fieldName
                                       arguments := arguments
                                       selectionSet := selectionSet } ::
                                      fields)
                                    { parentType := parentType
                                      responseName := responseName
                                      fieldName := fieldName
                                      arguments := laterArguments
                                      selectionSet := laterSelectionSet }
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains hincludes
                                      exact hprefixChildren childDepth'
                                        runtimeType' identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains)
                                        (by
                                          simpa [Schema.fieldReturnType?,
                                            hlookup] using hincludes))
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains
                                      exact hobjects childDepth' runtimeType'
                                        identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains))
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains
                                      exact herrors childDepth' runtimeType'
                                        identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains))
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains hincludes
                                      exact hchildren childDepth' runtimeType'
                                        identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains)
                                        (by
                                          simpa [Schema.fieldReturnType?,
                                            hlookup] using hincludes))
                                have hspecAppend := happend.left
                                have hrightNeutral := happend.right.left
                                have htailVisit :
                                    visitSubfields schema resolvers
                                      variableValues (childDepth + 2)
                                      parentType source
                                      (executableFieldSelections
                                        [{ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := laterArguments
                                           selectionSet := laterSelectionSet }])
                                      (groupedFieldVisitResult responseName
                                        (GraphQL.Execution.singleFieldResult
                                          responseName
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.list inner)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            resolvedValue))).fst =
                                    mergeResponseFieldResult responseName
                                      (completeResolvedValue schema resolvers
                                        variableValues (childDepth + 1)
                                        (.list inner) laterSelectionSet
                                        resolvedValue
                                        (some (resultValueOrNull
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.list inner)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            resolvedValue))))
                                      (groupedFieldVisitResult responseName
                                        (GraphQL.Execution.singleFieldResult
                                          responseName
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.list inner)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            resolvedValue))).fst := by
                                  cases hprefixCompleted :
                                      GraphQL.Execution.completeValue schema
                                        resolvers variableValues
                                        (childDepth + 1) (.list inner)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        resolvedValue with
                                  | error prefixErrors =>
                                      simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, htailNull, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk]
                                  | ok prefixResult =>
                                      rcases prefixResult with
                                        ⟨prefixValue, prefixErrors⟩
                                      have hlaterVisit :=
                                        visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
                                          schema resolvers variableValues
                                          childDepth parentType source
                                          responseName fieldName laterArguments
                                          laterSelectionSet
                                          { name := definitionName
                                            outputType := .list inner
                                            arguments := definitionArguments }
                                          resolvedValue prefixValue hlookup
                                          hresolveLater
                                      simpa [hprefixCompleted,
                                        groupedFieldVisitResult,
                                        GraphQL.Execution.singleFieldResult]
                                        using hlaterVisit
                                have hcombined :=
                                  groupedFieldVisitResult_singleFieldResult_combine_neutral
                                    responseName
                                    (GraphQL.Execution.completeValue schema
                                      resolvers variableValues (childDepth + 1)
                                      (.list inner)
                                      ({ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := arguments
                                         selectionSet := selectionSet } ::
                                        fields)
                                      resolvedValue)
                                    (completeResolvedValue schema resolvers
                                      variableValues (childDepth + 1)
                                      (.list inner) laterSelectionSet
                                      resolvedValue
                                      (some (resultValueOrNull
                                        (GraphQL.Execution.completeValue schema
                                          resolvers variableValues
                                          (childDepth + 1) (.list inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))))
                                    (GraphQL.Execution.completeValue schema
                                      resolvers variableValues (childDepth + 1)
                                      (.list inner)
                                      (({ parentType := parentType
                                          responseName := responseName
                                          fieldName := fieldName
                                          arguments := arguments
                                          selectionSet := selectionSet } ::
                                         fields) ++
                                        [{ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := laterArguments
                                           selectionSet :=
                                             laterSelectionSet }])
                                      resolvedValue)
                                    hrightNeutral hspecAppend
                                simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult]
                                  at htailVisit hcombined ⊢
                                rw [htailVisit]
                                exact hcombined
                            | nonNull inner =>
                                have happend :=
                                  completeValue_group_append_one_result_eq_spec_and_status
                                    schema resolvers variableValues
                                    (.nonNull inner) (childDepth + 1)
                                    resolvedValue
                                    ({ parentType := parentType
                                       responseName := responseName
                                       fieldName := fieldName
                                       arguments := arguments
                                       selectionSet := selectionSet } ::
                                      fields)
                                    { parentType := parentType
                                      responseName := responseName
                                      fieldName := fieldName
                                      arguments := laterArguments
                                      selectionSet := laterSelectionSet }
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains hincludes
                                      exact hprefixChildren childDepth'
                                        runtimeType' identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains)
                                        (by
                                          simpa [Schema.fieldReturnType?,
                                            hlookup] using hincludes))
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains
                                      exact hobjects childDepth' runtimeType'
                                        identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains))
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains
                                      exact herrors childDepth' runtimeType'
                                        identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains))
                                    (by
                                      intro childDepth' runtimeType' identity'
                                        hlt hcontains hincludes
                                      exact hchildren childDepth' runtimeType'
                                        identity' hlt
                                        (by simpa [resolvedValueOrNull] using
                                          hcontains)
                                        (by
                                          simpa [Schema.fieldReturnType?,
                                            hlookup] using hincludes))
                                have hspecAppend := happend.left
                                have hrightNeutral := happend.right.left
                                have htailVisit :
                                    visitSubfields schema resolvers
                                      variableValues (childDepth + 2)
                                      parentType source
                                      (executableFieldSelections
                                        [{ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := laterArguments
                                           selectionSet := laterSelectionSet }])
                                      (groupedFieldVisitResult responseName
                                        (GraphQL.Execution.singleFieldResult
                                          responseName
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.nonNull inner)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            resolvedValue))).fst =
                                    mergeResponseFieldResult responseName
                                      (completeResolvedValue schema resolvers
                                        variableValues (childDepth + 1)
                                        (.nonNull inner) laterSelectionSet
                                        resolvedValue
                                        (some (resultValueOrNull
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.nonNull inner)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            resolvedValue))))
                                      (groupedFieldVisitResult responseName
                                        (GraphQL.Execution.singleFieldResult
                                          responseName
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1) (.nonNull inner)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            resolvedValue))).fst := by
                                  cases hprefixCompleted :
                                      GraphQL.Execution.completeValue schema
                                        resolvers variableValues
                                        (childDepth + 1) (.nonNull inner)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        resolvedValue with
                                  | error prefixErrors =>
                                      simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, htailNull, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk]
                                  | ok prefixResult =>
                                      rcases prefixResult with
                                        ⟨prefixValue, prefixErrors⟩
                                      have hlaterVisit :=
                                        visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
                                          schema resolvers variableValues
                                          childDepth parentType source
                                          responseName fieldName laterArguments
                                          laterSelectionSet
                                          { name := definitionName
                                            outputType := .nonNull inner
                                            arguments := definitionArguments }
                                          resolvedValue prefixValue hlookup
                                          hresolveLater
                                      simpa [hprefixCompleted,
                                        groupedFieldVisitResult,
                                        GraphQL.Execution.singleFieldResult]
                                        using hlaterVisit
                                have hcombined :=
                                  groupedFieldVisitResult_singleFieldResult_combine_neutral
                                    responseName
                                    (GraphQL.Execution.completeValue schema
                                      resolvers variableValues (childDepth + 1)
                                      (.nonNull inner)
                                      ({ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := arguments
                                         selectionSet := selectionSet } ::
                                        fields)
                                      resolvedValue)
                                    (completeResolvedValue schema resolvers
                                      variableValues (childDepth + 1)
                                      (.nonNull inner) laterSelectionSet
                                      resolvedValue
                                      (some (resultValueOrNull
                                        (GraphQL.Execution.completeValue schema
                                          resolvers variableValues
                                          (childDepth + 1) (.nonNull inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))))
                                    (GraphQL.Execution.completeValue schema
                                      resolvers variableValues (childDepth + 1)
                                      (.nonNull inner)
                                      (({ parentType := parentType
                                          responseName := responseName
                                          fieldName := fieldName
                                          arguments := arguments
                                          selectionSet := selectionSet } ::
                                         fields) ++
                                        [{ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := laterArguments
                                           selectionSet :=
                                             laterSelectionSet }])
                                      resolvedValue)
                                    hrightNeutral hspecAppend
                                simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult]
                                  at htailVisit hcombined ⊢
                                rw [htailVisit]
                                exact hcombined

theorem ExecutableFieldsMergedResponse_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hprefixResponses :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups :
      ∀ candidate, candidate ∈ fields ++ [later] ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition)
    (hresolveFirst :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object [])))
    (hchildren :
        ∀ childDepth runtimeType identity,
          childDepth < depth ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            runtimeType = true ->
            ExecutionStateEquivalent
              { window :=
                { schema := schema
                  resolvers := resolvers
                  variableValues := variableValues
                  depth := childDepth
                  parentType := runtimeType
                  source := .object runtimeType identity
                  selectionSet :=
                    GraphQL.Execution.mergedFieldSelectionSet
                      ((field :: fields) ++ [later]) }
                initial := .object [] }) :
      ExecutableFieldsMergedResponse schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedResponse_of_raw schema resolvers variableValues
    depth parentType source responseName field (fields ++ [later]) resolved
  exact
    ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
      variableValues depth parentType source responseName field fields later
      resolved hprefixRaw hprefixResponses hfieldResponse hlaterResponse
      hfieldParent hlaterParent hfieldName htailLookups hresolveFirst hresolveLater
      (by
        intro childDepth runtimeType identity hlt _hcontains hincludes
        exact hprefixChildren childDepth runtimeType identity hlt hincludes)
      (by
        intro childDepth runtimeType identity hlt _hcontains
        exact hobjects childDepth runtimeType identity hlt)
      (by
        intro childDepth runtimeType identity hlt _hcontains
        exact herrors childDepth runtimeType identity hlt)
      (by
        intro childDepth runtimeType identity hlt _hcontains hincludes
        exact hchildren childDepth runtimeType identity hlt hincludes)

theorem ExecutableFieldsMergedComplete_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hprefixResponses :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups :
      ∀ candidate, candidate ∈ fields ++ [later] ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition)
    (hresolveFirst :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: fields) ++ [later]) }
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedComplete_of_MergedResponse
  apply ExecutableFieldsMergedResponse_append_one_of_prefix schema resolvers
    variableValues depth parentType source responseName field fields later
    resolved
  · exact hprefixRaw
  · exact hprefixResponses
  · exact hfieldResponse
  · exact hlaterResponse
  · exact hfieldParent
  · exact hlaterParent
  · exact hfieldName
  · exact htailLookups
  · exact hresolveFirst
  · exact hresolveLater
  · exact hprefixChildren
  · exact hobjects
  · exact herrors
  · exact hchildren

theorem ExecutableFieldsMergedResponse_append_one_of_prefix_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hprefixResponses :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups :
      ∀ candidate, candidate ∈ fields ++ [later] ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition)
    (hresolveFirst :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object [])))
      (hchildren :
        ∀ childDepth runtimeType identity,
          childDepth < depth ->
          ValueContainsObject resolved runtimeType identity ->
          schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            runtimeType = true ->
            ExecutionStateEquivalent
              { window :=
                { schema := schema
                  resolvers := resolvers
                  variableValues := variableValues
                  depth := childDepth
                  parentType := runtimeType
                  source := .object runtimeType identity
                  selectionSet :=
                    GraphQL.Execution.mergedFieldSelectionSet
                      ((field :: fields) ++ [later]) }
                initial := .object [] }) :
      ExecutableFieldsMergedResponse schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedResponse_of_raw schema resolvers variableValues
    depth parentType source responseName field (fields ++ [later]) resolved
  exact
    ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
      variableValues depth parentType source responseName field fields later
      resolved hprefixRaw hprefixResponses hfieldResponse hlaterResponse
      hfieldParent hlaterParent hfieldName htailLookups hresolveFirst
      hresolveLater
      hprefixChildren hobjects herrors hchildren

theorem ExecutableFieldsMergedComplete_append_one_of_prefix_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field fields resolved)
    (hprefixResponses :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups :
      ∀ candidate, candidate ∈ fields ++ [later] ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition)
    (hresolveFirst :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (field :: fields) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: fields) ++ [later]) }
              initial := .object [] }) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedComplete_of_MergedResponse
  apply ExecutableFieldsMergedResponse_append_one_of_prefix_contained
    schema resolvers variableValues depth parentType source responseName field
    fields later resolved
  · exact hprefixRaw
  · exact hprefixResponses
  · exact hfieldResponse
  · exact hlaterResponse
  · exact hfieldParent
  · exact hlaterParent
  · exact hfieldName
  · exact htailLookups
  · exact hresolveFirst
  · exact hresolveLater
  · exact hprefixChildren
  · exact hobjects
  · exact herrors
  · exact hchildren

def ExecutableFieldsMergedCompleteAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity)) :
    List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      later.responseName = responseName ∧
      later.parentType = parentType ∧
      later.fieldName = field.fieldName ∧
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object [])))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) ∧
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved
        (prefixTail ++ [later]) rest

def ExecutableFieldsMergedCompleteContainedAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity)) :
    List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      later.responseName = responseName ∧
      later.parentType = parentType ∧
      later.fieldName = field.fieldName ∧
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object [])))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) ∧
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved
        (prefixTail ++ [later]) rest

structure ExecutedFieldAppendStep
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (prefixTail : List ExecutableField) (later : ExecutableField) where
  responseName_eq : later.responseName = responseName
  parent_eq : later.parentType = parentType
  fieldName_eq : later.fieldName = field.fieldName
  resolved_eq :
    resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolved
  prefixChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet :=
                GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail) }
            initial := .object [] }
  absorbs :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
        ResponseAbsorbs
          (visitSubfields schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))
            (.object []))
          (visitSubfields schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
  errorNeutral :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
        VisitSubfieldsErrorNeutral schema resolvers variableValues
          childDepth runtimeType (.object runtimeType identity)
          later.selectionSet
          (visitSubfields schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet
              (field :: prefixTail))
            (.object []))
  extendedChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet :=
                GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: prefixTail) ++ [later]) }
            initial := .object [] }

def ExecutedFieldAppendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity)) :
    List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      ExecutedFieldAppendStep schema resolvers variableValues depth
        parentType source responseName field resolved prefixTail later ∧
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved (prefixTail ++ [later]) rest

def ExecutedFieldAppendPlanState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (field : ExecutableField) (fields : List ExecutableField) :
    List ExecutableField -> List ExecutableField -> Prop
  | prefixTail, [] =>
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }
  | prefixTail, later :: rest =>
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) ∧
      later ∈ field :: fields ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object [])))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))) ∧
      (∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) ∧
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields (prefixTail ++ [later]) rest

theorem ExecutedFieldAppendPlanState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields prefixTail : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail [] :=
  hprefixChildren

theorem ExecutedFieldAppendPlanState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail rest : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] })
    (hrest :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields (prefixTail ++ [later]) rest) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail (later :: rest) :=
  ⟨hprefixChildren, hlater, hobjects, herrors, hchildren, hrest⟩

theorem ExecutedFieldAppendPlanState.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail [later] := by
  refine ⟨hprefixChildren, hlater, hobjects, herrors, hchildren, ?_⟩
  intro childDepth runtimeType identity hlt hincludes
  simpa using hchildren childDepth runtimeType identity hlt hincludes

theorem ExecutedFieldAppendPlanState.cons_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail rest : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hsteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] })
    (hrest :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields (prefixTail ++ [later]) rest) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail (later :: rest) := by
  apply ExecutedFieldAppendPlanState.cons hprefixChildren hlater
  · intro childDepth runtimeType identity hlt
    exact visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity)
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object []))
      later.selectionSet
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object []))
      (hsteps childDepth runtimeType identity hlt)
  · exact herrors
  · exact hchildren
  · exact hrest

theorem ExecutedFieldAppendPlanState.singleton_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail : List ExecutableField}
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlater : later ∈ field :: fields)
    (hsteps :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail [later] := by
  apply ExecutedFieldAppendPlanState.cons_of_visit_absorbs hprefixChildren
    hlater hsteps herrors hchildren
  intro childDepth runtimeType identity hlt hincludes
  simpa using hchildren childDepth runtimeType identity hlt hincludes

theorem ExecutedFieldAppendPlanState.prefixChildren
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField}
    {fields prefixTail remaining : List ExecutableField} :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail remaining ->
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] } := by
  cases remaining with
  | nil =>
      intro hstate
      exact hstate
  | cons later rest =>
      intro hstate
      exact hstate.1

theorem ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ∀ prefixTail remaining,
      (∀ later, later ∈ remaining -> later ∈ fields) ->
        ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields prefixTail remaining
  | prefixTail, [], _hremaining => by
      exact ExecutedFieldAppendPlanState.nil (hprefixChildren prefixTail)
  | prefixTail, later :: rest, hremaining => by
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons (hprefixChildren prefixTail)
      · exact List.mem_cons_of_mem field hlaterFields
      · exact hobjects prefixTail later hlaterFields
      · exact herrors prefixTail later hlaterFields
      · exact hchildren prefixTail later hlaterFields
      · apply ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
          hprefixChildren hobjects herrors hchildren
          (prefixTail ++ [later]) rest
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])

theorem ExecutedFieldAppendPlanState.of_all_prefixes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields := by
  apply ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
    hprefixChildren hobjects herrors hchildren
  intro later hlater
  exact hlater

theorem ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ∀ prefixTail remaining,
      (∀ later, later ∈ remaining -> later ∈ fields) ->
        ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields prefixTail remaining
  | prefixTail, [], _hremaining => by
      exact ExecutedFieldAppendPlanState.nil (hprefixChildren prefixTail)
  | prefixTail, later :: rest, hremaining => by
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons_of_visit_absorbs
        (hprefixChildren prefixTail)
      · exact List.mem_cons_of_mem field hlaterFields
      · exact hsteps prefixTail later hlaterFields
      · exact herrors prefixTail later hlaterFields
      · exact hchildren prefixTail later hlaterFields
      · apply
          ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
            hprefixChildren hsteps herrors hchildren
            (prefixTail ++ [later]) rest
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])

theorem ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields := by
  apply
    ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
      hprefixChildren hsteps herrors hchildren
  intro later hlater
  exact hlater

theorem ExecutedFieldAppendPlanState.of_all_prefixes_of_local_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hlocal :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType = true ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields := by
  apply ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
    hprefixChildren
  · intro prefixTail later hlater childDepth runtimeType identity hlt
    let base :=
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object [])
    have hbaseReady : ResponseMergeReady base := by
      exact visitSubfields_response_ready schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) []
        ResponseMergeReady_empty_object
    have hbaseAbsorbs : ResponseAbsorbs base base :=
      ResponseAbsorbs_refl_of_ready base hbaseReady
    exact
      visitSubfields_absorbs_from_local_steps schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) base
        later.selectionSet base hbaseReady hbaseAbsorbs
        (hlocal prefixTail later hlater childDepth runtimeType identity hlt)
  · exact herrors
  · exact hchildren

theorem ExecutedFieldAppendPlan.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Option (ResolverValue ObjectIdentity)}
    {prefixTail : List ExecutableField} {later : ExecutableField}
    (step :
      ExecutedFieldAppendStep schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail later) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field resolved prefixTail [later] := by
  exact ⟨step, by simp [ExecutedFieldAppendPlan]⟩

theorem ExecutedFieldAppendPlan.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Option (ResolverValue ObjectIdentity)}
    {prefixTail : List ExecutableField} :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field resolved prefixTail [] := by
  simp [ExecutedFieldAppendPlan]

theorem ExecutedFieldAppendPlan.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Option (ResolverValue ObjectIdentity)}
    {prefixTail : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    (step :
      ExecutedFieldAppendStep schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail later)
    (restPlan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved (prefixTail ++ [later]) rest) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field resolved prefixTail (later :: rest) :=
  ⟨step, restPlan⟩

theorem ExecutedFieldAppendPlan.toAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity)) :
    ∀ prefixTail rest,
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail rest ->
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved prefixTail rest
  | _prefixTail, [], _plan => by
      simp [ExecutableFieldsMergedCompleteAppendSteps]
  | prefixTail, later :: rest, plan => by
      rcases plan with ⟨step, restPlan⟩
      simp [ExecutableFieldsMergedCompleteAppendSteps]
      exact
        ⟨step.responseName_eq, step.parent_eq, step.fieldName_eq,
          step.resolved_eq, step.prefixChildren, step.absorbs,
          step.errorNeutral, step.extendedChildren,
          ExecutedFieldAppendPlan.toAppendSteps schema resolvers
            variableValues depth parentType source responseName field resolved
            (prefixTail ++ [later]) rest restPlan⟩

structure ExecutedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) where
  resolved : Option (ResolverValue ObjectIdentity)
  responseName_eq :
    ∀ candidate, candidate ∈ field :: fields ->
      candidate.responseName = responseName
  parent_eq :
    ∀ candidate, candidate ∈ field :: fields ->
      candidate.parentType = parentType
  resolved_eq :
    resolvers.resolve field.parentType field.fieldName field.arguments source =
      resolved
  headLookup :
    ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
      some fieldDefinition
  headChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet := field.selectionSet }
            initial := .object [] }
  appendSteps :
    ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
      depth parentType source responseName field resolved [] fields

theorem ExecutableFieldsMergedComplete_of_appendSteps_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldParent : field.parentType = parentType)
    (hfieldResponse : field.responseName = responseName)
    (hresolveFirst :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved) :
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition) ->
    ∀ prefixTail remaining,
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field prefixTail resolved ->
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field prefixTail resolved ->
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved prefixTail
        remaining ->
      (∀ candidate, candidate ∈ field :: prefixTail ->
        candidate.responseName = responseName) ->
      (∀ candidate, candidate ∈ prefixTail ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition) ->
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field (prefixTail ++ remaining)
        resolved
  | _hfieldLookup, prefixTail, [], _hprefixRaw, hprefix, _hsteps,
      _hprefixResponses, _hprefixLookups => by
      simpa using hprefix
  | hfieldLookup, prefixTail, later :: rest, hprefixRaw, hprefix, hsteps,
      hprefixResponses, hprefixLookups => by
      simp [ExecutableFieldsMergedCompleteAppendSteps] at hsteps
      rcases hsteps with
        ⟨hlaterResponse, hlaterParent, hfieldName, hresolveLater,
          hprefixChildren, hobjects, herrors, hchildren, hrest⟩
      have htailLookups :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            ∃ fieldDefinition, schema.lookupField parentType
              candidate.fieldName = some fieldDefinition := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hprefixMem | hlater
        · exact hprefixLookups candidate hprefixMem
        · subst candidate
          rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
          exact ⟨fieldDefinition, by simpa [hfieldName] using hlookup⟩
      have hnextResponses :
          ∀ candidate, candidate ∈ field :: (prefixTail ++ [later]) ->
            candidate.responseName = responseName := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hhead | htail
        · subst candidate
          exact hfieldResponse
        · rcases htail with hprefixTail | hlater
          · exact hprefixResponses candidate (by simp [hprefixTail])
          · subst candidate
            exact hlaterResponse
      have hnextRaw :
          ExecutableFieldsMergedRaw schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
          variableValues depth parentType source responseName field prefixTail
          later resolved hprefixRaw hprefixResponses hfieldResponse
          hlaterResponse hfieldParent hlaterParent hfieldName htailLookups
          hresolveFirst hresolveLater
          (by
            intro childDepth runtimeType identity hlt _hcontains hincludes
            exact hprefixChildren childDepth runtimeType identity hlt hincludes)
          (by
            intro childDepth runtimeType identity hlt _hcontains
            exact hobjects childDepth runtimeType identity hlt)
          (by
            intro childDepth runtimeType identity hlt _hcontains
            exact herrors childDepth runtimeType identity hlt)
          (by
            intro childDepth runtimeType identity hlt _hcontains hincludes
            exact hchildren childDepth runtimeType identity hlt hincludes)
      have hnext :
          ExecutableFieldsMergedComplete schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedComplete_append_one_of_prefix schema resolvers
          variableValues depth parentType source responseName field prefixTail
          later resolved hprefixRaw hprefixResponses hfieldResponse
          hlaterResponse hfieldParent hlaterParent hfieldName htailLookups
          hresolveFirst hresolveLater hprefixChildren hobjects herrors
          hchildren
      have htail :=
        ExecutableFieldsMergedComplete_of_appendSteps_from_prefix schema
          resolvers variableValues depth parentType source responseName field
          resolved hfieldParent hfieldResponse hresolveFirst hfieldLookup
          (prefixTail ++ [later]) rest hnextRaw hnext hrest
          hnextResponses htailLookups
      simpa [List.append_assoc] using htail

theorem ExecutableFieldsMergedComplete_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved [] fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields resolved := by
  have hbase :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedComplete_single_of_guarded_child_states schema resolvers
      variableValues depth parentType source responseName field resolved
      hfieldResponse hfieldParent hresolve hfieldChildren
  have hbaseRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedRaw_single_of_guarded_child_states schema resolvers
      variableValues depth parentType source responseName field resolved
      hfieldResponse hfieldParent hresolve hfieldChildren
  simpa using
    ExecutableFieldsMergedComplete_of_appendSteps_from_prefix schema resolvers
      variableValues depth parentType source responseName field resolved
      hfieldParent hfieldResponse hresolve hfieldLookup [] fields hbaseRaw hbase
      hsteps
      (by
        intro candidate hmem
        simp at hmem
        subst candidate
        exact hfieldResponse)
      (by simp)

theorem ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldParent : field.parentType = parentType)
    (hfieldResponse : field.responseName = responseName)
    (hresolveFirst :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved) :
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition) ->
    ∀ prefixTail remaining,
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field prefixTail resolved ->
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field prefixTail resolved ->
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved
        prefixTail remaining ->
      (∀ candidate, candidate ∈ field :: prefixTail ->
        candidate.responseName = responseName) ->
      (∀ candidate, candidate ∈ prefixTail ->
        ∃ fieldDefinition, schema.lookupField parentType candidate.fieldName =
          some fieldDefinition) ->
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field (prefixTail ++ remaining)
        resolved
  | _hfieldLookup, prefixTail, [], _hprefixRaw, hprefix, _hsteps,
      _hprefixResponses, _hprefixLookups => by
      simpa using hprefix
  | hfieldLookup, prefixTail, later :: rest, hprefixRaw, hprefix, hsteps,
      hprefixResponses, hprefixLookups => by
      simp [ExecutableFieldsMergedCompleteContainedAppendSteps] at hsteps
      rcases hsteps with
        ⟨hlaterResponse, hlaterParent, hfieldName, hresolveLater,
          hprefixChildren, hobjects, herrors, hchildren, hrest⟩
      have htailLookups :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            ∃ fieldDefinition, schema.lookupField parentType
              candidate.fieldName = some fieldDefinition := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hprefixMem | hlater
        · exact hprefixLookups candidate hprefixMem
        · subst candidate
          rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
          exact ⟨fieldDefinition, by simpa [hfieldName] using hlookup⟩
      have hnextResponses :
          ∀ candidate, candidate ∈ field :: (prefixTail ++ [later]) ->
            candidate.responseName = responseName := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hhead | htail
        · subst candidate
          exact hfieldResponse
        · rcases htail with hprefixTail | hlater
          · exact hprefixResponses candidate (by simp [hprefixTail])
          · subst candidate
            exact hlaterResponse
      have hnextRaw :
          ExecutableFieldsMergedRaw schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
          variableValues depth parentType source responseName field prefixTail
          later resolved hprefixRaw hprefixResponses hfieldResponse
          hlaterResponse hfieldParent hlaterParent hfieldName htailLookups
          hresolveFirst hresolveLater hprefixChildren hobjects herrors
          hchildren
      have hnext :
          ExecutableFieldsMergedComplete schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedComplete_append_one_of_prefix_contained schema
          resolvers variableValues depth parentType source responseName field
          prefixTail later resolved hprefixRaw hprefixResponses hfieldResponse
          hlaterResponse hfieldParent hlaterParent hfieldName htailLookups
          hresolveFirst hresolveLater hprefixChildren hobjects herrors
          hchildren
      have htail :=
        ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix
          schema resolvers variableValues depth parentType source responseName
          field resolved hfieldParent hfieldResponse hresolveFirst hfieldLookup
          (prefixTail ++ [later]) rest hnextRaw hnext hrest
          hnextResponses htailLookups
      simpa [List.append_assoc] using htail

theorem ExecutableFieldsMergedComplete_of_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved []
        fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields resolved := by
  have hbase :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedComplete_single_of_contained_child_states schema
      resolvers variableValues depth parentType source responseName field
      resolved hfieldResponse hfieldParent hresolve hfieldChildren
  have hbaseRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedRaw_single_of_contained_child_states schema
      resolvers variableValues depth parentType source responseName field
      resolved hfieldResponse hfieldParent hresolve hfieldChildren
  simpa using
    ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix schema
      resolvers variableValues depth parentType source responseName field
      resolved hfieldParent hfieldResponse hresolve hfieldLookup [] fields
      hbaseRaw hbase
      hsteps (by
        intro candidate hmem
        simp at hmem
        subst candidate
        exact hfieldResponse)
      (by simp)

namespace ExecutedFieldGroup

def of_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields where
  resolved := resolved
  responseName_eq := hresponse
  parent_eq := hparent
  resolved_eq := hresolve
  headLookup := hfieldLookup
  headChildren := hfieldChildren
  appendSteps :=
    ExecutedFieldAppendPlan.toAppendSteps schema resolvers variableValues
      depth parentType source responseName field resolved [] fields plan

theorem field_responseName
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    field.responseName = responseName :=
  group.responseName_eq field (by simp)

theorem field_parent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    field.parentType = parentType :=
  group.parent_eq field (by simp)

theorem mergedComplete
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields group.resolved :=
  ExecutableFieldsMergedComplete_of_appendSteps schema resolvers variableValues
    depth parentType source responseName field fields group.resolved
    group.field_responseName group.field_parent group.resolved_eq
    group.headLookup group.headChildren group.appendSteps

theorem mergedComplete_resolved
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableFieldsMergedComplete schema resolvers variableValues depth
      parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source) := by
  rw [group.resolved_eq]
  exact group.mergedComplete

theorem flatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) :=
  ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete schema
    resolvers variableValues depth parentType source responseName field fields
    group.resolved group.responseName_eq group.parent_eq group.resolved_eq
    group.mergedComplete

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact group.flatSpecEquivalent

end ExecutedFieldGroup

def ExecutedFieldGroups
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    List (Name × List ExecutableField) -> Type
  | [] => Unit
  | (_responseName, []) :: _rest => Empty
  | (responseName, field :: fields) :: rest =>
      ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields ×
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source rest

def ExecutedFieldGroups.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      [] :=
  ()

def ExecutedFieldGroups.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    (hgroup :
      ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields)
    (hrest :
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source rest) :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, field :: fields) :: rest) :=
  (hgroup, hrest)

def ExecutedFieldGroups.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (hgroup :
      ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields) :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      [(responseName, field :: fields)] :=
  ExecutedFieldGroups.cons hgroup ExecutedFieldGroups.nil

theorem ExecutedFieldGroups.no_empty_head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {rest : List (Name × List ExecutableField)} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, []) :: rest) ->
    False := by
  intro hgroups
  exact nomatch hgroups

def ExecutedFieldGroups.head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, field :: fields) :: rest) ->
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields :=
  fun hgroups => hgroups.1

def ExecutedFieldGroups.tail
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)} :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      ((responseName, field :: fields) :: rest) ->
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      rest :=
  fun hgroups => hgroups.2

theorem ExecutedFieldGroups.nil_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [] :=
  ExecutableGroupsFlatSpecEquivalent_nil schema resolvers variableValues
    (depth + 1) parentType source

theorem ExecutedFieldGroups.head_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth parentType source
        ((responseName, field :: fields) :: rest)) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] :=
  (ExecutedFieldGroups.head hgroups).groupFlatSpecEquivalent

def ExecutedFieldGroup.of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields where
  resolved :=
    resolvers.resolve field.parentType field.fieldName field.arguments source
  responseName_eq :=
    hresponses responseName (field :: fields) hgroup
  parent_eq :=
    hparents responseName (field :: fields) hgroup
  resolved_eq := rfl
  headLookup := hfieldLookup
  headChildren := hfieldChildren
  appendSteps := hsteps

def ExecutedFieldGroup.of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields :=
  ExecutedFieldGroup.of_collected_appendSteps schema resolvers variableValues
    depth parentType source groups responseName field fields hgroup
    hresponses hparents hfieldLookup hfieldChildren
    (ExecutedFieldAppendPlan.toAppendSteps schema resolvers variableValues
      depth parentType source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source)
      [] fields plan)

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved [] fields) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved :=
    ExecutableFieldsMergedComplete_of_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields resolved
      hfieldResponse hfieldParent hresolve
      hfieldLookup hfieldChildren
      hsteps
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved [] fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hfieldLookup
      hfieldChildren hsteps

theorem ExecutableGroupsFlatSpecEquivalent_collected_nonempty_group_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  exact
    ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hgroupResponses hgroupParents rfl hfieldLookup
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      hsteps

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved []
        fields) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (field :: fields) := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved :=
    ExecutableFieldsMergedComplete_of_contained_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields resolved
      hfieldResponse hfieldParent hresolve hfieldLookup hfieldChildren hsteps
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hresolve :
      resolvers.resolve field.parentType field.fieldName field.arguments source =
        resolved)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject resolved runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field resolved []
        fields) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_contained_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hfieldLookup
      hfieldChildren hsteps

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source) :=
    ExecutableFieldsMergedComplete_of_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl hfieldLookup
      hfieldChildren
      hsteps
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source) :=
    ExecutableFieldsMergedComplete_of_contained_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl hfieldLookup hfieldChildren hsteps
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendSteps
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldLookup
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      hsteps

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_contained_appendSteps
      schema resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldLookup hfieldChildren hsteps

theorem executeQuery_eq_spec_of_exact_nonempty_group_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendSteps schema
      resolvers variableValues operation depth source responseName field fields
      hroot hcollect hdirect hresponse hparent hfieldLookup hfieldChildren
      hsteps

theorem executeQuery_eq_spec_of_exact_nonempty_group_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_contained_appendSteps
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hfieldLookup
      (by
        intro childDepth runtimeType identity hlt hcontains _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt hcontains)
      hsteps

theorem executeRootSelectionSet_eq_spec_of_executedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth parentType
        source responseName field fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect group.responseName_eq
      group.parent_eq group.mergedComplete_resolved

theorem executeQueryAtDepth_eq_spec_of_executedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth operation.rootType
        source responseName field fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      responseName field fields hcollect hdirect group

theorem executeQuery_eq_spec_of_executedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (group :
      ExecutedFieldGroup schema resolvers variableValues depth operation.rootType
        source responseName field fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_executedFieldGroup schema resolvers
      variableValues operation depth source responseName field fields hroot
      hcollect hdirect group

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = parentType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_appendPlan schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        hresponse hparent rfl hfieldLookup
        hfieldChildren
        plan)

theorem executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth
        operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendPlan schema
      resolvers variableValues depth operation.rootType source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldLookup hfieldChildren plan

theorem executeQuery_eq_spec_of_exact_nonempty_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponse :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.responseName = responseName)
    (hparent :
      ∀ candidate, candidate ∈ field :: fields ->
        candidate.parentType = operation.rootType)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth
        operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_exact_nonempty_group_appendPlan schema
      resolvers variableValues operation depth source responseName field fields
      hroot hcollect hdirect hresponse hparent hfieldLookup
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      plan

theorem executeRootSelectionSet_eq_spec_of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_appendSteps schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents
        hfieldLookup
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hfieldChildren childDepth runtimeType identity hlt)
        hsteps)

theorem executeQueryAtDepth_eq_spec_of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent operation.rootType groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (hsteps :
      ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_collected_appendSteps schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      [(responseName, field :: fields)] responseName field fields hcollect
      hgroup hdirect hresponses hparents hfieldLookup hfieldChildren hsteps rfl

theorem executeRootSelectionSet_eq_spec_of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_appendPlan schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents
        hfieldLookup
        hfieldChildren
        plan)

theorem executeQueryAtDepth_eq_spec_of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent operation.rootType groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth
        operation.rootType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields)
    (hexact : groups = [(responseName, field :: fields)]) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_collected_appendPlan schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      [(responseName, field :: fields)] responseName field fields hcollect
      hgroup hdirect hresponses hparents
      hfieldLookup
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      plan rfl

structure ExecutedSingleGroupSelectionState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) where
  groups : List (Name × List ExecutableField)
  responseName : Name
  field : ExecutableField
  fields : List ExecutableField
  collect_eq :
    GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet = groups
  group_mem : (responseName, field :: fields) ∈ groups
  exact_groups : groups = [(responseName, field :: fields)]
  direct :
    VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
      parentType source selectionSet (.object [])
  responses : CollectedGroupsResponseName groups
  parents : CollectedGroupsParent parentType groups
  headLookup :
    ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
      some fieldDefinition
  headChildren :
    ∀ childDepth runtimeType identity,
      childDepth < depth ->
      schema.typeIncludesObjectBool
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        runtimeType = true ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet := field.selectionSet }
            initial := .object [] }
  appendPlan :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source)
      [] fields

namespace ExecutedSingleGroupSelectionState

def of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hfieldChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := field.selectionSet }
              initial := .object [] })
    (plan :
      ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments
          source)
        [] fields) :
    ExecutedSingleGroupSelectionState schema resolvers variableValues depth
      parentType source selectionSet where
  groups := groups
  responseName := responseName
  field := field
  fields := fields
  collect_eq := hcollect
  group_mem := hgroup
  exact_groups := hexact
  direct := hdirect
  responses :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] }
      groups hcollect
  parents :=
    ExecutionCollectedFieldInvariant.parent_of_collect_eq
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] }
      groups hcollect
  headLookup := hfieldLookup
  headChildren := hfieldChildren
  appendPlan := plan

def toExecutedFieldGroup
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      state.responseName state.field state.fields :=
  ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
    depth parentType source state.groups state.responseName state.field
    state.fields state.group_mem state.responses state.parents
    state.headLookup state.headChildren state.appendPlan

theorem flatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source (state.field :: state.fields) :=
  state.toExecutedFieldGroup.flatSpecEquivalent

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
      (depth + 1) parentType source
      [(state.responseName, state.field :: state.fields)] :=
  state.toExecutedFieldGroup.groupFlatSpecEquivalent

theorem executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_appendPlan schema resolvers
    variableValues depth parentType source selectionSet state.groups
    state.responseName state.field state.fields state.collect_eq
    state.group_mem state.direct state.responses state.parents
    state.headLookup state.headChildren state.appendPlan state.exact_groups

theorem stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source selectionSet
      state.executeRootSelectionSet_eq_spec

theorem executeQueryAtDepth_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        operation.rootType source operation.selectionSet) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact state.executeRootSelectionSet_eq_spec

theorem executeQuery_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (state :
      ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        operation.rootType source operation.selectionSet) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact state.executeQueryAtDepth_eq_spec hroot

end ExecutedSingleGroupSelectionState

theorem ExecutedFieldAppendStep_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hlaterParent : later.parentType = parentType)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hfirstChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet ++ later.selectionSet }
              initial := .object [] }) :
    ExecutedFieldAppendStep schema resolvers variableValues depth parentType
      source responseName first resolved [] later := by
  refine
    { responseName_eq := hlaterResponse
      parent_eq := hlaterParent
      fieldName_eq := hfieldName
      resolved_eq := hresolveLater
      prefixChildren := ?prefixChildren
      absorbs := ?absorbs
      errorNeutral := ?errorNeutral
      extendedChildren := ?extendedChildren }
  · intro childDepth runtimeType identity hlt _hincludes
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hfirstChildren childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hobjects childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet,
      VisitSubfieldsErrorNeutral] using
      herrors childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt _hincludes
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildren childDepth runtimeType identity hlt

theorem ExecutedFieldAppendPlan_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hlaterParent : later.parentType = parentType)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
        resolved)
    (hfirstChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) first.selectionSet
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := first.selectionSet ++ later.selectionSet }
              initial := .object [] }) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName first resolved [] [later] :=
  ExecutedFieldAppendPlan.singleton
    (ExecutedFieldAppendStep_two_of_visit_absorbs schema resolvers
      variableValues depth parentType source responseName first later resolved
      hlaterParent hlaterResponse hfieldName hresolveLater hfirstChildren
      hobjects herrors hchildren)

theorem ExecutedFieldAppendStep.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) (later : ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hlater : later ∈ field :: fields)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object []))))
    (herrors :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object [])))
    (hchildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        schema.typeIncludesObjectBool
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          runtimeType = true ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }) :
    ExecutedFieldAppendStep schema resolvers variableValues depth parentType
      source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments
        source)
      prefixTail later := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible (field :: fields) :=
    hcompatible responseName (field :: fields) hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable resolvers source (field :: fields) :=
    hstable responseName (field :: fields) hgroup
  have hfieldResponse : field.responseName = responseName :=
    hgroupResponses field (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later hlater
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later hlater
  have hsameResponse : field.responseName = later.responseName := by
    rw [hfieldResponse, hlaterResponse]
  have hfieldName : later.fieldName = field.fieldName :=
    (hgroupCompatible field later (by simp) hlater hsameResponse).1.symm
  have hresolveLater :
      resolvers.resolve later.parentType later.fieldName later.arguments source =
      resolvers.resolve field.parentType field.fieldName field.arguments
        source :=
    (hgroupStable field later (by simp) hlater hsameResponse).symm
  refine
    { responseName_eq := hlaterResponse
      parent_eq := hlaterParent
      fieldName_eq := hfieldName
      resolved_eq := hresolveLater
      prefixChildren := hprefixChildren
      absorbs := hobjects
      errorNeutral := herrors
      extendedChildren := hchildren }

theorem ExecutedFieldAppendPlan.of_collected_group_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups) :
    ∀ prefixTail remaining,
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail remaining ->
        ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          prefixTail remaining
  | _prefixTail, [], _hstate => by
      exact ExecutedFieldAppendPlan.nil
  | prefixTail, later :: rest, hstate => by
      rcases hstate with
        ⟨hprefixChildren, hlater, hobjects, herrors, hchildren, hrest⟩
      apply ExecutedFieldAppendPlan.cons
      · exact
          ExecutedFieldAppendStep.of_collected_group schema resolvers
            variableValues depth parentType source groups responseName field
            fields prefixTail later hgroup hlater hresponses hparents
            hcompatible hstable hprefixChildren hobjects herrors hchildren
      · exact
          ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
            variableValues depth parentType source groups responseName field
            fields hgroup hresponses hparents hcompatible hstable
            (prefixTail ++ [later]) rest hrest

theorem ExecutedFieldAppendPlan.of_collected_group_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ∀ prefixTail remaining,
      (∀ later, later ∈ remaining -> later ∈ fields) ->
        ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          prefixTail remaining
  | prefixTail, remaining, hremaining => by
      exact
        ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
          variableValues depth parentType source groups responseName field fields
          hgroup hresponses hparents hcompatible hstable prefixTail remaining
          (ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
            (by
              intro prefixTail childDepth runtimeType identity hlt _hincludes
              exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
            hobjects
            herrors
            (by
              intro prefixTail later hlater childDepth runtimeType identity hlt
                _hincludes
              exact hchildren prefixTail later hlater childDepth runtimeType
                identity hlt)
            prefixTail remaining hremaining)

theorem ExecutedFieldAppendPlan.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
      source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      [] fields := by
  apply ExecutedFieldAppendPlan.of_collected_group_from_prefix schema resolvers
    variableValues depth parentType source groups responseName field fields
    hgroup hresponses hparents hcompatible hstable hprefixChildren hobjects
    herrors hchildren
  intro later hlater
  exact hlater

def ExecutedFieldGroup.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields := by
  let hstate :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields :=
    ExecutedFieldAppendPlanState.of_all_prefixes
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hobjects
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt)
  exact
    ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
      depth parentType source groups responseName field fields hgroup hresponses
      hparents hfieldLookup
      (by
        intro childDepth runtimeType identity hlt
        simpa [GraphQL.Execution.mergedFieldSelectionSet] using
          ExecutedFieldAppendPlanState.prefixChildren hstate childDepth
            runtimeType identity hlt)
      (ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
        variableValues depth parentType source groups responseName field fields
        hgroup hresponses hparents hcompatible hstable [] fields hstate)

def ExecutedFieldGroup.of_collected_group_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hstate :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    ExecutedFieldGroup schema resolvers variableValues depth parentType source
      responseName field fields :=
  ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
    depth parentType source groups responseName field fields hgroup hresponses
    hparents hfieldLookup
    (by
      intro childDepth runtimeType identity hlt
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        ExecutedFieldAppendPlanState.prefixChildren hstate childDepth
          runtimeType identity hlt)
    (ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
      variableValues depth parentType source groups responseName field fields
      hgroup hresponses hparents hcompatible hstable [] fields hstate)

theorem stateEquivalent_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  let state : ExecutionEquivalenceState ObjectIdentity :=
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := parentType
        source := source
        selectionSet := selectionSet }
      initial := .object [] }
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hstable : CollectedGroupsResolveStable resolvers source groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
        hinvariant hcollect
  apply stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_group schema resolvers variableValues
        depth parentType source [(responseName, field :: fields)] responseName
      field fields hgroup hresponses hparents hcompatible hstable
      hfieldLookup hprefixChildren hobjects herrors hchildren)

theorem stateEquivalent_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } := by
  let state : ExecutionEquivalenceState ObjectIdentity :=
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := parentType
        source := source
        selectionSet := selectionSet }
      initial := .object [] }
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hstable : CollectedGroupsResolveStable resolvers source groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
        hinvariant hcollect
  apply stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_group_state schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents hcompatible
        hstable hfieldLookup hplanState)

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet := selectionSet }
    (stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName field fields hcollect hgroup hexact hdirect hinvariant
      hcompatible hfieldLookup hplanState)

theorem executeQueryAtDepth_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
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
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth operation.rootType source
      operation.selectionSet groups responseName field fields hcollect hgroup
      hexact hdirect hinvariant hcompatible hfieldLookup hplanState

theorem executeQuery_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
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
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hplanState :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_field_group_state_of_invariant
      schema resolvers variableValues operation depth source groups responseName
      field fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hplanState

theorem stateEquivalent_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    ExecutionStateEquivalent
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth + 1
          parentType := parentType
          source := source
          selectionSet := selectionSet }
        initial := .object [] } :=
  stateEquivalent_of_collected_field_group_state_of_invariant schema
    resolvers variableValues depth parentType source selectionSet groups
    responseName field fields hcollect hgroup hexact hdirect hinvariant
    hcompatible hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_field_group_state_of_invariant
    schema resolvers variableValues depth parentType source selectionSet groups
    responseName field fields hcollect hgroup hexact hdirect hinvariant
    hcompatible hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeQueryAtDepth_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
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
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source :=
  executeQueryAtDepth_eq_spec_of_collected_field_group_state_of_invariant
    schema resolvers variableValues operation depth source groups responseName
    field fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
    hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeQuery_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
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
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hsteps :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source :=
  executeQuery_eq_spec_of_collected_field_group_state_of_invariant schema
    resolvers variableValues operation depth source groups responseName field
    fields hdepth hroot hcollect hgroup hexact hdirect hinvariant hcompatible
    hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object []))
    (hinvariant :
      ExecutionCollectedFieldInvariant
        { window :=
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := selectionSet }
          initial := .object [] })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeRootSelectionSet schema resolvers variableValues (depth + 1)
      parentType source selectionSet =
    GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    { schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet := selectionSet }
    (stateEquivalent_of_collected_field_group_of_invariant schema resolvers
      variableValues depth parentType source selectionSet groups responseName
      field fields hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hprefixChildren hobjects herrors hchildren)

theorem executeQueryAtDepth_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
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
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQueryAtDepth schema resolvers variableValues operation (depth + 1)
      source =
    GraphQL.Execution.executeQueryAtDepth schema resolvers variableValues
      operation (depth + 1) source := by
  apply executeQueryAtDepth_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_field_group_of_invariant schema resolvers
      variableValues depth operation.rootType source operation.selectionSet
      groups responseName field fields hcollect hgroup hexact hdirect
      hinvariant hcompatible hfieldLookup hprefixChildren hobjects herrors
      hchildren

theorem executeQuery_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryDepthBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect :
      GraphQL.Execution.collectFields schema variableValues operation.rootType
        source operation.selectionSet = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect :
      VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        operation.rootType source operation.selectionSet (.object []))
    (hinvariant :
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
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField operation.rootType
        field.fieldName = some fieldDefinition)
    (hprefixChildren :
      ∀ prefixTail childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] })
    (hobjects :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object []))
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail))
                    (.object []))))
    (herrors :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              VisitSubfieldsErrorNeutral schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail))
                  (.object [])))
    (hchildren :
      ∀ prefixTail later,
        later ∈ fields ->
          ∀ childDepth runtimeType identity,
            childDepth < depth ->
              ExecutionStateEquivalent
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later]) }
                  initial := .object [] }) :
    executeQuery schema resolvers variableValues operation source =
    GraphQL.Execution.executeQuery schema resolvers variableValues operation
      source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryAtDepth_eq_spec_of_collected_field_group_of_invariant schema
      resolvers variableValues operation depth source groups responseName field
      fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hprefixChildren hobjects herrors hchildren

end ExecutionUngrouped
end Algorithms

end GraphQL
