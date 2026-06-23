import GraphQL.Algorithms.ExecutionUngrouped.Equivalence.TwoField

/-!
Group-list proof helpers for the final ungrouped execution equivalence theorem.
-/
namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

local instance : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem combineVisitStatus_left_rotate
    (left middle right : VisitStatus) :
    combineVisitStatus left (combineVisitStatus middle right) =
      combineVisitStatus middle (combineVisitStatus left right) := by
  rw [← combineVisitStatus_assoc,
    combineVisitStatus_comm left middle,
    combineVisitStatus_assoc]

theorem combineVisitStatus_error_one_left_rotate
    (middle right : VisitStatus) :
    combineVisitStatus (.error 1 : VisitStatus)
        (combineVisitStatus middle right) =
      combineVisitStatus middle
        (combineVisitStatus (.error 1 : VisitStatus) right) :=
  combineVisitStatus_left_rotate (.error 1 : VisitStatus) middle right

theorem lookupResponseField?_append_of_not_mem
    (responseName : Name) (prefixFields suffix : List (Name × ResponseValue)) :
    responseName ∉ prefixFields.map Prod.fst ->
      lookupResponseField? responseName (prefixFields ++ suffix) =
        lookupResponseField? responseName suffix := by
  induction prefixFields with
  | nil =>
      intro _hfresh
      simp
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, response⟩
      intro hfresh
      have hhead : (fieldResponseName == responseName) = false := by
        cases h : fieldResponseName == responseName
        · exact rfl
        · exfalso
          exact hfresh (by simp [beq_iff_eq.mp h])
      have hrest : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hfresh (by simp [hmem])
      simp [lookupResponseField?, hhead, ih hrest]

theorem responseObjectField?_object_append_of_not_mem
    (responseName : Name) (prefixFields suffix : List (Name × ResponseValue)) :
    responseName ∉ prefixFields.map Prod.fst ->
      responseObjectField? responseName (.object (prefixFields ++ suffix)) =
        responseObjectField? responseName (.object suffix) := by
  intro hfresh
  simp [responseObjectField?,
    lookupResponseField?_append_of_not_mem responseName prefixFields suffix hfresh]

theorem mergeResponseField_append_of_not_mem
    (responseName : Name) (incoming : ResponseValue)
    (prefixFields suffix : List (Name × ResponseValue)) :
    responseName ∉ prefixFields.map Prod.fst ->
      mergeResponseField responseName incoming (prefixFields ++ suffix) =
        prefixFields ++ mergeResponseField responseName incoming suffix := by
  induction prefixFields with
  | nil =>
      intro _hfresh
      simp
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, existing⟩
      intro hfresh
      have hhead : (fieldResponseName == responseName) = false := by
        cases h : fieldResponseName == responseName
        · exact rfl
        · exfalso
          exact hfresh (by simp [beq_iff_eq.mp h])
      have hrest : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hfresh (by simp [hmem])
      simp [mergeResponseField, hhead, ih hrest]

theorem mergeResponseField_self_key_mem
    (responseName : Name) (incoming : ResponseValue) :
    ∀ fields : List (Name × ResponseValue),
      responseName ∈ (mergeResponseField responseName incoming fields).map
        Prod.fst
  | [] => by
      simp [mergeResponseField]
  | (fieldName, response) :: rest => by
      by_cases h : fieldName == responseName
      · simp [mergeResponseField, beq_iff_eq.mp h]
      · simp [mergeResponseField, h,
          mergeResponseField_self_key_mem responseName incoming rest]

theorem mergeResponseField_preserves_key_mem
    (target responseName : Name) (incoming : ResponseValue) :
    ∀ fields : List (Name × ResponseValue),
      target ∈ fields.map Prod.fst ->
        target ∈ (mergeResponseField responseName incoming fields).map Prod.fst
  | [], hmem => by
      simp at hmem
  | (fieldName, response) :: rest, hmem => by
      by_cases h : fieldName == responseName
      · simp [mergeResponseField, h] at hmem ⊢
        exact hmem
      · simp [mergeResponseField, h] at hmem ⊢
        rcases hmem with hhead | htail
        · exact Or.inl hhead
        · rcases htail with ⟨tailResponse, htailPair⟩
          rcases
            List.mem_map.mp
              (mergeResponseField_preserves_key_mem target responseName incoming
                rest
                (List.mem_map.mpr
                  ⟨(target, tailResponse), htailPair, rfl⟩))
          with ⟨mergedPair, hmergedPair, hmergedName⟩
          rcases mergedPair with ⟨mergedName, mergedResponse⟩
          dsimp at hmergedName
          subst mergedName
          exact Or.inr ⟨mergedResponse, hmergedPair⟩

mutual
  theorem visitSelection_preserves_object_key_mem
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (target : Name) :
      ∀ (selection : Selection) (fields : List (Name × ResponseValue)),
        target ∈ fields.map Prod.fst ->
          ∃ outputFields,
            (visitSelection schema resolvers variableValues depth parentType source
              selection (.object fields)).fst =
              .object outputFields
            ∧ target ∈ outputFields.map Prod.fst
  := by
    intro selection fields hmem
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases depth with
          | zero =>
              refine ⟨fields, ?_, hmem⟩
              simp [visitSelection, hallowed]
            | succ depth' =>
                let previous? :=
                  responseObjectField? responseName (.object fields)
                let field :=
                  executableField parentType responseName fieldName arguments
                    selectionSet
                let fieldResult :=
                  executeFieldVisitResult schema resolvers variableValues depth'
                    source previous? field
                let incoming := resultValueOrNull fieldResult
                cases hprevious :
                    responseObjectField? responseName (.object fields) with
                | none =>
                    refine
                      ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                    · rw [visitSelection_field_allowed_succ schema resolvers
                        variableValues depth' parentType source responseName
                        fieldName arguments directives selectionSet
                        (.object fields) hallowed]
                      simp [mergeResponseFieldResult,
                        mergeResponseFieldIntoObject, incoming, fieldResult,
                        previous?, field, executeFieldVisitResult, hprevious]
                    · exact mergeResponseField_preserves_key_mem target
                        responseName incoming fields hmem
                | some previous =>
                    cases previous with
                    | null =>
                        have hlookupRaw :
                            lookupResponseField? responseName fields =
                              some .null := by
                          simpa [responseObjectField?] using hprevious
                        have hincoming :
                            resultValueOrNull
                              (executeField schema resolvers variableValues
                                depth' source (some .null)
                                (executableField parentType responseName
                                  fieldName arguments selectionSet)) =
                              .null := by
                          cases hlookup :
                              schema.lookupField parentType fieldName <;>
                            simp [executeField, executableField, hlookup,
                              reusablePreviousValue?_null, resultValueOrNull]
                        have hmerge :
                            mergeResponseField responseName
                                (resultValueOrNull
                                  (executeField schema resolvers variableValues
                                    depth' source (some .null)
                                    (executableField parentType responseName
                                      fieldName arguments selectionSet)))
                                fields =
                              fields := by
                          rw [hincoming]
                          exact mergeResponseField_null_of_lookup_null
                            responseName fields hlookupRaw
                        refine ⟨fields, ?_, hmem⟩
                        rw [visitSelection_field_allowed_succ schema resolvers
                          variableValues depth' parentType source responseName
                          fieldName arguments directives selectionSet
                          (.object fields) hallowed]
                        simp [hprevious, mergeResponseFieldResult, mergeResponseFieldIntoObject, hmerge]
                    | scalar value =>
                        refine
                          ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                        · rw [visitSelection_field_allowed_succ schema resolvers
                            variableValues depth' parentType source responseName
                            fieldName arguments directives selectionSet
                            (.object fields) hallowed]
                          simp [mergeResponseFieldResult,
                            mergeResponseFieldIntoObject, incoming, fieldResult,
                            previous?, field, executeFieldVisitResult, hprevious]
                        · exact mergeResponseField_preserves_key_mem target
                            responseName incoming fields hmem
                    | object objectFields =>
                        refine
                          ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                        · rw [visitSelection_field_allowed_succ schema resolvers
                            variableValues depth' parentType source responseName
                            fieldName arguments directives selectionSet
                            (.object fields) hallowed]
                          simp [mergeResponseFieldResult,
                            mergeResponseFieldIntoObject, incoming, fieldResult,
                            previous?, field, executeFieldVisitResult, hprevious]
                        · exact mergeResponseField_preserves_key_mem target
                            responseName incoming fields hmem
                    | list values =>
                        refine
                          ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                        · rw [visitSelection_field_allowed_succ schema resolvers
                            variableValues depth' parentType source responseName
                            fieldName arguments directives selectionSet
                            (.object fields) hallowed]
                          simp [mergeResponseFieldResult,
                            mergeResponseFieldIntoObject, incoming, fieldResult,
                            previous?, field, executeFieldVisitResult, hprevious]
                        · exact mergeResponseField_preserves_key_mem target
                            responseName incoming fields hmem
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false :=
            by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
          exact
            ⟨fields, by
              unfold visitSelection
              simp [hblocked], hmem⟩
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases typeCondition with
          | none =>
              rcases
                visitSubfields_preserves_object_key_mem schema resolvers
                  variableValues depth parentType source target selectionSet
                  fields hmem
              with ⟨outputFields, hvisit, hkey⟩
              exact
                ⟨outputFields, by
                  simp [visitSelection, hallowed, hvisit], hkey⟩
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · rcases
                  visitSubfields_preserves_object_key_mem schema resolvers
                    variableValues depth parentType source target selectionSet
                    fields hmem
                with ⟨outputFields, hvisit, hkey⟩
                exact
                  ⟨outputFields, by
                    simp [visitSelection, hallowed, happly, hvisit], hkey⟩
              · exact
                  ⟨fields, by
                    simp [visitSelection, hallowed, happly], hmem⟩
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false :=
            by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
          cases typeCondition with
          | none =>
              exact
                ⟨fields, by
                  unfold visitSelection
                  simp [hblocked], hmem⟩
          | some typeCondition =>
              exact
                ⟨fields, by
                  unfold visitSelection
                  simp [hblocked], hmem⟩

  theorem visitSubfields_preserves_object_key_mem
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (target : Name) :
      ∀ (selectionSet : List Selection) (fields : List (Name × ResponseValue)),
        target ∈ fields.map Prod.fst ->
          ∃ outputFields,
            (visitSubfields schema resolvers variableValues depth parentType source
              selectionSet (.object fields)).fst =
              .object outputFields
            ∧ target ∈ outputFields.map Prod.fst
  := by
    intro selectionSet fields hmem
    cases selectionSet with
    | nil =>
        exact ⟨fields, by simp [visitSubfields], hmem⟩
    | cons selection rest =>
        rcases
          visitSelection_preserves_object_key_mem schema resolvers
            variableValues depth parentType source target selection fields hmem
        with ⟨headFields, hhead, hheadMem⟩
        rcases
          visitSubfields_preserves_object_key_mem schema resolvers
            variableValues depth parentType source target rest headFields
            hheadMem
        with ⟨tailFields, htail, htailMem⟩
        exact
          ⟨tailFields, by
            simp [visitSubfields]
            rw [hhead]
            simpa using htail, htailMem⟩
end

theorem executeField_object_append_fresh_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (prefixFields suffix : List (Name × ResponseValue)) :
      field.responseName ∉ prefixFields.map Prod.fst ->
        executeField schema resolvers variableValues depth source
          (responseObjectField? field.responseName
            (.object (prefixFields ++ suffix))) field =
        executeField schema resolvers variableValues depth source
          (responseObjectField? field.responseName
            (.object suffix)) field := by
  intro hfresh
  rw [responseObjectField?_object_append_of_not_mem field.responseName
    prefixFields suffix hfresh]

theorem visitSelection_executableField_prefix_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    (prefixFields suffix result : List (Name × ResponseValue))
    (status : VisitStatus) :
    field.responseName ∉ prefixFields.map Prod.fst ->
    visitSelection schema resolvers variableValues depth parentType source
      (executableFieldSelection field) (.object suffix) =
        (.object result, status) ->
    visitSelection schema resolvers variableValues depth parentType source
      (executableFieldSelection field) (.object (prefixFields ++ suffix)) =
      (.object (prefixFields ++ result), status) := by
  intro hfresh hvisit
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      have hfreshName : responseName ∉ prefixFields.map Prod.fst := by
        simpa using hfresh
      cases depth with
      | zero =>
          simp [visitSelection, executableFieldSelection,
            selectionDirectivesAllowBool_empty] at hvisit ⊢
          rcases hvisit with ⟨hresult, hstatus⟩
          subst result
          subst status
          simp
      | succ depth' =>
          have happend :
              responseObjectField? responseName
                  (.object (prefixFields ++ suffix)) =
                responseObjectField? responseName (.object suffix) :=
            responseObjectField?_object_append_of_not_mem responseName
              prefixFields suffix hfreshName
          cases hprevious :
              responseObjectField? responseName (.object suffix) with
          | none =>
              simp [visitSelection, executableFieldSelection, executableField,
                selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                mergeResponseFieldIntoObject, hprevious] at hvisit
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simp [visitSelection, executableFieldSelection, executableField,
                selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                mergeResponseFieldIntoObject, happend, hprevious]
              simpa [hprevious] using
                mergeResponseField_append_of_not_mem responseName
                  (resultValueOrNull
                    (executeField schema resolvers variableValues depth' source
                      (responseObjectField? responseName (.object suffix))
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet }))
                  prefixFields suffix hfreshName
          | some previous =>
              cases previous with
              | null =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    happend, hprevious]
                  simpa [hprevious] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          source
                          (responseObjectField? responseName (.object suffix))
                          (executableField parentType responseName fieldName
                            arguments selectionSet)))
                      prefixFields suffix hfreshName
              | scalar value =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection, executableField,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, happend, hprevious]
                  simpa [hprevious] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          source
                          (responseObjectField? responseName (.object suffix))
                          { parentType := parentType
                            responseName := responseName
                            fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet }))
                      prefixFields suffix hfreshName
              | object objectFields =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection, executableField,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, happend, hprevious]
                  simpa [hprevious] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          source
                          (responseObjectField? responseName (.object suffix))
                          { parentType := parentType
                            responseName := responseName
                            fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet }))
                      prefixFields suffix hfreshName
              | list values =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection, executableField,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, happend, hprevious]
                  simpa [hprevious] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          source
                          (responseObjectField? responseName (.object suffix))
                          { parentType := parentType
                            responseName := responseName
                            fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet }))
                      prefixFields suffix hfreshName

theorem visitSubfields_executableFieldSelections_prefix_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ (fields : List ExecutableField)
      (prefixFields suffix result : List (Name × ResponseValue))
      (status : VisitStatus),
      (∀ field, field ∈ fields ->
        field.responseName ∉ prefixFields.map Prod.fst) ->
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections fields) (.object suffix) =
        (.object result, status) ->
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections fields) (.object (prefixFields ++ suffix)) =
        (.object (prefixFields ++ result), status)
  | [], prefixFields, suffix, result, status, _hfresh, hvisit => by
      simp [executableFieldSelections, visitSubfields, visitOk] at hvisit
      rcases hvisit with ⟨hresult, hstatus⟩
      subst result
      subst status
      simp [executableFieldSelections, visitSubfields, visitOk]
  | field :: rest, prefixFields, suffix, result, status, hfresh, hvisit => by
      have hfreshHead :
          field.responseName ∉ prefixFields.map Prod.fst :=
        hfresh field (by simp)
      have hfreshRest :
          ∀ restField, restField ∈ rest ->
            restField.responseName ∉ prefixFields.map Prod.fst := by
        intro restField hrestField
        exact hfresh restField (by simp [hrestField])
      rcases
        visitSelection_preserves_object schema resolvers variableValues depth
          parentType source (executableFieldSelection field) suffix
        with ⟨headFields, hheadFst⟩
      let headStatus :=
        (visitSelection schema resolvers variableValues depth parentType source
          (executableFieldSelection field) (.object suffix)).snd
      have hhead :
          visitSelection schema resolvers variableValues depth parentType source
            (executableFieldSelection field) (.object suffix) =
          (.object headFields, headStatus) := by
        exact Prod.ext hheadFst rfl
      let tail :=
        visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections rest) (.object headFields)
      have hvisitTail :
          tail.fst = .object result ∧
            combineVisitStatus headStatus tail.snd = status := by
        simp [executableFieldSelections, visitSubfields] at hvisit
        rw [hhead] at hvisit
        simpa [tail, executableFieldSelections] using hvisit
      have htail :
          visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections rest) (.object headFields) =
          (.object result, tail.snd) := by
        exact Prod.ext hvisitTail.1 rfl
      have hheadPrefix :
          visitSelection schema resolvers variableValues depth parentType source
            (executableFieldSelection field)
            (.object (prefixFields ++ suffix)) =
          (.object (prefixFields ++ headFields), headStatus) :=
        visitSelection_executableField_prefix_fresh schema resolvers
          variableValues depth parentType source field prefixFields suffix
          headFields headStatus hfreshHead hhead
      have htailPrefix :
          visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections rest)
            (.object (prefixFields ++ headFields)) =
          (.object (prefixFields ++ result), tail.snd) :=
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues depth parentType source rest prefixFields headFields
          result tail.snd hfreshRest htail
      simp [executableFieldSelections, visitSubfields]
      rw [hheadPrefix]
      change
        (visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections rest)
            (.object (prefixFields ++ headFields))).fst =
            .object (prefixFields ++ result) ∧
          combineVisitStatus headStatus
            (visitSubfields schema resolvers variableValues depth parentType
              source (executableFieldSelections rest)
              (.object (prefixFields ++ headFields))).snd =
            status
      constructor
      · rw [htailPrefix]
      · rw [htailPrefix]
        exact hvisitTail.2

theorem visitSelection_field_prefix_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (prefixFields suffix result : List (Name × ResponseValue))
    (status : VisitStatus) :
    (selectionDirectivesAllowBool variableValues directives = true ->
      responseName ∉ prefixFields.map Prod.fst) ->
    visitSelection schema resolvers variableValues depth parentType source
      (.field responseName fieldName arguments directives selectionSet)
      (.object suffix) =
      (.object result, status) ->
    visitSelection schema resolvers variableValues depth parentType source
      (.field responseName fieldName arguments directives selectionSet)
      (.object (prefixFields ++ suffix)) =
      (.object (prefixFields ++ result), status) := by
  intro hfreshIfAllowed hvisit
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · have hfreshName := hfreshIfAllowed hallowed
    cases depth with
    | zero =>
        simp [visitSelection, hallowed] at hvisit ⊢
        rcases hvisit with ⟨hresult, hstatus⟩
        subst result
        subst status
        simp
    | succ depth' =>
        have happend :
            responseObjectField? responseName
                (.object (prefixFields ++ suffix)) =
              responseObjectField? responseName (.object suffix) :=
          responseObjectField?_object_append_of_not_mem responseName
            prefixFields suffix hfreshName
        cases hprevious :
            responseObjectField? responseName (.object suffix) with
        | none =>
            simp [visitSelection, hallowed, mergeResponseFieldResult,
              mergeResponseFieldIntoObject, hprevious] at hvisit
            rcases hvisit with ⟨hresult, hstatus⟩
            subst result
            subst status
            simp [visitSelection, hallowed, mergeResponseFieldResult,
              mergeResponseFieldIntoObject, happend, hprevious]
            simpa [hprevious] using
              mergeResponseField_append_of_not_mem responseName
                (resultValueOrNull
                  (executeField schema resolvers variableValues depth' source
                    (responseObjectField? responseName (.object suffix))
                    { parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet }))
                prefixFields suffix hfreshName
        | some previous =>
            cases previous with
            | null =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        source
                        (responseObjectField? responseName (.object suffix))
                        { parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
            | scalar value =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        source
                        (responseObjectField? responseName (.object suffix))
                        { parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
            | object objectFields =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        source
                        (responseObjectField? responseName (.object suffix))
                        { parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
            | list values =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        source
                        (responseObjectField? responseName (.object suffix))
                        { parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
  · have hskipped :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hdir :
          selectionDirectivesAllowBool variableValues directives <;>
        simp [hdir] at hallowed ⊢
    have hnotAllowed :
        ¬ selectionDirectivesAllowBool variableValues directives := by
      intro hallowed
      simp [hskipped] at hallowed
    unfold visitSelection at hvisit ⊢
    simp [hnotAllowed] at hvisit ⊢
    rcases hvisit with ⟨hresult, hstatus⟩
    subst result
    subst status
    simp

mutual
  theorem visitSelection_prefix_fresh
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity) :
      ∀ (selection : Selection)
        (prefixFields suffix result : List (Name × ResponseValue))
        (status : VisitStatus),
        (∀ field,
          field ∈
            collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection) ->
          field.responseName ∉ prefixFields.map Prod.fst) ->
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object suffix) =
          (.object result, status) ->
        visitSelection schema resolvers variableValues depth parentType source
          selection (.object (prefixFields ++ suffix)) =
          (.object (prefixFields ++ result), status)
  := by
    intro selection prefixFields suffix result status hfresh hvisit
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        apply visitSelection_field_prefix_fresh schema resolvers variableValues
          depth parentType source responseName fieldName arguments directives
          selectionSet prefixFields suffix result status
        · intro hallowed
          apply hfresh
            (executableField parentType responseName fieldName arguments
              selectionSet)
          simp [GraphQL.Execution.collectSelection, hallowed,
            collectedExecutableFields, executableField]
        · exact hvisit
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallowed :
                selectionDirectivesAllowBool variableValues directives
            · have hbodyFresh :
                  ∀ field,
                    field ∈
                      collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source selectionSet) ->
                    field.responseName ∉ prefixFields.map Prod.fst := by
                intro field hmem
                apply hfresh field
                simpa [GraphQL.Execution.collectSelection, hallowed] using hmem
              have hbodyVisit :
                  visitSubfields schema resolvers variableValues depth parentType
                    source selectionSet (.object suffix) =
                  (.object result, status) := by
                simpa [visitSelection, hallowed] using hvisit
              have hprefix :=
                visitSubfields_prefix_fresh schema resolvers variableValues
                  depth parentType source selectionSet prefixFields suffix result
                  status hbodyFresh hbodyVisit
              simpa [visitSelection, hallowed] using hprefix
            · simp [visitSelection, hallowed] at hvisit
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simp [visitSelection, hallowed]
        | some typeCondition =>
            by_cases hallowed :
                selectionDirectivesAllowBool variableValues directives
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · have hbodyFresh :
                    ∀ field,
                      field ∈
                        collectedExecutableFields
                          (GraphQL.Execution.collectFields schema variableValues
                            parentType source selectionSet) ->
                      field.responseName ∉ prefixFields.map Prod.fst := by
                  intro field hmem
                  apply hfresh field
                  simpa [GraphQL.Execution.collectSelection, hallowed, happly]
                    using hmem
                have hbodyVisit :
                    visitSubfields schema resolvers variableValues depth
                      parentType source selectionSet (.object suffix) =
                    (.object result, status) := by
                  simpa [visitSelection, hallowed, happly] using hvisit
                have hprefix :=
                  visitSubfields_prefix_fresh schema resolvers variableValues
                    depth parentType source selectionSet prefixFields suffix
                    result status hbodyFresh hbodyVisit
                simpa [visitSelection, hallowed, happly] using hprefix
              · simp [visitSelection, hallowed, happly] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, happly]
            · simp [visitSelection, hallowed] at hvisit
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simp [visitSelection, hallowed]

  theorem visitSubfields_prefix_fresh
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity) :
      ∀ (selectionSet : List Selection)
        (prefixFields suffix result : List (Name × ResponseValue))
        (status : VisitStatus),
        (∀ field,
          field ∈
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                parentType source selectionSet) ->
          field.responseName ∉ prefixFields.map Prod.fst) ->
        visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object suffix) =
          (.object result, status) ->
        visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object (prefixFields ++ suffix)) =
          (.object (prefixFields ++ result), status)
  | [], prefixFields, suffix, result, status, _hfresh, hvisit => by
      simp [visitSubfields] at hvisit
      rcases hvisit with ⟨hresult, hstatus⟩
      subst result
      subst status
      simp [visitSubfields]
  | selection :: rest, prefixFields, suffix, result, status, hfresh, hvisit => by
      have hheadFresh :
          ∀ field,
            field ∈
              collectedExecutableFields
                (GraphQL.Execution.collectSelection schema variableValues
                  parentType source selection) ->
            field.responseName ∉ prefixFields.map Prod.fst := by
        intro field hmem
        apply hfresh field
        simpa [GraphQL.Execution.collectFields] using
          (collectedExecutableFields_mem_mergeExecutableGroups
            (GraphQL.Execution.collectSelection schema variableValues
              parentType source selection)
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest)
            field).mpr (Or.inl hmem)
      have htailFresh :
          ∀ field,
            field ∈
              collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest) ->
            field.responseName ∉ prefixFields.map Prod.fst := by
        intro field hmem
        apply hfresh field
        simpa [GraphQL.Execution.collectFields] using
          (collectedExecutableFields_mem_mergeExecutableGroups
            (GraphQL.Execution.collectSelection schema variableValues
              parentType source selection)
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest)
            field).mpr (Or.inr hmem)
      rcases
        visitSelection_preserves_object schema resolvers variableValues depth
          parentType source selection suffix
      with ⟨headFields, hheadFst⟩
      let headStatus :=
        (visitSelection schema resolvers variableValues depth parentType source
          selection (.object suffix)).snd
      have hhead :
          visitSelection schema resolvers variableValues depth parentType source
            selection (.object suffix) =
          (.object headFields, headStatus) := by
        exact Prod.ext hheadFst rfl
      let tail :=
        visitSubfields schema resolvers variableValues depth parentType source
          rest (.object headFields)
      have hvisitTail :
          tail.fst = .object result ∧
            combineVisitStatus headStatus tail.snd = status := by
        simp [visitSubfields] at hvisit
        rw [hhead] at hvisit
        simpa [tail] using hvisit
      have htail :
          visitSubfields schema resolvers variableValues depth parentType source
            rest (.object headFields) =
          (.object result, tail.snd) := by
        exact Prod.ext hvisitTail.1 rfl
      have hheadPrefix :
          visitSelection schema resolvers variableValues depth parentType source
            selection (.object (prefixFields ++ suffix)) =
          (.object (prefixFields ++ headFields), headStatus) :=
        visitSelection_prefix_fresh schema resolvers variableValues depth
          parentType source selection prefixFields suffix headFields headStatus
          hheadFresh hhead
      have htailPrefix :
          visitSubfields schema resolvers variableValues depth parentType source
            rest (.object (prefixFields ++ headFields)) =
          (.object (prefixFields ++ result), tail.snd) :=
        visitSubfields_prefix_fresh schema resolvers variableValues depth
          parentType source rest prefixFields headFields result tail.snd
          htailFresh htail
      simp [visitSubfields]
      rw [hheadPrefix]
      change
        (visitSubfields schema resolvers variableValues depth parentType source
            rest (.object (prefixFields ++ headFields))).fst =
            .object (prefixFields ++ result) ∧
          combineVisitStatus headStatus
            (visitSubfields schema resolvers variableValues depth parentType
              source rest (.object (prefixFields ++ headFields))).snd =
            status
      constructor
      · rw [htailPrefix]
      · rw [htailPrefix]
        exact hvisitTail.2
end

theorem visitSubfields_executableFieldSelections_same_response_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) :
    ∀ (fields : List ExecutableField)
      (outputFields : List (Name × ResponseValue)),
      fields ≠ [] ->
      (∀ field, field ∈ fields -> field.responseName = responseName) ->
        ∃ resultFields,
          (visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections fields)
            (.object outputFields)).fst =
            .object resultFields
          ∧ responseName ∈ resultFields.map Prod.fst
  | [], _outputFields, hnonempty, _hresponse => by
      exact False.elim (hnonempty rfl)
  | field :: rest, outputFields, _hnonempty, hresponse => by
      rcases
        visitSelection_preserves_object schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelection field) outputFields
      with ⟨headFields, hheadFst⟩
      have hfieldResponse : field.responseName = responseName :=
        hresponse field (by simp)
      have hheadMemField :
          field.responseName ∈ headFields.map Prod.fst := by
        cases field with
        | mk fieldParent fieldResponse fieldName arguments selectionSet =>
              cases hprevious :
                  responseObjectField? fieldResponse (.object outputFields) with
              | none =>
                  simp [executableFieldSelection, visitSelection,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, hprevious] at hheadFst
                  rw [← hheadFst]
                  simpa [hprevious] using
                    mergeResponseField_self_key_mem fieldResponse
                    (resultValueOrNull
                      (executeField schema resolvers variableValues
                        completionDepth source
                        (responseObjectField? fieldResponse (.object outputFields))
                        (executableField parentType fieldResponse fieldName
                          arguments selectionSet)))
                    outputFields
              | some previous =>
                  cases previous with
                  | null =>
                      have hlookupRaw :
                          lookupResponseField? fieldResponse outputFields =
                            some .null := by
                        simpa [responseObjectField?] using hprevious
                      have hmem :
                          fieldResponse ∈ outputFields.map Prod.fst :=
                        List.mem_map_of_mem (f := Prod.fst)
                          (lookupResponseField?_some_mem fieldResponse .null
                            outputFields hlookupRaw)
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      exact mergeResponseField_preserves_key_mem fieldResponse
                        fieldResponse
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth source
                            (some .null)
                            (executableField parentType fieldResponse fieldName
                              arguments selectionSet)))
                        outputFields hmem
                  | scalar value =>
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      simpa [hprevious] using
                        mergeResponseField_self_key_mem fieldResponse
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth source
                            (responseObjectField? fieldResponse
                              (.object outputFields))
                            (executableField parentType fieldResponse fieldName
                              arguments selectionSet)))
                        outputFields
                  | object objectFields =>
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      simpa [hprevious] using
                        mergeResponseField_self_key_mem fieldResponse
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth source
                            (responseObjectField? fieldResponse
                              (.object outputFields))
                            (executableField parentType fieldResponse fieldName
                              arguments selectionSet)))
                        outputFields
                  | list values =>
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      simpa [hprevious] using
                        mergeResponseField_self_key_mem fieldResponse
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth source
                            (responseObjectField? fieldResponse
                              (.object outputFields))
                            (executableField parentType fieldResponse fieldName
                              arguments selectionSet)))
                        outputFields
      have hheadMem : responseName ∈ headFields.map Prod.fst := by
        simpa [hfieldResponse] using hheadMemField
      rcases
        visitSubfields_preserves_object_key_mem schema resolvers variableValues
          (completionDepth + 1) parentType source responseName
          (executableFieldSelections rest) headFields hheadMem
      with ⟨resultFields, htail, htailMem⟩
      refine ⟨resultFields, ?_, htailMem⟩
      let headStatus :=
        (visitSelection schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelection field)
          (.object outputFields)).snd
      have hhead :
          visitSelection schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelection field)
            (.object outputFields) =
          (.object headFields, headStatus) := by
        exact Prod.ext hheadFst rfl
      simp [executableFieldSelections, visitSubfields]
      rw [hhead]
      simpa using htail

theorem visitSubfields_executableFieldSelections_singleton_append_of_mem_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (fields suffix resultFields :
      List (Name × ResponseValue)) (status : VisitStatus)
    (hmem : field.responseName ∈ fields.map Prod.fst)
    (hfieldLookup :
      ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
        some fieldDefinition)
    (hvisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [field])
        (.object fields) =
      (.object resultFields, status)) :
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections [field])
      (.object (fields ++ suffix)) =
    (.object (resultFields ++ suffix), status) := by
  let executedField :=
    executableField parentType field.responseName field.fieldName
      field.arguments field.selectionSet
  rcases lookupResponseField?_some_of_mem field.responseName fields hmem with
    ⟨previous, hlookupRaw⟩
  have hlookup :
      responseObjectField? field.responseName (.object fields) =
        some previous := by
    simpa [responseObjectField?] using hlookupRaw
  have hlookupAppend :
      responseObjectField? field.responseName (.object (fields ++ suffix)) =
        some previous :=
    responseObjectField?_object_append_of_some_left field.responseName fields
      suffix previous hlookup
  let fieldResult :=
    executeFieldVisitResult schema resolvers variableValues completionDepth
      source previous executedField
  cases previous with
  | null =>
      rcases hfieldLookup with ⟨fieldDefinition, hfieldLookup⟩
      rw [show executableFieldSelections [field] =
          [executableFieldSelection field] by rfl] at hvisit ⊢
      simp only [visitSubfields, executableFieldSelection] at hvisit ⊢
      rw [visitSelection_field_allowed_succ schema resolvers variableValues
        completionDepth parentType source field.responseName field.fieldName
        field.arguments [] field.selectionSet (.object fields)
        (selectionDirectivesAllowBool_empty variableValues)] at hvisit
      rw [hlookup] at hvisit
      simp [visitOk, executeField, executableField, hfieldLookup,
        reusablePreviousValue?_null] at hvisit
      rcases hvisit with ⟨hfields, hstatus⟩
      have hmerge :
          mergeResponseField field.responseName .null fields = fields :=
        mergeResponseField_null_of_lookup_null field.responseName fields
          hlookupRaw
      simp [mergeResponseFieldResult, mergeResponseFieldIntoObject]
        at hfields hstatus
      cases hfields
      subst status
      have hlookupAppendRaw :
          lookupResponseField? field.responseName (fields ++ suffix) =
            some .null := by
        simpa [responseObjectField?] using hlookupAppend
      have hmergeAppend :
          mergeResponseField field.responseName .null (fields ++ suffix) =
            fields ++ suffix :=
        mergeResponseField_null_of_lookup_null field.responseName
          (fields ++ suffix) hlookupAppendRaw
      rw [visitSelection_field_allowed_succ schema resolvers variableValues
        completionDepth parentType source field.responseName field.fieldName
        field.arguments [] field.selectionSet (.object (fields ++ suffix))
        (selectionDirectivesAllowBool_empty variableValues)]
      rw [hlookupAppend]
      simpa [visitOk, executeField, executableField, hfieldLookup,
        reusablePreviousValue?_null, mergeResponseFieldResult,
        mergeResponseFieldIntoObject] using
        mergeResponseField_append_of_mem_left field.responseName .null fields
          suffix hmem
  | scalar value =>
      have hbase :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections [field])
            (.object fields) =
          (.object
            (mergeResponseField field.responseName
              (resultValueOrNull fieldResult) fields),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections [field] =
            [executableFieldSelection field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source field.responseName field.fieldName
          field.arguments [] field.selectionSet (.object fields)
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookup]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      have happend :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections [field])
            (.object (fields ++ suffix)) =
          (.object
            (mergeResponseField field.responseName
              (resultValueOrNull fieldResult) (fields ++ suffix)),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections [field] =
            [executableFieldSelection field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source field.responseName field.fieldName
          field.arguments [] field.selectionSet (.object (fields ++ suffix))
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookupAppend]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      rw [hbase] at hvisit
      injection hvisit with hresult hstatus
      injection hresult with hfields
      rw [happend]
      rw [mergeResponseField_append_of_mem_left field.responseName
        (resultValueOrNull fieldResult) fields suffix hmem]
      subst status
      subst resultFields
      rfl
  | object objectFields =>
      have hbase :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections [field])
            (.object fields) =
          (.object
            (mergeResponseField field.responseName
              (resultValueOrNull fieldResult) fields),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections [field] =
            [executableFieldSelection field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source field.responseName field.fieldName
          field.arguments [] field.selectionSet (.object fields)
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookup]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      have happend :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections [field])
            (.object (fields ++ suffix)) =
          (.object
            (mergeResponseField field.responseName
              (resultValueOrNull fieldResult) (fields ++ suffix)),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections [field] =
            [executableFieldSelection field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source field.responseName field.fieldName
          field.arguments [] field.selectionSet (.object (fields ++ suffix))
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookupAppend]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      rw [hbase] at hvisit
      injection hvisit with hresult hstatus
      injection hresult with hfields
      rw [happend]
      rw [mergeResponseField_append_of_mem_left field.responseName
        (resultValueOrNull fieldResult) fields suffix hmem]
      subst status
      subst resultFields
      rfl
  | list values =>
      have hbase :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections [field])
            (.object fields) =
          (.object
            (mergeResponseField field.responseName
              (resultValueOrNull fieldResult) fields),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections [field] =
            [executableFieldSelection field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source field.responseName field.fieldName
          field.arguments [] field.selectionSet (.object fields)
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookup]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      have happend :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections [field])
            (.object (fields ++ suffix)) =
          (.object
            (mergeResponseField field.responseName
              (resultValueOrNull fieldResult) (fields ++ suffix)),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections [field] =
            [executableFieldSelection field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source field.responseName field.fieldName
          field.arguments [] field.selectionSet (.object (fields ++ suffix))
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookupAppend]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      rw [hbase] at hvisit
      injection hvisit with hresult hstatus
      injection hresult with hfields
      rw [happend]
      rw [mergeResponseField_append_of_mem_left field.responseName
        (resultValueOrNull fieldResult) fields suffix hmem]
      subst status
      subst resultFields
      rfl

theorem collectFields_executableFieldSelections_key_mem_global
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (responseName : Name) :
    responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields)).map Prod.fst ↔
      responseName ∈ fields.map (fun field => field.responseName) := by
  induction fields with
  | nil =>
      simp [executableFieldSelections, GraphQL.Execution.collectFields]
  | cons field rest ih =>
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection field) =
            [(field.responseName,
              [executableField parentType field.responseName field.fieldName
                field.arguments field.selectionSet])] := by
        simp [executableFieldSelection, executableField,
          GraphQL.Execution.collectSelection, selectionDirectivesAllowBool_empty]
      simp only [executableFieldSelections, List.map_cons,
        GraphQL.Execution.collectFields]
      rw [hhead]
      rw [mergeExecutableGroups_key_mem]
      constructor
      · intro hmem
        rcases hmem with hheadMem | htailMem
        · have hheadEq : responseName = field.responseName := by
            simpa using hheadMem
          simp [hheadEq]
        · have htail :
              responseName ∈ rest.map (fun field => field.responseName) :=
            ih.mp htailMem
          simp [htail]
      · intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hheadEq | htail
        · exact Or.inl (by simp [hheadEq])
        · exact Or.inr (ih.mpr htail)

theorem collectedExecutableFields_collectFields_executableFieldSelections_lookup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ fields : List ExecutableField,
      ExecutableFieldsParent parentType fields ->
      (∀ field, field ∈ fields ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition) ->
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections fields)) ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition
  | [], _hparents, _hlookups, field, hmem => by
      simp [executableFieldSelections, GraphQL.Execution.collectFields,
        collectedExecutableFields] at hmem
  | original :: rest, hparents, hlookups, field, hmem => by
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection original) =
            [(original.responseName,
              [executableField parentType original.responseName
                original.fieldName original.arguments original.selectionSet])] := by
        simp [executableFieldSelection, executableField,
          GraphQL.Execution.collectSelection, selectionDirectivesAllowBool_empty]
      have hmemSplit :
          field ∈
              collectedExecutableFields
                [(original.responseName,
                  [executableField parentType original.responseName
                    original.fieldName original.arguments
                    original.selectionSet])]
            ∨ field ∈
              collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source (executableFieldSelections rest)) := by
          have hmerge := hmem
          simp only [executableFieldSelections] at hmerge
          exact
            (collectedExecutableFields_mem_mergeExecutableGroups
            [(original.responseName,
              [executableField parentType original.responseName
                original.fieldName original.arguments original.selectionSet])]
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections rest)) field).mp hmerge
      rcases hmemSplit with hheadMem | htailMem
      · have hfieldName : field.fieldName = original.fieldName := by
          have hfieldEq :
              field =
                executableField parentType original.responseName
                  original.fieldName original.arguments
                  original.selectionSet := by
            simpa [collectedExecutableFields, executableField] using hheadMem
          simp [hfieldEq, executableField]
        rcases hlookups original (by simp) with
          ⟨fieldDefinition, hlookup⟩
        exact ⟨fieldDefinition, by simpa [hfieldName] using hlookup⟩
      · exact
          collectedExecutableFields_collectFields_executableFieldSelections_lookup
            schema variableValues parentType source rest
            (by
              intro candidate hcandidate
              exact hparents candidate (by simp [hcandidate]))
            (by
              intro candidate hcandidate
              exact hlookups candidate (by simp [hcandidate]))
            field htailMem

mutual
  def executionSelectionLookupValid (schema : Schema)
      (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives _selectionSet =>
        ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
    | .inlineFragment none _directives selectionSet =>
        executionSelectionSetLookupValid schema parentType selectionSet
    | .inlineFragment (some _typeCondition) _directives selectionSet =>
        executionSelectionSetLookupValid schema parentType selectionSet

    def executionSelectionSetLookupValid (schema : Schema)
        (parentType : Name) (selectionSet : List Selection) : Prop :=
      ∀ selection, selection ∈ selectionSet ->
        executionSelectionLookupValid schema parentType selection
  end

mutual
  theorem collectedExecutableFields_collectSelection_lookupValid
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selection : Selection) :
      executionSelectionLookupValid schema parentType selection ->
      ∀ candidate,
        candidate ∈
            collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection) ->
          ∃ fieldDefinition,
            schema.lookupField parentType candidate.fieldName =
              some fieldDefinition := by
    intro hlookup candidate hcandidate
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldLookupExists :
            ∃ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition := by
          simpa [executionSelectionLookupValid] using hlookup
        rcases hfieldLookupExists with ⟨fieldDefinition, hfieldLookup⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows,
            collectedExecutableFields] at hcandidate
          subst candidate
          exact ⟨fieldDefinition, hfieldLookup⟩
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            collectedExecutableFields] at hcandidate
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hchildLookup :
                executionSelectionSetLookupValid schema parentType
                  selectionSet := by
              simpa [executionSelectionLookupValid] using hlookup
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows] at hcandidate
              exact
                collectedExecutableFields_collectFields_lookupValid schema
                  variableValues parentType source selectionSet hchildLookup
                  candidate hcandidate
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases h :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate
        | some typeCondition =>
            have hchildLookup :
                executionSelectionSetLookupValid schema parentType
                  selectionSet := by
              simpa [executionSelectionLookupValid] using hlookup
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly] at hcandidate
                exact
                  collectedExecutableFields_collectFields_lookupValid schema
                    variableValues parentType source selectionSet hchildLookup
                    candidate hcandidate
              · have hskip :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases h :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hskip,
                  collectedExecutableFields] at hcandidate
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases h :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate

  theorem collectedExecutableFields_collectFields_lookupValid
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection) :
      executionSelectionSetLookupValid schema parentType selectionSet ->
      ∀ candidate,
        candidate ∈
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet) ->
          ∃ fieldDefinition,
            schema.lookupField parentType candidate.fieldName =
              some fieldDefinition := by
    intro hlookup candidate hcandidate
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hcandidate
    | cons selection rest =>
        have hlookupFn :
            ∀ selected, selected ∈ selection :: rest ->
              executionSelectionLookupValid schema parentType selected := by
          simpa [executionSelectionSetLookupValid] using hlookup
        have hheadLookup :
            executionSelectionLookupValid schema parentType selection :=
          hlookupFn selection (by simp)
        have htailLookup :
            executionSelectionSetLookupValid schema parentType rest := by
          unfold executionSelectionSetLookupValid
          intro selected hselected
          exact hlookupFn selected (List.mem_cons_of_mem selection hselected)
        simp [GraphQL.Execution.collectFields] at hcandidate
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
              candidate).mp hcandidate with hhead | htail
        · exact
            collectedExecutableFields_collectSelection_lookupValid schema
              variableValues parentType source selection hheadLookup candidate
              hhead
        · exact
            collectedExecutableFields_collectFields_lookupValid schema
              variableValues parentType source rest htailLookup candidate htail
end

theorem collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    executionSelectionSetLookupValid schema parentType selectionSet ->
      CollectedGroupsFieldLookupValid schema parentType
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
  intro hlookup responseName field fields hgroup
  exact
    collectedExecutableFields_collectFields_lookupValid schema variableValues
      parentType source selectionSet hlookup field
      (collectedExecutableFields_mem_of_group_mem hgroup (by simp))

theorem visitSubfields_flattened_empty_key_mem_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (fields : List (Name × ResponseValue))
    (responseName : Name) :
    (visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet)))
      (.object [])).fst = .object fields ->
    responseName ∈ fields.map Prod.fst ->
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet).map Prod.fst := by
  intro hvisit hmem
  have hflatKey :=
    visitSubfields_object_empty_key_mem_collectFields schema resolvers
      variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet)))
      fields responseName hvisit hmem
  simpa
    [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
    using hflatKey

theorem collectedExecutableFields_responseName_mem
    (groups : List (Name × List ExecutableField))
    (hresponses : CollectedGroupsResponseName groups)
    (field : ExecutableField) :
    field ∈ collectedExecutableFields groups ->
      field.responseName ∈ groups.map Prod.fst := by
  induction groups with
  | nil =>
      intro hmem
      simp [collectedExecutableFields] at hmem
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      intro hmem
      simp [collectedExecutableFields] at hmem
      rcases hmem with hfield | hrest
      · have hfieldResponse :
            field.responseName = responseName :=
          hresponses responseName fields (by simp) field hfield
        simp [hfieldResponse]
      · have hrestResponses : CollectedGroupsResponseName rest :=
          CollectedGroupsResponseName_tail hresponses
        have hname := ih hrestResponses hrest
        simp [hname]

theorem collectedExecutableFields_responseName_ne_of_not_mem
    (responseName : Name)
    (groups : List (Name × List ExecutableField))
    (hresponses : CollectedGroupsResponseName groups) :
    responseName ∉ groups.map Prod.fst ->
      ∀ field, field ∈ collectedExecutableFields groups ->
        field.responseName ≠ responseName := by
  intro hnot field hfield heq
  have hmem :
      field.responseName ∈ groups.map Prod.fst :=
    collectedExecutableFields_responseName_mem groups hresponses field hfield
  exact hnot (by simpa [heq] using hmem)

theorem collectedExecutableFields_fresh_singleton_prefix_of_not_mem
    (responseName : Name) (response : ResponseValue)
    (groups : List (Name × List ExecutableField))
    (hresponses : CollectedGroupsResponseName groups) :
    responseName ∉ groups.map Prod.fst ->
      ∀ field, field ∈ collectedExecutableFields groups ->
        field.responseName ∉ [(responseName, response)].map Prod.fst := by
  intro hnot field hfield hprefix
  have hne :=
    collectedExecutableFields_responseName_ne_of_not_mem responseName groups
      hresponses hnot field hfield
  simp at hprefix
  exact hne hprefix

def VisitSubfieldsFlatCollectsFreshPrefixes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) : Prop :=
  ∀ fields,
    (∀ field,
      field ∈
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet) ->
      field.responseName ∉ fields.map Prod.fst) ->
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source selectionSet (.object fields)

theorem VisitSubfieldsFlatCollectsFreshPrefixes.empty
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection} :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source selectionSet ->
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source selectionSet (.object []) := by
  intro hfresh
  exact hfresh [] (by simp)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source [] := by
  intro fields _hfresh
  exact VisitSubfieldsFlatCollects_nil schema resolvers variableValues depth
    parentType source (.object fields)

theorem VisitSubfieldsFlatCollectsFreshPrefixes.of_allOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
      parentType source selectionSet ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source selectionSet := by
  intro hflat fields _hfresh
  exact hflat (.object fields)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_executableFieldSelections_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) := by
  intro fields _hfresh
  exact
    VisitSubfieldsFlatCollects_executableFieldSelections_collectedCollectFields
      schema resolvers variableValues depth parentType source selectionSet
      (.object fields)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (fields : List ExecutableField)
    (hresponse :
      ∀ field, field ∈ fields -> field.responseName = responseName)
    (hparent :
      ∀ field, field ∈ fields -> field.parentType = parentType) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source (executableFieldSelections fields) :=
  VisitSubfieldsFlatCollectsFreshPrefixes.of_allOutputs schema resolvers
    variableValues depth parentType source (executableFieldSelections fields)
    (by
      intro output
      exact VisitSubfieldsFlatCollects_executableFieldSelections_same_group
        schema resolvers variableValues depth parentType source responseName
        fields output hresponse hparent)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection)
    (hbody :
      match selection with
      | .field _responseName _fieldName _arguments _directives
          _selectionSet =>
          True
      | .inlineFragment none directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
            VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers
              variableValues depth parentType source selectionSet
      | .inlineFragment (some typeCondition) directives selectionSet =>
          selectionDirectivesAllowBool variableValues directives = true ->
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            true ->
            VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers
              variableValues depth parentType source selectionSet) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source [selection] := by
  intro fields hfresh
  apply VisitSubfieldsFlatCollects_single schema resolvers variableValues depth
    parentType source selection (.object fields)
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      exact trivial
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          intro hallowed
          apply hbody hallowed fields
          intro field hfield
          apply hfresh field
          simpa [GraphQL.Execution.collectFields,
            GraphQL.Execution.collectSelection, hallowed] using hfield
      | some typeCondition =>
          intro hallowed happly
          apply hbody hallowed happly fields
          intro field hfield
          apply hfresh field
          simpa [GraphQL.Execution.collectFields,
            GraphQL.Execution.collectSelection, hallowed, happly] using hfield

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      [.field responseName fieldName arguments directives selectionSet] := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_single
  trivial

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hbody :
      selectionDirectivesAllowBool variableValues directives = true ->
        VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source selectionSet) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      [.inlineFragment none directives selectionSet] := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_single
  exact hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (hbody :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        true ->
        VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source selectionSet) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      [.inlineFragment (some typeCondition) directives selectionSet] := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_single
  exact hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues directives = true ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source (selectionSet ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hallows hflat fields hfresh
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (selectionSet ++ rest)) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source selectionSet rest (ResponseValue.object fields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues directives = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source rest ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hskip hflat fields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    (selectionDirectivesAllowBool variableValues directives = true ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source (selectionSet ++ rest)) ->
    (selectionDirectivesAllowBool variableValues directives = false ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hallowed hskipped
  by_cases hallows : selectionDirectivesAllowBool variableValues directives = true
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_allowed
        schema resolvers variableValues depth parentType source directives
        selectionSet rest hallows (hallowed hallows)
  · have hskip : selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_skipped
        schema resolvers variableValues depth parentType source directives
        selectionSet rest hskip (hskipped hskip)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_allowed_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues directives = true ->
    doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source (selectionSet ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.inlineFragment (some typeCondition) directives selectionSet
          :: rest) := by
  intro hallows happly hflat fields hfresh
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (selectionSet ++ rest)) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, happly,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source selectionSet rest (ResponseValue.object fields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, happly,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues directives = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source rest ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.inlineFragment (some typeCondition) directives selectionSet
          :: rest) := by
  intro hskip hflat fields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues directives = true ->
    doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source rest ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.inlineFragment (some typeCondition) directives selectionSet
          :: rest) := by
  intro hallows hnotApply hflat fields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
      hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
    hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection) :
    (selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source (selectionSet ++ rest)) ->
    (selectionDirectivesAllowBool variableValues directives = false ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source rest) ->
    (selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.inlineFragment (some typeCondition) directives selectionSet
          :: rest) := by
  intro hallowedApply hskipped hnotApply
  by_cases hallows : selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · exact
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_allowed_apply
          schema resolvers variableValues depth parentType source typeCondition
          directives selectionSet rest hallows happly
          (hallowedApply hallows happly)
    · have hdoesNotApply :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases h :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      exact
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_not_apply
          schema resolvers variableValues depth parentType source typeCondition
          directives selectionSet rest hallows hdoesNotApply
          (hnotApply hallows hdoesNotApply)
  · have hskip : selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_skipped
        schema resolvers variableValues depth parentType source typeCondition
        directives selectionSet rest hskip (hskipped hskip)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_none_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = true ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
          fieldSelectionSet ::
        inlineSelectionSet ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.field responseName fieldName arguments fieldDirectives
            fieldSelectionSet ::
          Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
          rest) := by
  intro hallows hflat prefixFields hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet ::
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
        fieldSelectionSet :: inlineSelectionSet)
      rest (ResponseValue.object prefixFields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_none_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
          fieldSelectionSet :: rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.field responseName fieldName arguments fieldDirectives
            fieldSelectionSet ::
          Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
          rest) := by
  intro hskip hflat prefixFields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet :: rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_some_cons_allowed_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName typeCondition : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = true ->
    doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
          fieldSelectionSet ::
        inlineSelectionSet ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.field responseName fieldName arguments fieldDirectives
            fieldSelectionSet ::
          Selection.inlineFragment (some typeCondition) inlineDirectives
            inlineSelectionSet ::
          rest) := by
  intro hallows happly hflat prefixFields hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet ::
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, happly,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
        fieldSelectionSet :: inlineSelectionSet)
      rest (ResponseValue.object prefixFields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, happly,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_some_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName typeCondition : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
          fieldSelectionSet :: rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.field responseName fieldName arguments fieldDirectives
            fieldSelectionSet ::
          Selection.inlineFragment (some typeCondition) inlineDirectives
            inlineSelectionSet ::
          rest) := by
  intro hskip hflat prefixFields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet :: rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_some_cons_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName typeCondition : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = true ->
    doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
          fieldSelectionSet :: rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (Selection.field responseName fieldName arguments fieldDirectives
            fieldSelectionSet ::
          Selection.inlineFragment (some typeCondition) inlineDirectives
            inlineSelectionSet ::
          rest) := by
  intro hallows hnotApply hflat prefixFields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet :: rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
      hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
    hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues directives = true ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections prefixFields ++
        executableFieldSelections
          [executableField parentType responseName fieldName arguments
            selectionSet] ++
        rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections prefixFields ++
          Selection.field responseName fieldName arguments directives
            selectionSet ::
          rest) := by
  intro hallows hflat prefixOutput hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++
                executableFieldSelections
                  [executableField parentType responseName fieldName
                    arguments selectionSet] ++
                rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      executableFieldSelections, executableFieldSelection, executableField,
      selectionDirectivesAllowBool_empty,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
    (executableFieldSelections prefixFields ++
      executableFieldSelections
        [executableField parentType responseName fieldName arguments
          selectionSet])
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (executableFieldSelections
      [executableField parentType responseName fieldName arguments
        selectionSet])
    (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.field responseName fieldName arguments directives selectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  cases depth with
  | zero =>
      simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows,
        executableFieldSelections, executableFieldSelection, executableField,
        selectionDirectivesAllowBool_empty,
        GraphQL.NormalForm.collectFields_append, List.append_assoc,
        outOfFuel, combineVisitStatus_error_one_left_rotate] using hbody
  | succ depth' =>
    simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      executableFieldSelections, executableFieldSelection, executableField,
      selectionDirectivesAllowBool_empty,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues directives = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections prefixFields ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections prefixFields ++
          Selection.field responseName fieldName arguments directives
            selectionSet ::
          rest) := by
  intro hskip hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.field responseName fieldName arguments directives selectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  cases depth <;>
    simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = true ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections prefixFields ++
        inlineSelectionSet ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections prefixFields ++
          Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
          rest) := by
  intro hallows hflat prefixOutput hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
    (executableFieldSelections prefixFields ++ inlineSelectionSet)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    inlineSelectionSet (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections prefixFields ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections prefixFields ++
          Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
          rest) := by
  intro hskip hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_allowed_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (typeCondition : Name)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = true ->
    doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections prefixFields ++
        inlineSelectionSet ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections prefixFields ++
          Selection.inlineFragment (some typeCondition) inlineDirectives
            inlineSelectionSet ::
          rest) := by
  intro hallows happly hflat prefixOutput hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, happly,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
    (executableFieldSelections prefixFields ++ inlineSelectionSet)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    inlineSelectionSet (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment (some typeCondition) inlineDirectives
      inlineSelectionSet :: rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, happly,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (typeCondition : Name)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections prefixFields ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections prefixFields ++
          Selection.inlineFragment (some typeCondition) inlineDirectives
            inlineSelectionSet ::
          rest) := by
  intro hskip hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment (some typeCondition) inlineDirectives
      inlineSelectionSet :: rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (typeCondition : Name)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection) :
    selectionDirectivesAllowBool variableValues inlineDirectives = true ->
    doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (executableFieldSelections prefixFields ++ rest) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections prefixFields ++
          Selection.inlineFragment (some typeCondition) inlineDirectives
            inlineSelectionSet ::
          rest) := by
  intro hallows hnotApply hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment (some typeCondition) inlineDirectives
      inlineSelectionSet :: rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List Selection)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right))
    (hleft :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source left)
    (hright :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source right) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source (left ++ right) := by
  intro prefixFields hfresh
  have hrightNodup :
      GraphQL.NormalForm.executableGroupNamesNodup
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right) :=
    GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source right
  have hflatAppend :
      collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (left ++ right)) =
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source left) ++
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source right) := by
    rw [GraphQL.NormalForm.collectFields_append]
    exact
      collectedExecutableFields_mergeExecutableGroups_eq_append_of_namesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right)
        hdisjoint hrightNodup
  have hleftFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left) ->
        field.responseName ∉ prefixFields.map Prod.fst := by
    intro field hmem
    apply hfresh field
    rw [hflatAppend]
    exact List.mem_append_left _ hmem
  let leftFlatSelections :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left))
  obtain ⟨suffixFields, hsuffixFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source leftFlatSelections []
  let suffixStatus :=
    (visitSubfields schema resolvers variableValues depth parentType source
      leftFlatSelections (.object [])).snd
  have hsuffix :
      visitSubfields schema resolvers variableValues depth parentType source
        leftFlatSelections (.object []) =
      (.object suffixFields, suffixStatus) :=
    Prod.ext hsuffixFields rfl
  have hleftPrefix :
      visitSubfields schema resolvers variableValues depth parentType source
        leftFlatSelections (.object prefixFields) =
      (.object (prefixFields ++ suffixFields), suffixStatus) := by
    simpa [leftFlatSelections] using
      visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
        variableValues depth parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source left))
        prefixFields [] suffixFields suffixStatus hleftFresh
        (by simpa [leftFlatSelections] using hsuffix)
  have hrightFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source right) ->
        field.responseName ∉ (prefixFields ++ suffixFields).map Prod.fst := by
    intro field hmem hname
    have hrightName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source right).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right)
        (collectFields_responseName schema variableValues parentType source
          right)
        field hmem
    have hcombined :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (left ++ right)) := by
      rw [hflatAppend]
      exact List.mem_append_right _ hmem
    simp [List.map_append] at hname
    rcases hname with hprefix | hsuffixMem
    · have hprefixName : field.responseName ∈ prefixFields.map Prod.fst := by
        simpa [List.mem_map] using hprefix
      exact hfresh field hcombined hprefixName
    · have hleftName :
          field.responseName ∈
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left).map Prod.fst :=
        visitSubfields_flattened_empty_key_mem_collectFields schema resolvers
          variableValues depth parentType source left suffixFields
          field.responseName
          (by simpa [leftFlatSelections] using hsuffixFields)
          (by simpa [List.mem_map] using hsuffixMem)
      exact hdisjoint field.responseName hleftName hrightName
  apply VisitSubfieldsFlatCollects_append_of_namesDisjoint schema resolvers
    variableValues depth parentType source left right (.object prefixFields)
    hdisjoint hrightNodup
  · simpa [VisitSubfieldsRawFlatCollects, VisitSubfieldsFlatCollects] using
      hleft prefixFields hleftFresh
  · have hrightFlat := hright (prefixFields ++ suffixFields) hrightFresh
    simpa [VisitSubfieldsRawFlatCollects, VisitSubfieldsFlatCollects,
      leftFlatSelections, hleftPrefix] using hrightFlat

theorem VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection) (rest : List Selection)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source [selection])
        (GraphQL.Execution.collectFields schema variableValues parentType
          source rest))
    (hselection :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source [selection])
    (hrest :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source rest) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source (selection :: rest) := by
  simpa using
    VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint schema
      resolvers variableValues depth parentType source [selection] rest
      hdisjoint hselection hrest

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_cons_of_responseName_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (hfresh :
      selectionDirectivesAllowBool variableValues directives = true ->
        responseName ∉
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest).map Prod.fst)
    (hrest :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source rest) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source
      (.field responseName fieldName arguments directives selectionSet ::
        rest) := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint
  · intro candidate hleft hright
    by_cases hallowed :
        selectionDirectivesAllowBool variableValues directives = true
    · simp [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
        hallowed] at hleft
      subst candidate
      exact hfresh hallowed hright
    · have hblocked :
          selectionDirectivesAllowBool variableValues directives = false := by
        cases h :
            selectionDirectivesAllowBool variableValues directives
        · rfl
        · exact False.elim (hallowed h)
      simp [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
        hblocked] at hleft
  · apply VisitSubfieldsFlatCollectsFreshPrefixes_single
    trivial
  · exact hrest

def SelectionSetCollectFieldsHeadDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    List Selection -> Prop
  | [] => True
  | selection :: rest =>
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [selection])
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rest)
      ∧ SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
        source rest

theorem SelectionSetCollectFieldsHeadDisjoint_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ left right,
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
        source left ->
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
        source right ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          right) ->
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
        source (left ++ right)
  | [], right, _hleft, hright, _hdisjoint => by
      simpa [SelectionSetCollectFieldsHeadDisjoint] using hright
  | selection :: rest, right, hleft, hright, hdisjoint => by
      rcases hleft with ⟨hheadRest, hrest⟩
      constructor
      · intro responseName hhead htail
        have htailParts :
            responseName ∈
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest).map Prod.fst
              ∨
            responseName ∈
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source right).map Prod.fst := by
          have htailMerge :
              responseName ∈
                (GraphQL.Execution.mergeExecutableGroups
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest)
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source right)).map Prod.fst := by
            simpa [GraphQL.NormalForm.collectFields_append] using htail
          exact
            (mergeExecutableGroups_key_mem
              (GraphQL.Execution.collectFields schema variableValues
                parentType source rest)
              (GraphQL.Execution.collectFields schema variableValues
                parentType source right)
              responseName).mp htailMerge
        rcases htailParts with hrestName | hrightName
        · exact hheadRest responseName hhead hrestName
        · apply hdisjoint responseName
          · rw [show selection :: rest = [selection] ++ rest by rfl]
            rw [GraphQL.NormalForm.collectFields_append]
            exact
              (mergeExecutableGroups_key_mem
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source [selection])
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest)
                responseName).mpr (Or.inl hhead)
          · exact hrightName
      · exact
          SelectionSetCollectFieldsHeadDisjoint_append_of_namesDisjoint schema
            variableValues parentType source rest right hrest hright
            (by
              intro responseName hrestName hrightName
              apply hdisjoint responseName
              · rw [show selection :: rest = [selection] ++ rest by rfl]
                rw [GraphQL.NormalForm.collectFields_append]
                exact
                  (mergeExecutableGroups_key_mem
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source [selection])
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source rest)
                    responseName).mpr (Or.inr hrestName)
              · exact hrightName)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ selectionSet,
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
        source selectionSet ->
      (∀ selection,
        selection ∈ selectionSet ->
          VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers
            variableValues depth parentType source [selection]) ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source selectionSet
  | [], _hdisjoint, _hsingle =>
      VisitSubfieldsFlatCollectsFreshPrefixes_nil schema resolvers
        variableValues depth parentType source
  | selection :: rest, hdisjoint, hsingle => by
      rcases hdisjoint with ⟨hheadDisjoint, hrestDisjoint⟩
      apply VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint
        schema resolvers variableValues depth parentType source selection rest
        hheadDisjoint
      · exact hsingle selection (by simp)
      · exact
          VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjoint schema
            resolvers variableValues depth parentType source rest
            hrestDisjoint
            (by
              intro candidate hcandidate
              exact hsingle candidate (by simp [hcandidate]))

mutual
  def SelectionCollectFieldsHeadDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity) :
      Selection -> Prop
    | .field _responseName _fieldName _arguments _directives _selectionSet =>
        True
    | .inlineFragment _typeCondition _directives selectionSet =>
        SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet

  def SelectionSetCollectFieldsHeadDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection) : Prop :=
    SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
      source selectionSet
    ∧ ∀ selection, selection ∈ selectionSet ->
        SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
          source selection
end

mutual
  theorem VisitSubfieldsFlatCollectsFreshPrefixes_single_of_headDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity) :
      ∀ selection,
        SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
          source selection ->
        VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source [selection]
    | .field responseName fieldName arguments directives selectionSet, _htree =>
        VisitSubfieldsFlatCollectsFreshPrefixes_field_single schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet
    | .inlineFragment none directives selectionSet, htree =>
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
          resolvers variableValues depth parentType source directives
          selectionSet
          (by
            intro _hallowed
            exact
              VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree
                schema resolvers variableValues depth parentType source
                selectionSet
                (by
                  simpa [SelectionCollectFieldsHeadDisjointTree] using htree))
    | .inlineFragment (some typeCondition) directives selectionSet, htree =>
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
          resolvers variableValues depth parentType source typeCondition
          directives selectionSet
          (by
            intro _hallowed _happly
            exact
              VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree
                schema resolvers variableValues depth parentType source
                selectionSet
                (by
                  simpa [SelectionCollectFieldsHeadDisjointTree] using htree))

  theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity) :
      ∀ selectionSet,
        SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet ->
        VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source selectionSet
    | selectionSet, htree => by
        have htree' :
            SelectionSetCollectFieldsHeadDisjoint schema variableValues
                parentType source selectionSet
              ∧ ∀ selection, selection ∈ selectionSet ->
                  SelectionCollectFieldsHeadDisjointTree schema variableValues
                    parentType source selection := by
          simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree
        rcases htree' with ⟨hdisjoint, hchildren⟩
        exact VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjoint schema
          resolvers variableValues depth parentType source selectionSet
          hdisjoint
          (by
            intro selection hselection
            exact
              VisitSubfieldsFlatCollectsFreshPrefixes_single_of_headDisjointTree
                schema resolvers variableValues depth parentType source
                selection (hchildren selection hselection))
end

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (firstResponse laterResponse : ResponseValue)
    (suffix : List (Name × ResponseValue))
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
      (hfirstResponse :
        firstResponse =
          executeField schema resolvers variableValues completionDepth source
            none
            (executableField parentType first.responseName first.fieldName
              first.arguments first.selectionSet))
      (hlaterResponse :
        laterResponse =
          executeField schema resolvers variableValues completionDepth source
            (some firstResponse)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
    (hmiddleEmpty :
      (visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle)))
        (.object [])).fst =
      .object suffix)
    (hmiddleFlatBase :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source middle
        (.object [(first.responseName, firstResponse)])) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  let firstField :=
    executableField parentType first.responseName first.fieldName
      first.arguments first.selectionSet
  let laterField :=
    executableField parentType later.responseName later.fieldName
      later.arguments later.selectionSet
  let flatMiddle :=
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle))
  let firstStatus :=
      resultStatus
        (executeField schema resolvers variableValues completionDepth source
          none firstField)
  let middleStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source flatMiddle (.object [])).snd
  let laterVisitResult : Result ResponseValue :=
      executeFieldVisitResult schema resolvers variableValues completionDepth
        source (some firstResponse) laterField
  let laterStatus :=
    match firstResponse with
    | .null => visitOk
    | _ => resultStatus laterVisitResult
  have hfirstResponse' :
        firstResponse =
          Result.getD default
            (executeField schema resolvers variableValues completionDepth source
              none firstField) := by
    simpa [firstField] using hfirstResponse
  have hfirstValue :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            none firstField) =
      firstResponse := by
    rw [hfirstResponse']
    cases
          executeField schema resolvers variableValues completionDepth source
            none firstField <;> rfl
  have hlaterResponse' :
        laterResponse =
          Result.getD default
            (executeField schema resolvers variableValues completionDepth source
              (some firstResponse) laterField) := by
    simpa [laterField] using hlaterResponse
  have hlaterValue :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            (some firstResponse) laterField) =
      laterResponse := by
    rw [hlaterResponse']
    cases
          executeField schema resolvers variableValues completionDepth source
            (some firstResponse) laterField <;> rfl
  have hlaterValueSameResponse :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            (some firstResponse)
            (executableField parentType first.responseName later.fieldName
              later.arguments later.selectionSet)) =
         laterResponse := by
    simpa [laterField, hsameResponse] using hlaterValue
  have hlaterVisitValue :
      resultValueOrNull laterVisitResult = laterResponse := by
    dsimp [laterVisitResult]
    exact
        (resultValueOrNull_fieldVisitResult_eq_executeField schema resolvers
          variableValues completionDepth source (some firstResponse)
          laterField).trans
        hlaterValue
  have hfirstVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first]) (.object []) =
      (.object [(first.responseName, firstResponse)], firstStatus) := by
    rw [visitSubfields_executableFieldSelections_singleton_succ schema
      resolvers variableValues completionDepth parentType source first]
    simp [firstField, firstStatus, hfirstValue]
  have hmiddleEmptyPair :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object []) =
      (.object suffix, middleStatus) := by
    exact Prod.ext (by simpa [flatMiddle] using hmiddleEmpty) rfl
  have hsuffixFresh :
      first.responseName ∉ suffix.map Prod.fst := by
    intro hmem
    have hkey :
        first.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle).map Prod.fst :=
      visitSubfields_flattened_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source middle suffix
        first.responseName
        (by simpa [flatMiddle] using hmiddleEmpty)
        hmem
    exact hnotMiddle hkey
  have hmiddleBaseFlat :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object [(first.responseName, firstResponse)]) =
      (.object ([(first.responseName, firstResponse)] ++ suffix),
        middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object ([(first.responseName, firstResponse)] ++ [])) =
        (.object ([(first.responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      apply visitSubfields_executableFieldSelections_prefix_fresh schema
        resolvers variableValues (completionDepth + 1) parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
        [(first.responseName, firstResponse)] [] suffix middleStatus
      · intro field hmem hname
        have hfieldName :
            field.responseName ∈
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle).map Prod.fst :=
          collectedExecutableFields_responseName_mem
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle)
            (collectFields_responseName schema variableValues parentType source
              middle)
            field hmem
        have hfieldEq : field.responseName = first.responseName := by
          simpa using hname
        exact hnotMiddle (by simpa [hfieldEq] using hfieldName)
      · simpa [flatMiddle] using hmiddleEmptyPair
    have hflatBase :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object [(first.responseName, firstResponse)]) =
        (.object ([(first.responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      simpa using hflatPrefix
    simpa [VisitSubfieldsFlatCollects, flatMiddle] using
      hmiddleFlatBase.trans hflatBase
  have hlaterVisitAfterMiddle :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object ([(first.responseName, firstResponse)] ++ suffix)) =
      (.object
        (mergeResponseField first.responseName laterResponse
          ([(first.responseName, firstResponse)] ++ suffix)),
        laterStatus) := by
    have hlookup :
        responseObjectField? later.responseName
          (.object ([(first.responseName, firstResponse)] ++ suffix)) =
        some firstResponse := by
      apply responseObjectField?_object_append_of_some_left
      simp [responseObjectField?, lookupResponseField?, hsameResponse]
    rw [show executableFieldSelections [later] =
        [executableFieldSelection later] by rfl]
    simp only [visitSubfields, executableFieldSelection]
    rw [visitSelection_field_allowed_succ schema resolvers variableValues
      completionDepth parentType source later.responseName later.fieldName
      later.arguments [] later.selectionSet
      (.object ([(first.responseName, firstResponse)] ++ suffix))
      (selectionDirectivesAllowBool_empty variableValues)]
    rw [hlookup]
    cases firstResponse with
    | null =>
        rcases hlaterLookup with ⟨_laterDefinition, hlaterLookup⟩
        have hlaterNull : laterResponse = .null := by
          rw [hlaterResponse]
          simp [executableField, executeField, hlaterLookup, GraphQL.Execution.Result.getD, reusablePreviousValue?_null]
        have hlaterDataNull :
            Result.getD default
              (executeField schema resolvers variableValues completionDepth
                source (some .null)
                (executableField parentType first.responseName
                  later.fieldName later.arguments later.selectionSet)) =
            .null := by
          have hdata :
              Result.getD default
                (executeField schema resolvers variableValues completionDepth
                  source (some .null)
                  (executableField parentType first.responseName
                    later.fieldName later.arguments later.selectionSet)) =
              laterResponse := by
            symm
            simpa [laterField, hsameResponse] using hlaterResponse
          exact hdata.trans hlaterNull
        simp [hlaterNull, visitOk, laterStatus, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, hsameResponse, mergeResponseFieldResult, executeField, executableField, hlaterLookup, reusablePreviousValue?_null, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine]
    | scalar value =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.scalar value))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              ((first.responseName, .scalar value) :: suffix) =
            mergeResponseField first.responseName laterResponse
              ((first.responseName, .scalar value) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.scalar value))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.scalar value))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | object objectFields =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.object objectFields))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              ((first.responseName, .object objectFields) :: suffix) =
            mergeResponseField first.responseName laterResponse
              ((first.responseName, .object objectFields) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.object objectFields))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.object objectFields))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | list values =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.list values))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              ((first.responseName, .list values) :: suffix) =
            mergeResponseField first.responseName laterResponse
              ((first.responseName, .list values) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.list values))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.list values))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
  have hmergedMiddleFlat :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle
        (mergeResponseFieldIntoObject first.responseName laterResponse
          (.object [(first.responseName, firstResponse)])) =
      (.object
        (mergeResponseField first.responseName laterResponse
          [(first.responseName, firstResponse)] ++ suffix),
        middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object
            (mergeResponseField first.responseName laterResponse
              [(first.responseName, firstResponse)] ++ [])) =
        (.object
          (mergeResponseField first.responseName laterResponse
            [(first.responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      apply visitSubfields_executableFieldSelections_prefix_fresh schema
        resolvers variableValues (completionDepth + 1) parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
        (mergeResponseField first.responseName laterResponse
          [(first.responseName, firstResponse)])
        [] suffix middleStatus
      · intro field hmem hname
        have hfieldName :
            field.responseName ∈
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle).map Prod.fst :=
          collectedExecutableFields_responseName_mem
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle)
            (collectFields_responseName schema variableValues parentType source
              middle)
            field hmem
        have hfieldEq : field.responseName = first.responseName := by
          simpa [mergeResponseField, mergeResponse] using hname
        exact hnotMiddle (by simpa [hfieldEq] using hfieldName)
      · simpa [flatMiddle] using hmiddleEmptyPair
    simpa [mergeResponseFieldIntoObject] using hflatPrefix
  have hraw :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) (.object []) =
      (.object
        (mergeResponseField first.responseName laterResponse
          ([(first.responseName, firstResponse)] ++ suffix)),
        combineVisitStatus firstStatus
          (combineVisitStatus middleStatus laterStatus)) := by
    rw [show executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later] =
      executableFieldSelections [first] ++
        (middle ++ executableFieldSelections [later]) by
      simp [List.append_assoc]]
    rw [visitSubfields_append_equivalence]
    rw [hfirstVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (middle ++ executableFieldSelections [later])
          (.object [(first.responseName, firstResponse)])
       (rightResult.fst, combineVisitStatus firstStatus rightResult.snd)) =
      _
    rw [visitSubfields_append_equivalence]
    rw [hmiddleBaseFlat]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object ([(first.responseName, firstResponse)] ++ suffix))
       (rightResult.fst,
        combineVisitStatus firstStatus
          (combineVisitStatus middleStatus rightResult.snd))) =
      _
    rw [hlaterVisitAfterMiddle]
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections [first] ++ middle ++
                executableFieldSelections [later]))) =
      executableFieldSelections [first, later] ++ flatMiddle := by
    simpa [flatMiddle] using
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source first later middle
        hsameResponse hnotMiddle
  have hlaterVisitAfterFirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object [(first.responseName, firstResponse)]) =
      (mergeResponseFieldIntoObject first.responseName laterResponse
        (.object [(first.responseName, firstResponse)]),
        laterStatus) := by
    have hlookup :
        responseObjectField? later.responseName
          (.object [(first.responseName, firstResponse)]) =
        some firstResponse := by
      simp [responseObjectField?, lookupResponseField?, hsameResponse]
    rw [show executableFieldSelections [later] =
        [executableFieldSelection later] by rfl]
    simp only [visitSubfields, executableFieldSelection]
    rw [visitSelection_field_allowed_succ schema resolvers variableValues
      completionDepth parentType source later.responseName later.fieldName
      later.arguments [] later.selectionSet
      (.object [(first.responseName, firstResponse)])
      (selectionDirectivesAllowBool_empty variableValues)]
    rw [hlookup]
    cases firstResponse with
    | null =>
        rcases hlaterLookup with ⟨_laterDefinition, hlaterLookup⟩
        have hlaterNull : laterResponse = .null := by
          rw [hlaterResponse]
          simp [executableField, executeField, hlaterLookup, GraphQL.Execution.Result.getD, reusablePreviousValue?_null]
        have hlaterDataNull :
            Result.getD default
              (executeField schema resolvers variableValues completionDepth
                source (some .null)
                (executableField parentType first.responseName
                  later.fieldName later.arguments later.selectionSet)) =
            .null := by
          have hdata :
              Result.getD default
                (executeField schema resolvers variableValues completionDepth
                  source (some .null)
                  (executableField parentType first.responseName
                    later.fieldName later.arguments later.selectionSet)) =
              laterResponse := by
            symm
            simpa [laterField, hsameResponse] using hlaterResponse
          exact hdata.trans hlaterNull
        simp [hlaterNull, visitOk, laterStatus, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, hsameResponse, mergeResponseFieldResult, executeField, executableField, hlaterLookup, reusablePreviousValue?_null, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine]
    | scalar value =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.scalar value))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              [(first.responseName, .scalar value)] =
            mergeResponseField first.responseName laterResponse
              [(first.responseName, .scalar value)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.scalar value))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.scalar value))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | object objectFields =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.object objectFields))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              [(first.responseName, .object objectFields)] =
            mergeResponseField first.responseName laterResponse
              [(first.responseName, .object objectFields)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.object objectFields))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.object objectFields))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | list values =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.list values))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              [(first.responseName, .list values)] =
            mergeResponseField first.responseName laterResponse
              [(first.responseName, .list values)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.list values))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.list values))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
  have hfirstLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first, later])
        (.object []) =
      (mergeResponseFieldIntoObject first.responseName laterResponse
        (.object [(first.responseName, firstResponse)]),
        combineVisitStatus firstStatus laterStatus) := by
    rw [show executableFieldSelections [first, later] =
        executableFieldSelections [first] ++ executableFieldSelections [later] by
      rfl]
    rw [visitSubfields_append_equivalence]
    rw [hfirstVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object [(first.responseName, firstResponse)])
       (rightResult.fst, combineVisitStatus firstStatus rightResult.snd)) =
      _
    rw [hlaterVisitAfterFirst]
  have hnormalized :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first, later] ++ flatMiddle)
        (.object []) =
      (.object
        (mergeResponseField first.responseName laterResponse
          [(first.responseName, firstResponse)] ++ suffix),
        combineVisitStatus (combineVisitStatus firstStatus laterStatus)
          middleStatus) := by
    rw [visitSubfields_append_equivalence]
    rw [hfirstLater]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (mergeResponseFieldIntoObject first.responseName laterResponse
            (.object [(first.responseName, firstResponse)]))
       (rightResult.fst,
        combineVisitStatus (combineVisitStatus firstStatus laterStatus)
          rightResult.snd)) =
      _
    rw [hmergedMiddleFlat]
  unfold VisitSubfieldsFlatCollects
  rw [hraw]
  rw [hnormalizedBlock]
  rw [hnormalized]
  apply Prod.ext
  · rw [mergeResponseField_append_of_mem_left first.responseName laterResponse
      [(first.responseName, firstResponse)] suffix (by simp)]
  · rw [combineVisitStatus_assoc]
    rw [combineVisitStatus_comm middleStatus laterStatus]

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddleEmpty :
      ∃ suffix,
        (visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle)))
          (.object [])).fst =
        .object suffix)
    (hmiddleFresh :
      ∀ fields,
        (∀ field,
          field ∈
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle) ->
          field.responseName ∉ fields.map Prod.fst) ->
        VisitSubfieldsFlatCollects schema resolvers variableValues
          (completionDepth + 1) parentType source middle (.object fields)) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  rcases hmiddleEmpty with ⟨suffix, hmiddleEmpty⟩
  let firstResponse : ResponseValue :=
      executeField schema resolvers variableValues completionDepth source
        none
        (executableField parentType first.responseName first.fieldName
          first.arguments first.selectionSet)
  let laterResponse : ResponseValue :=
      executeField schema resolvers variableValues completionDepth source
        (some firstResponse)
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet)
  apply
    VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
      schema resolvers variableValues completionDepth parentType source first
      later middle firstResponse laterResponse suffix hsameResponse
      hlaterLookup hnotMiddle
  · rfl
  · rfl
  · exact hmiddleEmpty
  · apply hmiddleFresh
    intro field hmem hname
    have hfieldName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        field hmem
    have hfieldEq : field.responseName = first.responseName := by
      simpa using hname
    exact hnotMiddle (by simpa [hfieldEq] using hfieldName)

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_freshPrefixes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  apply VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_fresh
    schema resolvers variableValues completionDepth parentType source first
    later middle hsameResponse hlaterLookup hnotMiddle
  · obtain ⟨suffix, hsuffix⟩ :=
      visitSubfields_preserves_object schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle)))
        []
    exact ⟨suffix, hsuffix⟩
  · exact hmiddle

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle) :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) := by
  intro prefixFields hfresh
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let flatFields :=
    collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
  obtain ⟨resultFields, hresultFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source rawBlock []
  let status :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object [])).snd
  have hrawEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object []) =
      (.object resultFields, status) :=
    Prod.ext hresultFields rfl
  have hrawPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object prefixFields) =
      (.object (prefixFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_prefix_fresh schema resolvers variableValues
          (completionDepth + 1) parentType source rawBlock prefixFields []
          resultFields status hfresh hrawEmpty
  have hflatEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields) (.object []) =
      (.object resultFields, status) := by
    have hflat :=
      VisitSubfieldsFlatCollects_duplicate_field_middle_of_freshPrefixes schema
        resolvers variableValues completionDepth parentType source first later
        middle hsameResponse hlaterLookup hnotMiddle hmiddle
    unfold VisitSubfieldsFlatCollects at hflat
    dsimp [rawBlock, flatFields] at hflat
    rw [← hflat]
    exact hrawEmpty
  have hflatPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields)
        (.object prefixFields) =
      (.object (prefixFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues (completionDepth + 1) parentType source flatFields
          prefixFields [] resultFields status
          (by
            intro field hmem
            exact hfresh field
              (show
                field ∈
                  collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source
                      (executableFieldSelections [first] ++ middle ++
                        executableFieldSelections [later])) from
                by
                  change
                    field ∈
                      collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source rawBlock)
                  exact hmem))
          hflatEmpty
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object prefixFields) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections flatFields)
        (.object prefixFields)
  rw [hrawPrefix, hflatPrefix]

theorem VisitSubfieldsFlatCollects_group_duplicate_field_middle_of_freshPrefixes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections prefixFields ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let flatMiddle :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle))
  let normalizedBlock :=
    executableFieldSelections (prefixFields ++ [later]) ++ flatMiddle
  obtain ⟨middleSuffix, hmiddleSuffix⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source flatMiddle []
  let middleStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source flatMiddle (.object [])).snd
  have hmiddleEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object []) =
      (.object middleSuffix, middleStatus) :=
    Prod.ext hmiddleSuffix rfl
  obtain ⟨prefixResult, hprefixFst, hprefixKey⟩ :=
    visitSubfields_executableFieldSelections_same_response_key_mem schema
      resolvers variableValues completionDepth parentType source responseName
      prefixFields [] hprefixNonempty hprefixResponse
  let prefixStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections prefixFields)
      (.object [])).snd
  have hprefixVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections prefixFields)
        (.object []) =
      (.object prefixResult, prefixStatus) :=
    Prod.ext hprefixFst rfl
  have hprefixKeys :
      ∀ key, key ∈ prefixResult.map Prod.fst -> key = responseName := by
    intro key hkey
    have hcollectKey :
        key ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (executableFieldSelections prefixFields)).map Prod.fst :=
      visitSubfields_object_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source
        (executableFieldSelections prefixFields) prefixResult key hprefixFst
        hkey
    have hfieldKey :
        key ∈ prefixFields.map (fun field => field.responseName) :=
      (collectFields_executableFieldSelections_key_mem_global schema
        variableValues parentType source prefixFields key).mp hcollectKey
    rcases List.mem_map.mp hfieldKey with ⟨field, hfield, hfieldKeyEq⟩
    rw [← hfieldKeyEq]
    exact hprefixResponse field hfield
  have hmiddleFreshPrefix :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle) ->
        field.responseName ∉ prefixResult.map Prod.fst := by
    intro field hmem hkey
    have hfieldCollectName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        field hmem
    have hfieldName : field.responseName = responseName :=
      hprefixKeys field.responseName hkey
    exact hnotMiddle (by simpa [hfieldName] using hfieldCollectName)
  have hmiddlePrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object prefixResult) =
      (.object (prefixResult ++ middleSuffix), middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle (.object prefixResult) =
        (.object (prefixResult ++ middleSuffix), middleStatus) := by
      simpa [flatMiddle] using
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues (completionDepth + 1) parentType source
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle))
          prefixResult [] middleSuffix middleStatus hmiddleFreshPrefix
          (by simpa [flatMiddle] using hmiddleEmpty)
    have hrawFlat := hmiddle prefixResult hmiddleFreshPrefix
    unfold VisitSubfieldsFlatCollects at hrawFlat
    rw [hrawFlat]
    exact hflatPrefix
  have hlaterMemPrefix : later.responseName ∈ prefixResult.map Prod.fst := by
    simpa [hlaterResponse] using hprefixKey
  obtain ⟨laterResult, hlaterFst⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [later]) prefixResult
  let laterStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections [later])
      (.object prefixResult)).snd
  have hlaterVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object prefixResult) =
      (.object laterResult, laterStatus) :=
    Prod.ext hlaterFst rfl
  have hlaterVisitAfterMiddle :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object (prefixResult ++ middleSuffix)) =
      (.object (laterResult ++ middleSuffix), laterStatus) :=
    visitSubfields_executableFieldSelections_singleton_append_of_mem_succ
      schema resolvers variableValues completionDepth parentType source later
      prefixResult middleSuffix laterResult laterStatus hlaterMemPrefix
      hlaterLookup
      hlaterVisit
  have hraw :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object []) =
      (.object (laterResult ++ middleSuffix),
        combineVisitStatus prefixStatus
          (combineVisitStatus middleStatus laterStatus)) := by
    dsimp [rawBlock]
    rw [show executableFieldSelections prefixFields ++ middle ++
        executableFieldSelections [later] =
      executableFieldSelections prefixFields ++
        (middle ++ executableFieldSelections [later]) by
      simp [List.append_assoc]]
    rw [visitSubfields_append_equivalence]
    rw [hprefixVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (middle ++ executableFieldSelections [later])
          (.object prefixResult)
       (rightResult.fst,
        combineVisitStatus prefixStatus rightResult.snd)) =
      _
    rw [visitSubfields_append_equivalence]
    rw [hmiddlePrefix]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object (prefixResult ++ middleSuffix))
       (rightResult.fst,
        combineVisitStatus prefixStatus
          (combineVisitStatus middleStatus rightResult.snd))) =
      _
    rw [hlaterVisitAfterMiddle]
  have hprefixLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections (prefixFields ++ [later]))
        (.object []) =
      (.object laterResult, combineVisitStatus prefixStatus laterStatus) := by
    rw [show executableFieldSelections (prefixFields ++ [later]) =
        executableFieldSelections prefixFields ++
          executableFieldSelections [later] by
      simp [executableFieldSelections, List.map_append]]
    rw [visitSubfields_append_equivalence]
    rw [hprefixVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object prefixResult)
       (rightResult.fst,
        combineVisitStatus prefixStatus rightResult.snd)) =
      _
    rw [hlaterVisit]
  have hprefixLaterKeys :
      ∀ key, key ∈ laterResult.map Prod.fst -> key = responseName := by
    intro key hkey
    have hcollectKey :
        key ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source
            (executableFieldSelections (prefixFields ++ [later]))).map
            Prod.fst :=
      visitSubfields_object_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source
        (executableFieldSelections (prefixFields ++ [later])) laterResult key
        (by
          have hfst := congrArg Prod.fst hprefixLater
          simpa using hfst)
        hkey
    have hfieldKey :
        key ∈ (prefixFields ++ [later]).map
          (fun field => field.responseName) :=
      (collectFields_executableFieldSelections_key_mem_global schema
        variableValues parentType source (prefixFields ++ [later]) key).mp
        hcollectKey
    rcases List.mem_map.mp hfieldKey with ⟨field, hfield, hfieldKeyEq⟩
    rw [← hfieldKeyEq]
    rcases List.mem_append.mp hfield with hprefix | hlater
    · exact hprefixResponse field hprefix
    · rcases List.mem_singleton.mp hlater
      exact hlaterResponse
  have hmiddleFreshLater :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle) ->
        field.responseName ∉ laterResult.map Prod.fst := by
    intro field hmem hkey
    have hfieldCollectName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        field hmem
    have hfieldName : field.responseName = responseName :=
      hprefixLaterKeys field.responseName hkey
    exact hnotMiddle (by simpa [hfieldName] using hfieldCollectName)
  have hflatMiddleLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object laterResult) =
      (.object (laterResult ++ middleSuffix), middleStatus) := by
    simpa [flatMiddle] using
      visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
        variableValues (completionDepth + 1) parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
        laterResult [] middleSuffix middleStatus hmiddleFreshLater
        (by simpa [flatMiddle] using hmiddleEmpty)
  have hnormalized :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source normalizedBlock (.object []) =
      (.object (laterResult ++ middleSuffix),
        combineVisitStatus (combineVisitStatus prefixStatus laterStatus)
          middleStatus) := by
    dsimp [normalizedBlock]
    rw [visitSubfields_append_equivalence]
    rw [hprefixLater]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle (.object laterResult)
       (rightResult.fst,
        combineVisitStatus (combineVisitStatus prefixStatus laterStatus)
          rightResult.snd)) =
      _
    rw [hflatMiddleLater]
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock)) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock, flatMiddle]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object []) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rawBlock)))
      (.object [])
  rw [hraw, hnormalizedBlock, hnormalized]
  apply Prod.ext
  · rfl
  · rw [combineVisitStatus_comm middleStatus laterStatus]
    rw [← combineVisitStatus_assoc]

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle) :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections prefixFields ++ middle ++
        executableFieldSelections [later]) := by
  intro outputFields hfresh
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let flatFields :=
    collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
  obtain ⟨resultFields, hresultFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source rawBlock []
  let status :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object [])).snd
  have hrawEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object []) =
      (.object resultFields, status) :=
    Prod.ext hresultFields rfl
  have hrawPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object outputFields) =
      (.object (outputFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_prefix_fresh schema resolvers variableValues
          (completionDepth + 1) parentType source rawBlock outputFields []
          resultFields status hfresh hrawEmpty
  have hflatEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields)
        (.object []) =
      (.object resultFields, status) := by
    have hflat :=
      VisitSubfieldsFlatCollects_group_duplicate_field_middle_of_freshPrefixes
        schema resolvers variableValues completionDepth parentType source
        responseName prefixFields later middle hprefixNonempty
        hprefixResponse hlaterResponse hlaterLookup hnotMiddle hmiddle
    unfold VisitSubfieldsFlatCollects at hflat
    dsimp [rawBlock, flatFields] at hflat
    rw [← hflat]
    exact hrawEmpty
  have hflatPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields)
        (.object outputFields) =
      (.object (outputFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues (completionDepth + 1) parentType source flatFields
          outputFields [] resultFields status
          (by
            intro field hmem
            exact hfresh field
              (show
                field ∈
                  collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source
                      (executableFieldSelections prefixFields ++ middle ++
                        executableFieldSelections [later])) from
                by
                  change
                    field ∈
                      collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source rawBlock)
                  exact hmem))
          hflatEmpty
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object outputFields) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections flatFields)
        (.object outputFields)
  rw [hrawPrefix, hflatPrefix]

theorem visitSubfields_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (prefixFields : List (Name × ResponseValue))
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle)
    (hfresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections [first] ++ middle ++
                executableFieldSelections [later])) ->
        field.responseName ∉ prefixFields.map Prod.fst) :
      visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections [first] ++ middle ++
              executableFieldSelections [later]) ++ suffix)
          (.object prefixFields) =
          visitSubfields schema resolvers variableValues
            (completionDepth + 1) parentType source
            ((executableFieldSelections [first, later] ++
                executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle))) ++ suffix)
            (.object prefixFields) := by
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections [first, later] ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle))
  have hblock :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock
        (.object prefixFields) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
      resolvers variableValues completionDepth parentType source first later
      middle hsameResponse hlaterLookup hnotMiddle hmiddle prefixFields hfresh
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock)) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source first later middle
        hsameResponse hnotMiddle
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (rawBlock ++ suffix) (.object prefixFields) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (normalizedBlock ++ suffix) (.object prefixFields)
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source rawBlock suffix
    (.object prefixFields)]
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source normalizedBlock suffix
    (.object prefixFields)]
  unfold VisitSubfieldsFlatCollects at hblock
  rw [hnormalizedBlock] at hblock
  rw [hblock]

theorem visitSubfields_group_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle suffix : List Selection)
    (outputFields : List (Name × ResponseValue))
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle)
    (hfresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++ middle ++
                executableFieldSelections [later])) ->
        field.responseName ∉ outputFields.map Prod.fst) :
    visitSubfields schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections prefixFields ++ middle ++
            executableFieldSelections [later]) ++ suffix)
        (.object outputFields) =
        visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections (prefixFields ++ [later]) ++
              executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))) ++ suffix)
          (.object outputFields) := by
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections (prefixFields ++ [later]) ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle))
  have hblock :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock
        (.object outputFields) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
      schema resolvers variableValues completionDepth parentType source
      responseName prefixFields later middle hprefixNonempty hprefixResponse
      hlaterResponse hlaterLookup hnotMiddle hmiddle outputFields hfresh
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock)) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (rawBlock ++ suffix) (.object outputFields) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (normalizedBlock ++ suffix) (.object outputFields)
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source rawBlock suffix
    (.object outputFields)]
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source normalizedBlock suffix
    (.object outputFields)]
  unfold VisitSubfieldsFlatCollects at hblock
  rw [hnormalizedBlock] at hblock
  rw [hblock]

theorem collectFields_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst) :
    GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) ++ suffix) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++ suffix) := by
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections [first, later] ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
  have hblock :
      GraphQL.Execution.collectFields schema variableValues parentType source
          rawBlock =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    rw [←
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source first later middle
        hsameResponse hnotMiddle]
    exact
      (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later])).symm
  change
    GraphQL.Execution.collectFields schema variableValues parentType source
        (rawBlock ++ suffix) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (normalizedBlock ++ suffix)
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source rawBlock suffix]
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source normalizedBlock suffix]
  rw [hblock]

theorem collectFields_group_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle suffix : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hnotMiddle :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst) :
    GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections prefixFields ++ middle ++
            executableFieldSelections [later]) ++ suffix) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections (prefixFields ++ [later]) ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++ suffix) := by
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections (prefixFields ++ [later]) ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
  have hblock :
      GraphQL.Execution.collectFields schema variableValues parentType source
          rawBlock =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    rw [←
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hprefixResponse hlaterResponse hnotMiddle]
    exact
      (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source
        (executableFieldSelections prefixFields ++ middle ++
          executableFieldSelections [later])).symm
  change
    GraphQL.Execution.collectFields schema variableValues parentType source
        (rawBlock ++ suffix) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (normalizedBlock ++ suffix)
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source rawBlock suffix]
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source normalizedBlock suffix]
  rw [hblock]

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_normalized
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle)
    (hnormalized :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++ suffix)) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source
      ((executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) ++ suffix) := by
  intro prefixFields hfresh
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let normalized :=
    (executableFieldSelections [first, later] ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))) ++ suffix
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (rawBlock ++ suffix) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalized := by
    dsimp [rawBlock, normalized]
    exact
      collectFields_duplicate_field_middle_append_eq_collected_middle schema
        variableValues parentType source first later middle suffix
        hsameResponse hnotMiddle
  have hblockFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) ->
        field.responseName ∉ prefixFields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    have hfieldRaw :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix)) := by
      exact
        (collectedExecutableFields_mem_mergeExecutableGroups
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rawBlock)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source suffix) field).mpr (Or.inl hfield)
    have hfieldWhole :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (rawBlock ++ suffix)) := by
      rw [GraphQL.NormalForm.collectFields_append schema variableValues
        parentType source rawBlock suffix]
      exact hfieldRaw
    simpa [rawBlock] using hfieldWhole
  change
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source (rawBlock ++ suffix)
      (.object prefixFields)
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_duplicate_field_middle_append_eq_collected_middle schema
    resolvers variableValues completionDepth parentType source first later
    middle suffix prefixFields hsameResponse hlaterLookup hnotMiddle hmiddle
    hblockFresh]
  rw [hcollect]
  exact hnormalized prefixFields
    (by
      intro field hfield
      have hfieldRaw :
          field ∈
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (rawBlock ++ suffix)) := by
        rw [hcollect]
        exact hfield
      apply hfresh field
      simpa [rawBlock, List.append_assoc] using hfieldRaw)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_group_duplicate_field_middle_append_of_normalized
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle suffix : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle)
    (hnormalized :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections (prefixFields ++ [later]) ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++ suffix)) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source
      ((executableFieldSelections prefixFields ++ middle ++
        executableFieldSelections [later]) ++ suffix) := by
  intro outputFields hfresh
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let normalized :=
    (executableFieldSelections (prefixFields ++ [later]) ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))) ++ suffix
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (rawBlock ++ suffix) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalized := by
    dsimp [rawBlock, normalized]
    exact
      collectFields_group_duplicate_field_middle_append_eq_collected_middle
        schema variableValues parentType source responseName prefixFields later
        middle suffix hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  have hblockFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) ->
        field.responseName ∉ outputFields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    have hfieldRaw :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix)) := by
      exact
        (collectedExecutableFields_mem_mergeExecutableGroups
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rawBlock)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source suffix) field).mpr (Or.inl hfield)
    have hfieldWhole :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (rawBlock ++ suffix)) := by
      rw [GraphQL.NormalForm.collectFields_append schema variableValues
        parentType source rawBlock suffix]
      exact hfieldRaw
    simpa [rawBlock] using hfieldWhole
  change
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source (rawBlock ++ suffix)
      (.object outputFields)
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_group_duplicate_field_middle_append_eq_collected_middle
    schema resolvers variableValues completionDepth parentType source
    responseName prefixFields later middle suffix outputFields hprefixNonempty
    hprefixResponse hlaterResponse hlaterLookup hnotMiddle hmiddle
    hblockFresh]
  rw [hcollect]
  exact hnormalized outputFields
    (by
      intro field hfield
      have hfieldRaw :
          field ∈
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (rawBlock ++ suffix)) := by
        rw [hcollect]
        exact hfield
      apply hfresh field
      simpa [rawBlock, List.append_assoc] using hfieldRaw)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_of_allOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues
        (completionDepth + 1) parentType source middle) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) :=
  VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
    resolvers variableValues completionDepth parentType source first later
    middle hsameResponse hlaterLookup hnotMiddle
    (VisitSubfieldsFlatCollectsFreshPrefixes.of_allOutputs schema resolvers
      variableValues (completionDepth + 1) parentType source middle hmiddle)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix))
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle)
    (hsuffix :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source suffix) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later] ++ suffix) := by
  have hblock :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
      resolvers variableValues completionDepth parentType source first later
      middle hsameResponse hlaterLookup hnotMiddle hmiddle
  simpa [List.append_assoc] using
    VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint schema
      resolvers variableValues (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later])
      suffix hdisjoint hblock hsuffix

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_headDisjointTrees
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix))
    (hmiddle :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source middle)
    (hsuffix :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source suffix) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later] ++ suffix) :=
  VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
    schema resolvers variableValues completionDepth parentType source first later
    middle suffix hsameResponse hlaterLookup hnotMiddle hdisjoint
    (VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source middle
      hmiddle)
    (VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source suffix
      hsuffix)

inductive FreshPrefixSelectionPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    List Selection -> Prop where
  | nil :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source []
  | appendDisjoint (left right : List Selection) :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source left ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source right ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          right) ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source (left ++ right)
  | sameGroup (responseName : Name) (fields : List ExecutableField) :
      (∀ field, field ∈ fields -> field.responseName = responseName) ->
      (∀ field, field ∈ fields -> field.parentType = parentType) ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source (executableFieldSelections fields)
  | duplicateFieldBlockNormalize
      (first later : ExecutableField) (middle suffix : List Selection) :
      later.responseName = first.responseName ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source middle ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++ suffix) ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) ++ suffix)
  | consDisjoint
      (selection : Selection) (rest : List Selection) :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source [selection] ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source rest ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [selection])
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rest) ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source (selection :: rest)
  | duplicateFieldBlock
      (first later : ExecutableField) (middle suffix : List Selection) :
      later.responseName = first.responseName ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix) ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source middle ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source suffix ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later] ++ suffix)

inductive FreshPrefixSelectionDerivation
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    List Selection -> Prop where
  | nil :
      FreshPrefixSelectionDerivation schema variableValues parentType source []
  | appendDisjoint (left right : List Selection) :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        left ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        right ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          right) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (left ++ right)
  | sameGroup (responseName : Name) (fields : List ExecutableField) :
      (∀ field, field ∈ fields -> field.responseName = responseName) ->
      (∀ field, field ∈ fields -> field.parentType = parentType) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections fields)
  | inlineFragmentNone (directives : List DirectiveApplication)
      (selectionSet : List Selection) :
      (selectionDirectivesAllowBool variableValues directives = true ->
        FreshPrefixSelectionDerivation schema variableValues parentType source
          selectionSet) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        [.inlineFragment none directives selectionSet]
  | inlineFragmentSome (typeCondition : Name)
      (directives : List DirectiveApplication) (selectionSet : List Selection) :
      (selectionDirectivesAllowBool variableValues directives = true ->
        doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
          FreshPrefixSelectionDerivation schema variableValues parentType source
            selectionSet) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        [.inlineFragment (some typeCondition) directives selectionSet]
  | duplicateFieldBlockNormalize
      (first later : ExecutableField) (middle suffix : List Selection) :
      later.responseName = first.responseName ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        middle ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++ suffix) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        ((executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) ++ suffix)
  | consHeadDisjoint
      (selection : Selection) (rest : List Selection) :
      SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
        source selection ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        rest ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [selection])
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rest) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (selection :: rest)
  | duplicateFieldBlock
      (first later : ExecutableField) (middle suffix : List Selection) :
      later.responseName = first.responseName ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        middle ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        suffix ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later] ++ suffix)

namespace FreshPrefixSelectionDerivation

theorem single_of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection)
    (htree :
      SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
        source selection) :
    FreshPrefixSelectionDerivation schema variableValues parentType source
      [selection] :=
  .consHeadDisjoint selection []
    htree
    .nil
    (by
      intro responseName _hleft hright
      simp [GraphQL.Execution.collectFields] at hright)

theorem of_headDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ selectionSet,
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
        source selectionSet ->
      (∀ selection, selection ∈ selectionSet ->
        SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
          source selection) ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        selectionSet
  | [], _hdisjoint, _hchildren => .nil
  | selection :: rest, hdisjoint, hchildren => by
      rcases hdisjoint with ⟨hheadDisjoint, hrestDisjoint⟩
      exact .consHeadDisjoint selection rest
        (hchildren selection (by simp))
        (of_headDisjoint schema variableValues parentType source rest
          hrestDisjoint
          (by
            intro candidate hcandidate
            exact hchildren candidate (by simp [hcandidate])))
        hheadDisjoint

theorem of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (htree :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source selectionSet) :
    FreshPrefixSelectionDerivation schema variableValues parentType source
      selectionSet := by
  have htree' :
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source selectionSet
        ∧ ∀ selection, selection ∈ selectionSet ->
            SelectionCollectFieldsHeadDisjointTree schema variableValues
              parentType source selection := by
    simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree
  rcases htree' with ⟨hdisjoint, hchildren⟩
  exact of_headDisjoint schema variableValues parentType source selectionSet
    hdisjoint hchildren

theorem duplicateFieldBlock_of_headDisjointTrees
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix))
    (hmiddle :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source middle)
    (hsuffix :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source suffix) :
    FreshPrefixSelectionDerivation schema variableValues parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later] ++ suffix) :=
  .duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
    hnotMiddle hdisjoint
    (of_headDisjointTree schema variableValues parentType source middle hmiddle)
    (of_headDisjointTree schema variableValues parentType source suffix hsuffix)

theorem duplicateFieldPair_of_headDisjointMiddle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source middle) :
    FreshPrefixSelectionDerivation schema variableValues parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) := by
  simpa using
    duplicateFieldBlock_of_headDisjointTrees schema variableValues parentType
      source first later middle [] hsameResponse hlaterLookup hnotMiddle
      (by
        intro responseName _hleft hright
        simp [GraphQL.Execution.collectFields] at hright)
      hmiddle
      (by
        simp [SelectionSetCollectFieldsHeadDisjointTree,
          SelectionSetCollectFieldsHeadDisjoint])

def singletonExecutableGroups :
    List ExecutableField -> List (Name × List ExecutableField)
  | [] => []
  | field :: rest =>
      (field.responseName, [field]) :: singletonExecutableGroups rest

theorem collectedExecutableFields_singletonExecutableGroups :
    ∀ fields,
      collectedExecutableFields (singletonExecutableGroups fields) = fields
  | [] => by
      simp [singletonExecutableGroups, collectedExecutableFields]
  | field :: rest => by
      simp [singletonExecutableGroups, collectedExecutableFields,
        collectedExecutableFields_singletonExecutableGroups rest]

theorem singletonExecutableGroups_mem_cons :
    ∀ {fields : List ExecutableField} {responseName : Name}
      {field : ExecutableField} {fieldsTail : List ExecutableField},
      (responseName, field :: fieldsTail) ∈
        singletonExecutableGroups fields ->
        field ∈ fields ∧ fieldsTail = []
  | [], _responseName, _field, _fieldsTail, hmem => by
      simp [singletonExecutableGroups] at hmem
  | head :: rest, responseName, field, fieldsTail, hmem => by
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        cases fieldsTail with
        | nil =>
            simp at hfields
            subst field
            exact ⟨by simp, rfl⟩
        | cons tailHead tailRest =>
            simp at hfields
      · rcases singletonExecutableGroups_mem_cons htail with
          ⟨hfield, hfieldsTail⟩
        exact ⟨by simp [hfield], hfieldsTail⟩

theorem singletonExecutableGroups_map_fst :
    ∀ fields,
      (singletonExecutableGroups fields).map Prod.fst =
        fields.map (fun field => field.responseName)
  | [] => by
      simp [singletonExecutableGroups]
  | field :: rest => by
      simp [singletonExecutableGroups, singletonExecutableGroups_map_fst rest]

theorem pairKeysNodup_singletonExecutableGroups
    {fields : List ExecutableField} :
    (fields.map (fun field => field.responseName)).Nodup ->
      PairKeysNodup (singletonExecutableGroups fields) := by
  intro hnodup
  simpa [PairKeysNodup, singletonExecutableGroups_map_fst] using hnodup

theorem collectedGroupsFieldsNonempty_singletonExecutableGroups
    (fields : List ExecutableField) :
    CollectedGroupsFieldsNonempty (singletonExecutableGroups fields) := by
  intro responseName groupFields hmem
  induction fields with
  | nil =>
      simp [singletonExecutableGroups] at hmem
  | cons field rest ih =>
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponse, hfields⟩
        simp [hfields]
      · exact ih htail

theorem collectedGroupsResponseName_singletonExecutableGroups
    (fields : List ExecutableField) :
    CollectedGroupsResponseName (singletonExecutableGroups fields) := by
  intro responseName groupFields hmem
  induction fields generalizing responseName groupFields with
  | nil =>
      simp [singletonExecutableGroups] at hmem
  | cons field rest ih =>
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponse, hfields⟩
        subst responseName
        subst groupFields
        intro candidate hcandidate
        have hcandidateEq : candidate = field := by
          simpa using hcandidate
        subst candidate
        rfl
      · exact ih responseName groupFields htail

theorem collectedGroupsParent_singletonExecutableGroups
    {parentType : Name} {fields : List ExecutableField} :
    ExecutableFieldsParent parentType fields ->
      CollectedGroupsParent parentType (singletonExecutableGroups fields) := by
  intro hparents responseName groupFields hmem
  induction fields generalizing responseName groupFields with
  | nil =>
      simp [singletonExecutableGroups] at hmem
  | cons field rest ih =>
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponse, hfields⟩
        subst groupFields
        intro candidate hcandidate
        have hcandidateEq : candidate = field := by
          simpa using hcandidate
        subst candidate
        exact hparents field (by simp)
      · exact ih
          (by
            intro restField hrestField
            exact hparents restField (by simp [hrestField]))
          responseName groupFields htail

theorem ExecutableFieldsParent_collectedExecutableFields
    {parentType : Name} :
    ∀ {groups : List (Name × List ExecutableField)},
      CollectedGroupsParent parentType groups ->
        ExecutableFieldsParent parentType
          (collectedExecutableFields groups)
  | [], _hparents => by
      intro field hfield
      simp [collectedExecutableFields] at hfield
  | (responseName, fields) :: rest, hparents => by
      intro field hfield
      simp [collectedExecutableFields] at hfield
      rcases hfield with hfield | hfield
      · exact hparents responseName fields (by simp) field hfield
      · exact
          ExecutableFieldsParent_collectedExecutableFields
            (CollectedGroupsParent_tail hparents) field hfield

theorem collectFields_executableFieldSelections_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (responseName : Name) :
    responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields)).map Prod.fst ↔
      responseName ∈ fields.map (fun field => field.responseName) := by
  induction fields with
  | nil =>
      simp [executableFieldSelections, GraphQL.Execution.collectFields]
  | cons field rest ih =>
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection field) =
            [(field.responseName,
              [executableField parentType field.responseName field.fieldName
                field.arguments field.selectionSet])] := by
        simp [executableFieldSelection, executableField,
          GraphQL.Execution.collectSelection, selectionDirectivesAllowBool_empty]
      simp only [executableFieldSelections, List.map_cons,
        GraphQL.Execution.collectFields]
      rw [hhead]
      rw [mergeExecutableGroups_key_mem]
      constructor
      · intro hmem
        rcases hmem with hheadMem | htailMem
        · have hheadEq : responseName = field.responseName := by
            simpa using hheadMem
          simp [hheadEq]
        · have htail : responseName ∈ rest.map (fun field => field.responseName) :=
            ih.mp htailMem
          simp [htail]
      · intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hheadMem | htailMem
        · left
          simp [hheadMem]
        · right
          exact ih.mpr htailMem

theorem executableFields_first_responseName_split
    (responseName : Name) :
    ∀ fields : List ExecutableField,
      responseName ∈ fields.map (fun field => field.responseName) ->
        ∃ middle later suffix,
          fields = middle ++ later :: suffix ∧
          later.responseName = responseName ∧
          responseName ∉ middle.map (fun field => field.responseName)
  | [], hmem => by
      simp at hmem
  | field :: rest, hmem => by
      by_cases hfield : field.responseName = responseName
      · exact ⟨[], field, rest, by simp, hfield, by simp⟩
      · have hrest :
            responseName ∈ rest.map (fun field => field.responseName) := by
          simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · exact False.elim (hfield hhead.symm)
          · exact htail
        rcases executableFields_first_responseName_split responseName rest
          hrest with
          ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
        refine ⟨field :: middle, later, suffix, ?_, hlater, ?_⟩
        · simp [hsplit]
        · intro hmemMiddle
          simp only [List.map_cons, List.mem_cons] at hmemMiddle
          rcases hmemMiddle with hhead | hmiddle
          · exact hfield hhead.symm
          · exact hnotMiddle hmiddle

theorem executableFieldConsFresh
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (hfresh :
      field.responseName ∉ rest.map (fun field => field.responseName))
    (hrest :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections rest)) :
    FreshPrefixSelectionDerivation schema variableValues parentType source
      (executableFieldSelections (field :: rest)) := by
  simpa [executableFieldSelections] using
    FreshPrefixSelectionDerivation.consHeadDisjoint
      (schema := schema) (variableValues := variableValues)
      (parentType := parentType) (source := source)
      (selection := executableFieldSelection field)
      (rest := executableFieldSelections rest)
      (by simp [executableFieldSelection,
        SelectionCollectFieldsHeadDisjointTree])
      hrest
      (by
        intro responseName hhead htail
        have hheadEq : responseName = field.responseName := by
          simpa [GraphQL.Execution.collectFields,
            GraphQL.Execution.collectSelection,
            GraphQL.Execution.mergeExecutableGroups,
            executableFieldSelection, executableField,
            selectionDirectivesAllowBool_empty] using hhead
        have htailName :
            responseName ∈ rest.map (fun field => field.responseName) :=
          (collectFields_executableFieldSelections_key_mem schema
            variableValues parentType source rest responseName).mp htail
        exact hfresh (by simpa [hheadEq] using htailName))

theorem of_collectedGroups
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ groups,
      PairKeysNodup groups ->
      CollectedGroupsFieldsNonempty groups ->
      CollectedGroupsResponseName groups ->
      CollectedGroupsParent parentType groups ->
        FreshPrefixSelectionDerivation schema variableValues parentType source
          (executableFieldSelections (collectedExecutableFields groups))
  | [], _hnodup, _hnonempty, _hresponses, _hparents => by
      simpa [collectedExecutableFields, executableFieldSelections] using
        (FreshPrefixSelectionDerivation.nil
          (schema := schema) (variableValues := variableValues)
          (parentType := parentType) (source := source))
  | (responseName, fields) :: rest, hnodup, hnonempty, hresponses, hparents =>
      by
        have hrestNodup : PairKeysNodup rest :=
          PairKeysNodup.tail hnodup
        have hrestNonempty : CollectedGroupsFieldsNonempty rest :=
          CollectedGroupsFieldsNonempty_tail hnonempty
        have hrestResponses : CollectedGroupsResponseName rest :=
          CollectedGroupsResponseName_tail hresponses
        have hrestParents : CollectedGroupsParent parentType rest :=
          CollectedGroupsParent_tail hparents
        have hfieldsNonempty : fields ≠ [] :=
          hnonempty responseName fields (by simp)
        cases fields with
        | nil =>
            exact False.elim (hfieldsNonempty rfl)
        | cons field fieldsTail =>
            have hheadResponse :
                ExecutableFieldsResponseName responseName
                  (field :: fieldsTail) :=
              hresponses responseName (field :: fieldsTail) (by simp)
            have hheadParent :
                ExecutableFieldsParent parentType (field :: fieldsTail) :=
              hparents responseName (field :: fieldsTail) (by simp)
            have hheadCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
                [(responseName, field :: fieldsTail)] :=
              collectFields_executableFieldSelections_same_group schema
                variableValues parentType source responseName
                (field :: fieldsTail) hheadResponse hheadParent
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) =
                rest :=
              collectFields_executableFieldSelections_collectedExecutableFields
                schema variableValues parentType source rest hrestNodup
                hrestNonempty hrestResponses hrestParents
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
              intro candidate hleft hright
              rw [hheadCollect] at hleft
              rw [hrestCollect] at hright
              exact
                executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
                  hnodup candidate hleft hright
            have hhead :
                FreshPrefixSelectionDerivation schema variableValues parentType
                  source (executableFieldSelections (field :: fieldsTail)) :=
              .sameGroup responseName (field :: fieldsTail) hheadResponse
                hheadParent
            have htail :
                FreshPrefixSelectionDerivation schema variableValues parentType
                  source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) :=
              of_collectedGroups schema variableValues parentType source rest
                hrestNodup hrestNonempty hrestResponses hrestParents
            simpa [collectedExecutableFields, executableFieldSelections] using
              FreshPrefixSelectionDerivation.appendDisjoint
                (schema := schema) (variableValues := variableValues)
                (parentType := parentType) (source := source)
                (executableFieldSelections (field :: fieldsTail))
                (executableFieldSelections (collectedExecutableFields rest))
                hhead htail hdisjoint

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    FreshPrefixSelectionDerivation schema variableValues parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :=
  of_collectedGroups schema variableValues parentType source
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet))
    (collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet)
    (collectFields_responseName schema variableValues parentType source
      selectionSet)
    (collectFields_parent schema variableValues parentType source selectionSet)

theorem of_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields) :
    FreshPrefixSelectionDerivation schema variableValues parentType source
      (executableFieldSelections fields) := by
  simpa [collectedExecutableFields_singletonExecutableGroups] using
    of_collectedGroups schema variableValues parentType source
      (singletonExecutableGroups fields)
      (pairKeysNodup_singletonExecutableGroups hnodup)
      (collectedGroupsFieldsNonempty_singletonExecutableGroups fields)
      (collectedGroupsResponseName_singletonExecutableGroups fields)
      (collectedGroupsParent_singletonExecutableGroups hparents)

theorem collectFields_executableFieldSelections_singletonExecutableGroups
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields) :
    GraphQL.Execution.collectFields schema variableValues parentType source
      (executableFieldSelections fields) =
    singletonExecutableGroups fields := by
  simpa [collectedExecutableFields_singletonExecutableGroups] using
    collectFields_executableFieldSelections_collectedExecutableFields schema
      variableValues parentType source (singletonExecutableGroups fields)
      (pairKeysNodup_singletonExecutableGroups hnodup)
      (collectedGroupsFieldsNonempty_singletonExecutableGroups fields)
      (collectedGroupsResponseName_singletonExecutableGroups fields)
      (collectedGroupsParent_singletonExecutableGroups hparents)

theorem collectFields_executableFieldSelections_mem_cons
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {fields : List ExecutableField}
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    {responseName : Name} {field : ExecutableField}
    {fieldsTail : List ExecutableField}
    (hgroup :
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields)) :
    field ∈ fields ∧ fieldsTail = [] := by
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields) =
        singletonExecutableGroups fields :=
    collectFields_executableFieldSelections_singletonExecutableGroups schema
      variableValues parentType source fields hnodup hparents
  have hgroupSingle :
      (responseName, field :: fieldsTail) ∈
        singletonExecutableGroups fields := by
    rwa [hcollect] at hgroup
  exact singletonExecutableGroups_mem_cons hgroupSingle

theorem collectFields_executableFieldSelections_prefix_empty
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {fields : List ExecutableField}
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    {responseName : Name} {field : ExecutableField}
    {fieldsTail prefixTail : List ExecutableField}
    (hgroup :
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields))
    (hprefix :
      ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fieldsTail) :
    field ∈ fields ∧ fieldsTail = [] ∧ prefixTail = [] := by
  rcases
      collectFields_executableFieldSelections_mem_cons schema variableValues
        parentType source hnodup hparents hgroup with
    ⟨hfield, hfieldsTail⟩
  have hprefixTail : prefixTail = [] := by
    cases prefixTail with
    | nil => rfl
    | cons head tail =>
        have hhead : head ∈ fieldsTail := hprefix head (by simp)
        simp [hfieldsTail] at hhead
  exact ⟨hfield, hfieldsTail, hprefixTail⟩

def executableFieldOfSelection (parentType : Name) : Selection -> ExecutableField
  | .field responseName fieldName arguments _directives selectionSet =>
      { parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := selectionSet }
  | .inlineFragment _typeCondition _directives _selectionSet =>
      { parentType := parentType
        responseName := ""
        fieldName := ""
        arguments := []
        selectionSet := [] }

theorem executableFieldSelections_map_executableFieldOfSelection
    (parentType : Name) :
    ∀ selectionSet,
      NormalForm.selectionsAllFields selectionSet ->
      NormalForm.selectionSetDirectiveFree selectionSet ->
        executableFieldSelections
            (selectionSet.map (executableFieldOfSelection parentType))
          =
        selectionSet
  | [], _hall, _hfree => by
      simp [executableFieldSelections]
  | selection :: rest, hall, hfree => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have hrestFree : NormalForm.selectionSetDirectiveFree rest := by
        simpa [NormalForm.selectionSetDirectiveFree] using hfree.2
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hdirectives : directives = [] := by
            simpa [NormalForm.selectionSetDirectiveFree,
              NormalForm.selectionDirectiveFree] using hfree.1.1
          subst directives
          have hrestEq :
              List.map
                  (executableFieldSelection ∘
                    executableFieldOfSelection parentType) rest =
                rest := by
            simpa [executableFieldSelections, List.map_map,
              Function.comp_def] using
              executableFieldSelections_map_executableFieldOfSelection
                parentType rest hrestAll hrestFree
          simp [executableFieldSelections, executableFieldSelection,
            executableFieldOfSelection, hrestEq]
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem responseNames_map_executableFieldOfSelection
    (parentType : Name) :
    ∀ selectionSet,
      NormalForm.selectionsAllFields selectionSet ->
        selectionSet.filterMap Selection.responseName? =
          (selectionSet.map (fun selection =>
            (executableFieldOfSelection parentType selection).responseName))
  | [], _hall => by
      simp
  | selection :: rest, hall => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          simp [Selection.responseName?, executableFieldOfSelection,
            responseNames_map_executableFieldOfSelection parentType rest
              hrestAll]
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem responseNamesNodup_map_executableFieldOfSelection
    (parentType : Name) (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
      (selectionSet.map (fun selection =>
        (executableFieldOfSelection parentType selection).responseName)).Nodup := by
  intro hall hnodup
  have hnames :=
    responseNames_map_executableFieldOfSelection parentType selectionSet hall
  simpa [NormalForm.responseNamesNodup, hnames] using hnodup

theorem executableFieldsParent_map_executableFieldOfSelection
    (parentType : Name) (selectionSet : List Selection) :
    ExecutableFieldsParent parentType
      (selectionSet.map (executableFieldOfSelection parentType)) := by
  intro field hfield
  rcases List.mem_map.mp hfield with ⟨selection, _hselection, hfieldEq⟩
  subst field
  cases selection <;> rfl

theorem collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
    ∀ {responseName : Name} {field : ExecutableField}
      {fieldsTail prefixTail : List ExecutableField},
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fieldsTail) ->
        fieldsTail = [] ∧ prefixTail = [] := by
  intro hall hfree hnodup responseName field fieldsTail prefixTail hgroup
    hprefix
  let fields := selectionSet.map (executableFieldOfSelection parentType)
  have hselectionSet :
      executableFieldSelections fields = selectionSet := by
    exact executableFieldSelections_map_executableFieldOfSelection parentType
      selectionSet hall hfree
  have hfieldsNodup :
      (fields.map (fun field => field.responseName)).Nodup := by
    simpa [fields, List.map_map] using
      responseNamesNodup_map_executableFieldOfSelection parentType
        selectionSet hall hnodup
  have hparents : ExecutableFieldsParent parentType fields := by
    simpa [fields] using
      executableFieldsParent_map_executableFieldOfSelection parentType
        selectionSet
  have hgroup' :
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields) := by
    simpa [hselectionSet] using hgroup
  rcases
      collectFields_executableFieldSelections_prefix_empty schema
        variableValues parentType source hfieldsNodup hparents hgroup'
        hprefix with
    ⟨_hfield, hfieldsTail, hprefixTail⟩
  exact ⟨hfieldsTail, hprefixTail⟩

theorem collectFields_allFields_directiveFree_responseNamesNodup_field_mem_prefix_empty
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
    ∀ {responseName : Name} {field : ExecutableField}
      {fieldsTail prefixTail : List ExecutableField},
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fieldsTail) ->
        field ∈ selectionSet.map (executableFieldOfSelection parentType)
          ∧ fieldsTail = []
          ∧ prefixTail = [] := by
  intro hall hfree hnodup responseName field fieldsTail prefixTail hgroup
    hprefix
  let fields := selectionSet.map (executableFieldOfSelection parentType)
  have hselectionSet :
      executableFieldSelections fields = selectionSet := by
    exact executableFieldSelections_map_executableFieldOfSelection parentType
      selectionSet hall hfree
  have hfieldsNodup :
      (fields.map (fun field => field.responseName)).Nodup := by
    simpa [fields, List.map_map] using
      responseNamesNodup_map_executableFieldOfSelection parentType
        selectionSet hall hnodup
  have hparents : ExecutableFieldsParent parentType fields := by
    simpa [fields] using
      executableFieldsParent_map_executableFieldOfSelection parentType
        selectionSet
  have hgroup' :
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields) := by
    simpa [hselectionSet] using hgroup
  rcases
      collectFields_executableFieldSelections_prefix_empty schema
        variableValues parentType source hfieldsNodup hparents hgroup'
        hprefix with
    ⟨hfield, hfieldsTail, hprefixTail⟩
  exact ⟨by simpa [fields] using hfield, hfieldsTail, hprefixTail⟩

theorem fieldMerge_collectFields_parent_of_allFields
    (schema : Schema) (parentType : Name) :
    ∀ selectionSet scopedField,
      NormalForm.selectionsAllFields selectionSet ->
      scopedField ∈ FieldMerge.collectFields schema parentType selectionSet ->
        scopedField.parentType = parentType
  | [], scopedField, _hall, hmem => by
      simp [FieldMerge.collectFields] at hmem
  | selection :: rest, scopedField, hall, hmem => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              exact
                fieldMerge_collectFields_parent_of_allFields schema
                  parentType rest scopedField hrestAll hmem
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              rcases hmem with hhead | htail
              · subst scopedField
                rfl
              · exact
                  fieldMerge_collectFields_parent_of_allFields schema
                    parentType rest scopedField hrestAll htail
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

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
      have hrestAll : NormalForm.selectionsAllFields rest := by
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
          · exact
              selectionSetResponseNameFree_of_allFields_responseNamesNodup
                schema parentType responseName rest hrestAll hrestNotMem
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem collectFields_responseName_not_mem_of_allFields_responseNameFree
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) :
    ∀ selectionSet,
      NormalForm.selectionsAllFields selectionSet ->
      NormalForm.selectionSetResponseNameFree schema parentType responseName
        selectionSet ->
        responseName ∉
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet).map Prod.fst
  | [], _hall, _hfree => by
      simp [GraphQL.Execution.collectFields]
  | selection :: rest, hall, hfree => by
      have hheadField : Selection.isField selection := hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have hrestFree :
          NormalForm.selectionSetResponseNameFree schema parentType
            responseName rest :=
        NormalForm.selectionSetResponseNameFree_tail hfree
      have htailNotMem :
          responseName ∉
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest).map Prod.fst :=
        collectFields_responseName_not_mem_of_allFields_responseNameFree
          schema variableValues parentType source responseName rest hrestAll
          hrestFree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hheadFree := NormalForm.selectionSetResponseNameFree_head hfree
          have hfieldNe : fieldResponseName ≠ responseName := by
            simpa [NormalForm.selectionResponseNameFree] using hheadFree
          by_cases hallows :
              selectionDirectivesAllowBool variableValues directives = true
          · intro hmem
            have hparts :
                responseName = fieldResponseName ∨
                responseName ∈
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest).map Prod.fst := by
              have hmemMerge :
                  responseName ∈
                    (GraphQL.Execution.mergeExecutableGroups
                      (GraphQL.Execution.collectSelection schema
                        variableValues parentType source
                        (.field fieldResponseName fieldName arguments
                          directives selectionSet))
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source rest)).map Prod.fst := by
                simpa [GraphQL.Execution.collectFields] using hmem
              have hpartsRaw :=
                (mergeExecutableGroups_key_mem
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType source
                    (.field fieldResponseName fieldName arguments directives
                      selectionSet))
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest)
                  responseName).mp hmemMerge
              rcases hpartsRaw with hhead | htail
              · left
                simpa [GraphQL.Execution.collectSelection, hallows] using hhead
              · exact Or.inr htail
            rcases hparts with hhead | htail
            · exact hfieldNe hhead.symm
            · exact htailNotMem htail
          · have hskip :
                selectionDirectivesAllowBool variableValues directives =
                  false := by
              cases h :
                  selectionDirectivesAllowBool variableValues directives
              · rfl
              · contradiction
            intro hmem
            have hmemMerge :
                responseName ∈
                  (GraphQL.Execution.mergeExecutableGroups
                    (GraphQL.Execution.collectSelection schema variableValues
                      parentType source
                      (.field fieldResponseName fieldName arguments
                        directives selectionSet))
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source rest)).map Prod.fst := by
              simpa [GraphQL.Execution.collectFields] using hmem
            have hpartsRaw :=
              (mergeExecutableGroups_key_mem
                (GraphQL.Execution.collectSelection schema variableValues
                  parentType source
                  (.field fieldResponseName fieldName arguments directives
                    selectionSet))
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest)
                responseName).mp hmemMerge
            rcases hpartsRaw with hhead | htail
            · simp [GraphQL.Execution.collectSelection, hskip] at hhead
            · exact htailNotMem htail
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem scopedField_outputType_eq_fieldReturnType_of_identity_match
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (scopedField : FieldMerge.ScopedField)
    (field : ExecutableField) :
    Validation.selectionSetValid schema variableDefinitions parentType
      selectionSet ->
    scopedField ∈ FieldMerge.collectFields schema parentType selectionSet ->
    field.parentType = scopedField.parentType ->
    ScopedFieldMatchesExecutableIdentity scopedField field ->
      scopedField.outputType.namedType =
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName) := by
  intro hvalid hscopedMem hparent hmatch
  rcases hmatch with
    ⟨_hresponseName, hfieldName, _harguments, _hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid
        schema variableDefinitions parentType selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, hlookup, houtput, _hfieldSelectionSet⟩
  have hreturn :
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName) = fieldDefinition.outputType.namedType := by
    simp [Schema.fieldReturnType?, hparent, ← hfieldName, hlookup]
  rw [hreturn]
  exact (congrArg TypeRef.namedType houtput).symm

theorem of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
      FreshPrefixSelectionDerivation schema variableValues parentType source
        selectionSet := by
  intro hall hfree hnodup
  let fields := selectionSet.map (executableFieldOfSelection parentType)
  have hselectionSet :
      executableFieldSelections fields = selectionSet := by
    exact executableFieldSelections_map_executableFieldOfSelection parentType
      selectionSet hall hfree
  have hfieldsNodup :
      (fields.map (fun field => field.responseName)).Nodup := by
    simpa [fields, List.map_map] using
      responseNamesNodup_map_executableFieldOfSelection parentType selectionSet
        hall hnodup
  have hparents : ExecutableFieldsParent parentType fields := by
    simpa [fields] using
      executableFieldsParent_map_executableFieldOfSelection parentType
        selectionSet
  have hderivation :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections fields) :=
    of_executableFieldSelections_responseNamesNodup schema variableValues
      parentType source fields hfieldsNodup hparents
  rwa [hselectionSet] at hderivation

theorem selectionSetCollectFieldsHeadDisjointTree_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields) :
    SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
      source (executableFieldSelections fields) := by
  have htree :
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source (executableFieldSelections fields)
        ∧ ∀ selection, selection ∈ executableFieldSelections fields ->
            SelectionCollectFieldsHeadDisjointTree schema variableValues
              parentType source selection := by
    constructor
    · induction fields with
      | nil =>
          simp [executableFieldSelections, SelectionSetCollectFieldsHeadDisjoint]
      | cons field rest ih =>
          simp [executableFieldSelections, SelectionSetCollectFieldsHeadDisjoint]
          constructor
          · intro responseName hleft hright
            have hheadParent : field.parentType = parentType :=
              hparents field (by simp)
            have hrestParents : ExecutableFieldsParent parentType rest := by
              intro restField hrestField
              exact hparents restField (by simp [hrestField])
            have hrestNodup :
                (rest.map (fun field => field.responseName)).Nodup := by
              simpa using (List.nodup_cons.mp hnodup).2
            have hheadCollect :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source (executableFieldSelections [field]) =
                  singletonExecutableGroups [field] :=
              collectFields_executableFieldSelections_singletonExecutableGroups
                schema variableValues parentType source [field]
                (by simp)
                (ExecutableFieldsParent_singleton parentType field hheadParent)
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source (executableFieldSelections rest) =
                  singletonExecutableGroups rest :=
              collectFields_executableFieldSelections_singletonExecutableGroups
                schema variableValues parentType source rest hrestNodup
                hrestParents
            have hheadCollect' :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source [executableFieldSelection field] =
                  singletonExecutableGroups [field] := by
              simpa [executableFieldSelections] using hheadCollect
            have hrestCollect' :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source (List.map executableFieldSelection rest) =
                  singletonExecutableGroups rest := by
              simpa [executableFieldSelections] using hrestCollect
            rw [hheadCollect'] at hleft
            rw [hrestCollect'] at hright
            have hleftEq : responseName = field.responseName := by
              simpa [singletonExecutableGroups] using hleft
            have hrightMem :
                responseName ∈ rest.map (fun field => field.responseName) := by
              simpa [singletonExecutableGroups_map_fst] using hright
            exact (List.nodup_cons.mp hnodup).1 (by
              simpa [hleftEq] using hrightMem)
          · exact ih (by simpa using (List.nodup_cons.mp hnodup).2)
              (by
                intro restField hrestField
                exact hparents restField (by simp [hrestField]))
    · intro selection hselection
      rcases List.mem_map.mp hselection with ⟨field, _hfield, hselectionEq⟩
      cases hselectionEq
      simp [executableFieldSelection, SelectionCollectFieldsHeadDisjointTree]
  simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree

end FreshPrefixSelectionDerivation

theorem collectFields_executableFieldSelections_single_prefix_duplicate_fresh_middle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List ExecutableField)
    (hsameResponse : later.responseName = first.responseName)
    (hmiddleNodup :
      (middle.map (fun field => field.responseName)).Nodup)
    (hmiddleParents :
      ∀ field, field ∈ middle -> field.parentType = parentType)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName)) :
    GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections ([first] ++ (middle ++ [later]))) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections ([first] ++ [later] ++ middle)) := by
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (executableFieldSelections middle)).map Prod.fst := by
    intro hmem
    have hfieldMem :
        first.responseName ∈ middle.map (fun field => field.responseName) :=
      (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middle first.responseName).mp
        hmem
    exact hnotMiddle (by simpa [hsameResponse] using hfieldMem)
  have hmiddleCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections middle) =
        FreshPrefixSelectionDerivation.singletonExecutableGroups middle :=
    FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_singletonExecutableGroups
      schema variableValues parentType source middle hmiddleNodup hmiddleParents
  have hdup :=
    collectFields_duplicate_field_middle_append_eq_collected_middle schema
      variableValues parentType source first later
      (executableFieldSelections middle) [] hsameResponse hnotMiddleCollect
  rw [hmiddleCollect] at hdup
  simpa [executableFieldSelections, List.append_assoc,
    FreshPrefixSelectionDerivation.collectedExecutableFields_singletonExecutableGroups]
    using hdup

namespace FreshPrefixSelectionPlan

theorem freshFlat
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} {selectionSet} :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source selectionSet ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source selectionSet := by
  intro plan
  induction plan with
  | nil =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_nil schema resolvers
        variableValues (completionDepth + 1) parentType source
  | appendDisjoint left right hleft hright hdisjoint ihleft ihright =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint
        schema resolvers variableValues (completionDepth + 1) parentType source
        left right hdisjoint ihleft ihright
  | sameGroup responseName fields hresponse hparent =>
      exact
        VisitSubfieldsFlatCollectsFreshPrefixes_executableFieldSelections_same_group
          schema resolvers variableValues (completionDepth + 1) parentType
          source responseName fields hresponse hparent
  | duplicateFieldBlockNormalize first later middle suffix hsameResponse
      hlaterLookup hnotMiddle hmiddle hnormalized ihmiddle ihnormalized =>
      exact
        VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_normalized
          schema resolvers variableValues completionDepth parentType source
          first later middle suffix hsameResponse hlaterLookup hnotMiddle
          ihmiddle ihnormalized
  | consDisjoint selection rest hselection hrest hdisjoint ihrest =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint schema
        resolvers variableValues (completionDepth + 1) parentType source
        selection rest hdisjoint hselection ihrest
  | duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
      hnotMiddle hdisjoint hmiddle hsuffix ihmiddle ihsuffix =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
        schema resolvers variableValues completionDepth parentType source first
        later middle suffix hsameResponse hlaterLookup hnotMiddle hdisjoint
        ihmiddle ihsuffix

theorem single_of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection)
    (htree :
      SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
        source selection) :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source [selection] :=
  .consDisjoint selection []
    (VisitSubfieldsFlatCollectsFreshPrefixes_single_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source
      selection htree)
    .nil
    (by
      intro responseName _hleft hright
      simp [GraphQL.Execution.collectFields] at hright)

theorem of_headDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ selectionSet,
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
        source selectionSet ->
      (∀ selection, selection ∈ selectionSet ->
        FreshPrefixSelectionPlan schema resolvers variableValues
          completionDepth parentType source [selection]) ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source selectionSet
  | [], _hdisjoint, _hsingle => .nil
  | selection :: rest, hdisjoint, hsingle => by
      rcases hdisjoint with ⟨hheadDisjoint, hrestDisjoint⟩
      exact .consDisjoint selection rest
        (freshFlat (hsingle selection (by simp)))
        (of_headDisjoint schema resolvers variableValues completionDepth
          parentType source rest hrestDisjoint
          (by
            intro candidate hcandidate
            exact hsingle candidate (by simp [hcandidate])))
        hheadDisjoint

theorem of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (htree :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source selectionSet) :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source selectionSet := by
  have htree' :
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source selectionSet
        ∧ ∀ selection, selection ∈ selectionSet ->
            SelectionCollectFieldsHeadDisjointTree schema variableValues
              parentType source selection := by
    simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree
  rcases htree' with ⟨hdisjoint, hchildren⟩
  exact of_headDisjoint schema resolvers variableValues completionDepth
    parentType source selectionSet hdisjoint
    (by
      intro selection hselection
      exact single_of_headDisjointTree schema resolvers variableValues
        completionDepth parentType source selection
        (hchildren selection hselection))

theorem duplicateFieldBlock_of_headDisjointTrees
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix))
    (hmiddle :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source middle)
    (hsuffix :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source suffix) :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later] ++ suffix) :=
  .duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
    hnotMiddle hdisjoint
    (of_headDisjointTree schema resolvers variableValues completionDepth
      parentType source middle hmiddle)
    (of_headDisjointTree schema resolvers variableValues completionDepth
      parentType source suffix hsuffix)

theorem duplicateFieldPair_of_headDisjointMiddle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source middle) :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) := by
  simpa using
    duplicateFieldBlock_of_headDisjointTrees schema resolvers variableValues
      completionDepth parentType source first later middle [] hsameResponse
      hlaterLookup hnotMiddle
      (by
        intro responseName _hleft hright
        simp [GraphQL.Execution.collectFields] at hright)
      hmiddle
      (by
        simp [SelectionSetCollectFieldsHeadDisjointTree,
          SelectionSetCollectFieldsHeadDisjoint])

theorem of_collectedGroups
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ groups,
      PairKeysNodup groups ->
      CollectedGroupsFieldsNonempty groups ->
      CollectedGroupsResponseName groups ->
      CollectedGroupsParent parentType groups ->
        FreshPrefixSelectionPlan schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections (collectedExecutableFields groups))
  | [], _hnodup, _hnonempty, _hresponses, _hparents => by
      simpa [collectedExecutableFields, executableFieldSelections] using
        (FreshPrefixSelectionPlan.nil
          (schema := schema) (resolvers := resolvers)
          (variableValues := variableValues)
          (completionDepth := completionDepth)
          (parentType := parentType) (source := source))
  | (responseName, fields) :: rest, hnodup, hnonempty, hresponses, hparents =>
      by
        have hrestNodup : PairKeysNodup rest :=
          PairKeysNodup.tail hnodup
        have hrestNonempty : CollectedGroupsFieldsNonempty rest :=
          CollectedGroupsFieldsNonempty_tail hnonempty
        have hrestResponses : CollectedGroupsResponseName rest :=
          CollectedGroupsResponseName_tail hresponses
        have hrestParents : CollectedGroupsParent parentType rest :=
          CollectedGroupsParent_tail hparents
        have hfieldsNonempty : fields ≠ [] :=
          hnonempty responseName fields (by simp)
        cases fields with
        | nil =>
            exact False.elim (hfieldsNonempty rfl)
        | cons field fieldsTail =>
            have hheadResponse :
                ExecutableFieldsResponseName responseName
                  (field :: fieldsTail) :=
              hresponses responseName (field :: fieldsTail) (by simp)
            have hheadParent :
                ExecutableFieldsParent parentType (field :: fieldsTail) :=
              hparents responseName (field :: fieldsTail) (by simp)
            have hheadCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
                [(responseName, field :: fieldsTail)] :=
              collectFields_executableFieldSelections_same_group schema
                variableValues parentType source responseName
                (field :: fieldsTail) hheadResponse hheadParent
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) =
                rest :=
              collectFields_executableFieldSelections_collectedExecutableFields
                schema variableValues parentType source rest hrestNodup
                hrestNonempty hrestResponses hrestParents
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
              intro candidate hleft hright
              rw [hheadCollect] at hleft
              rw [hrestCollect] at hright
              exact
                executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
                  hnodup candidate hleft hright
            have hhead :
                FreshPrefixSelectionPlan schema resolvers variableValues
                  completionDepth parentType source
                  (executableFieldSelections (field :: fieldsTail)) :=
              .sameGroup responseName (field :: fieldsTail) hheadResponse
                hheadParent
            have htail :
                FreshPrefixSelectionPlan schema resolvers variableValues
                  completionDepth parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) :=
              of_collectedGroups schema resolvers variableValues completionDepth
                parentType source rest hrestNodup hrestNonempty
                hrestResponses hrestParents
            simpa [collectedExecutableFields, executableFieldSelections] using
              FreshPrefixSelectionPlan.appendDisjoint
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth)
                (parentType := parentType) (source := source)
                (executableFieldSelections (field :: fieldsTail))
                (executableFieldSelections (collectedExecutableFields rest))
                hhead htail hdisjoint

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :=
  of_collectedGroups schema resolvers variableValues completionDepth parentType
    source
    (GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet)
    (PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet))
    (collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet)
    (collectFields_responseName schema variableValues parentType source
      selectionSet)
    (collectFields_parent schema variableValues parentType source selectionSet)

theorem duplicateFieldBlockNormalizePlan_of_headDisjointSuffix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hparents : ExecutableFieldsParent parentType [first, later])
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix))
    (hsuffix :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source suffix) :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source
      ((executableFieldSelections [first, later] ++
          executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle))) ++
        suffix) := by
  let collectedMiddle :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle))
  let normalizedBlock := executableFieldSelections [first, later] ++
    collectedMiddle
  have hpairResponses :
      ExecutableFieldsResponseName first.responseName [first, later] := by
    intro field hfield
    simp at hfield
    rcases hfield with hfield | hfield
    · subst field
      rfl
    · subst field
      exact hsameResponse
  have hpairCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first, later]) =
        [(first.responseName, [first, later])] :=
    collectFields_executableFieldSelections_same_group schema variableValues
      parentType source first.responseName [first, later] hpairResponses
      hparents
  have hmiddleCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle =
        GraphQL.Execution.collectFields schema variableValues parentType source
          middle := by
    dsimp [collectedMiddle]
    exact
      collectFields_executableFieldSelections_collectedExecutableFields schema
        variableValues parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (PairKeysNodup_of_executableGroupNamesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source middle))
        (collectFields_fieldsNonempty schema variableValues parentType source
          middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        (collectFields_parent schema variableValues parentType source middle)
  have hpairMiddleDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first, later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle) := by
    intro responseName hleft hright
    rw [hpairCollect] at hleft
    rw [hmiddleCollect] at hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  have hnormalizedBlockPlan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source normalizedBlock :=
    FreshPrefixSelectionPlan.appendDisjoint
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues)
      (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      (executableFieldSelections [first, later])
      collectedMiddle
      (.sameGroup first.responseName [first, later] hpairResponses hparents)
      (of_collectedCollectFields schema resolvers variableValues
        completionDepth parentType source middle)
      hpairMiddleDisjoint
  have hblockCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    have hcollect :=
      collectFields_duplicate_field_middle_append_eq_collected_middle schema
        variableValues parentType source first later middle [] hsameResponse
        hnotMiddle
    simpa [normalizedBlock, collectedMiddle] using hcollect
  have hblockSuffixDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix) := by
    intro responseName hleft hright
    exact hdisjoint responseName (by rwa [hblockCollect]) hright
  exact
    FreshPrefixSelectionPlan.appendDisjoint
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues)
      (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      normalizedBlock suffix hnormalizedBlockPlan
      (of_headDisjointTree schema resolvers variableValues completionDepth
        parentType source suffix hsuffix)
      hblockSuffixDisjoint

theorem of_derivation
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ {selectionSet},
      FreshPrefixSelectionDerivation schema variableValues parentType source
        selectionSet ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source selectionSet
  | _, FreshPrefixSelectionDerivation.nil => .nil
  | _, FreshPrefixSelectionDerivation.appendDisjoint left right hleft hright
        hdisjoint =>
      .appendDisjoint left right
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hleft)
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hright)
        hdisjoint
  | _, FreshPrefixSelectionDerivation.sameGroup responseName fields hresponse
        hparent =>
      .sameGroup responseName fields hresponse hparent
  | _, FreshPrefixSelectionDerivation.inlineFragmentNone directives
        selectionSet hselectionSet =>
      .consDisjoint (.inlineFragment none directives selectionSet) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          directives selectionSet
          (by
            intro hallowed
            exact freshFlat
              (of_derivation schema resolvers variableValues completionDepth
                parentType source (hselectionSet hallowed))))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)
  | _, FreshPrefixSelectionDerivation.inlineFragmentSome typeCondition
        directives selectionSet hselectionSet =>
      .consDisjoint
        (.inlineFragment (some typeCondition) directives selectionSet) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          typeCondition directives selectionSet
          (by
            intro hallowed happly
            exact freshFlat
              (of_derivation schema resolvers variableValues completionDepth
                parentType source (hselectionSet hallowed happly))))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)
  | _, FreshPrefixSelectionDerivation.duplicateFieldBlockNormalize first later
        middle suffix hsameResponse hlaterLookup hnotMiddle hmiddle hnormalized =>
      .duplicateFieldBlockNormalize first later middle suffix hsameResponse
        hlaterLookup hnotMiddle
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hmiddle)
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hnormalized)
  | _, FreshPrefixSelectionDerivation.consHeadDisjoint selection rest hselection
        hrest hdisjoint =>
      .consDisjoint selection rest
        (freshFlat
          (single_of_headDisjointTree schema resolvers variableValues
            completionDepth parentType source selection hselection))
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hrest)
        hdisjoint
  | _, FreshPrefixSelectionDerivation.duplicateFieldBlock first later middle
        suffix hsameResponse hlaterLookup hnotMiddle hdisjoint hmiddle hsuffix =>
      .duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
        hnotMiddle hdisjoint
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hmiddle)
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hsuffix)

theorem of_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields) :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source (executableFieldSelections fields) :=
  of_derivation schema resolvers variableValues completionDepth parentType source
    (FreshPrefixSelectionDerivation.of_executableFieldSelections_responseNamesNodup
      schema variableValues parentType source fields hnodup hparents)

theorem of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source selectionSet :=
  fun hall hfree hnodup =>
    of_derivation schema resolvers variableValues completionDepth parentType
      source
      (FreshPrefixSelectionDerivation.of_allFields_directiveFree_responseNamesNodup
        schema variableValues parentType source selectionSet hall hfree hnodup)

theorem of_normalizeSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionSetDirectiveFree selectionSet ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        (NormalForm.normalizeSelectionSet schema parentType selectionSet) := by
  intro hfree
  exact
    of_allFields_directiveFree_responseNamesNodup schema resolvers
      variableValues completionDepth parentType source
      (NormalForm.normalizeSelectionSet schema parentType selectionSet)
      (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
        schema parentType selectionSet)
      (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
        schema parentType selectionSet hfree)
      (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
        schema parentType selectionSet)

end FreshPrefixSelectionPlan

theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source selectionSet :=
  fun hall hfree hnodup =>
    (FreshPrefixSelectionPlan.of_allFields_directiveFree_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source
      selectionSet hall hfree hnodup).freshFlat

theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_normal
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetNormal schema selectionSet ->
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source selectionSet := by
  intro hall hfree hnormal
  have hnodup : NormalForm.responseNamesNodup selectionSet := by
    have hnonRedundant : NormalForm.selectionSetNonRedundant selectionSet :=
      hnormal.2
    unfold NormalForm.selectionSetNonRedundant at hnonRedundant
    exact hnonRedundant.1
  exact
    VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source
      selectionSet hall hfree hnodup

structure SelectionSetFreshPlanNormalizes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (raw normalized : List Selection) : Prop where
  collect_eq :
    GraphQL.Execution.collectFields schema variableValues parentType source raw =
    GraphQL.Execution.collectFields schema variableValues parentType source
      normalized
  rawFreshFlat :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      (completionDepth + 1) parentType source raw
  normalizedPlan :
    FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
      parentType source normalized

namespace SelectionSetFreshPlanNormalizes

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source [] [] :=
  let plan :=
    FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
  { collect_eq := rfl
    rawFreshFlat := FreshPrefixSelectionPlan.freshFlat plan
    normalizedPlan := plan }

theorem of_plan
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (plan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source selectionSet) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source selectionSet selectionSet :=
  { collect_eq := rfl
    rawFreshFlat := FreshPrefixSelectionPlan.freshFlat plan
    normalizedPlan := plan }

theorem of_derivation
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (derivation :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        selectionSet) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source selectionSet selectionSet :=
  of_plan
    (FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
      completionDepth parentType source derivation)

theorem of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (htree :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source selectionSet) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source selectionSet selectionSet :=
  of_plan
    (FreshPrefixSelectionPlan.of_headDisjointTree schema resolvers
      variableValues completionDepth parentType source selectionSet htree)

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet)))
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :=
  of_plan
    (FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
      variableValues completionDepth parentType source selectionSet)

theorem of_rawFreshFlat_collectedCollectFields
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw : List Selection}
    (hrawFreshFlat :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source raw) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source raw
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source raw))) :=
  { collect_eq :=
      (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source raw).symm
    rawFreshFlat := hrawFreshFlat
    normalizedPlan :=
      FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
        variableValues completionDepth parentType source raw }

theorem of_derivation_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (derivation :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        selectionSet) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source selectionSet
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :=
  of_rawFreshFlat_collectedCollectFields
    (FreshPrefixSelectionPlan.freshFlat
      (FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
        completionDepth parentType source derivation))

theorem of_normalizeSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionSetDirectiveFree selectionSet ->
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (NormalForm.normalizeSelectionSet schema parentType selectionSet)
        (NormalForm.normalizeSelectionSet schema parentType selectionSet) :=
  fun hfree =>
    of_plan
      (FreshPrefixSelectionPlan.of_normalizeSelectionSet schema resolvers
        variableValues completionDepth parentType source selectionSet hfree)

theorem trans
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw middle normalized : List Selection}
    (left :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source raw middle)
    (right :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source middle normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source raw normalized :=
  { collect_eq := by
      rw [left.collect_eq, right.collect_eq]
    rawFreshFlat := left.rawFreshFlat
    normalizedPlan := right.normalizedPlan }

theorem appendDisjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {rawLeft rawRight normalizedLeft normalizedRight : List Selection}
    (left :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rawLeft normalizedLeft)
    (right :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rawRight normalizedRight)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rawLeft)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rawRight)) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source (rawLeft ++ rawRight)
      (normalizedLeft ++ normalizedRight) := by
  have hnormalizedDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedLeft)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedRight) := by
    intro responseName hleft hright
    exact hdisjoint responseName
      (by rwa [left.collect_eq])
      (by rwa [right.collect_eq])
  exact
    { collect_eq := by
        rw [GraphQL.NormalForm.collectFields_append]
        rw [GraphQL.NormalForm.collectFields_append]
        rw [left.collect_eq, right.collect_eq]
      rawFreshFlat :=
        VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint schema
          resolvers variableValues (completionDepth + 1) parentType source
          rawLeft rawRight hdisjoint left.rawFreshFlat right.rawFreshFlat
      normalizedPlan :=
        FreshPrefixSelectionPlan.appendDisjoint normalizedLeft normalizedRight
          left.normalizedPlan right.normalizedPlan hnormalizedDisjoint }

theorem consDisjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selection : Selection} {rest normalizedSelection normalizedRest : List Selection}
    (head :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source [selection] normalizedSelection)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rest normalizedRest)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [selection])
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rest)) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source (selection :: rest)
      (normalizedSelection ++ normalizedRest) := by
  simpa using
    appendDisjoint (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      (rawLeft := [selection]) (rawRight := rest)
      (normalizedLeft := normalizedSelection)
      (normalizedRight := normalizedRest) head tail hdisjoint

theorem field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.field responseName fieldName arguments directives selectionSet]
      [.field responseName fieldName arguments directives selectionSet] :=
  of_headDisjointTree schema resolvers variableValues completionDepth
    parentType source
    (by
      have htree :
          SelectionSetCollectFieldsHeadDisjoint schema variableValues
              parentType source
              [.field responseName fieldName arguments directives selectionSet]
            ∧
            (∀ selection,
              selection ∈
                  [.field responseName fieldName arguments directives
                    selectionSet] ->
                SelectionCollectFieldsHeadDisjointTree schema variableValues
                  parentType source selection) := by
        constructor
        · constructor
          · intro _candidate _hleft hright
            simp [GraphQL.Execution.collectFields] at hright
          · simp [SelectionSetCollectFieldsHeadDisjoint]
        · intro selection hselection
          simp at hselection
          subst selection
          simp [SelectionCollectFieldsHeadDisjointTree]
      simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree)

theorem of_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source (executableFieldSelections fields)
      (executableFieldSelections fields) :=
  of_plan
    (FreshPrefixSelectionPlan.of_executableFieldSelections_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source fields
      hnodup hparents)

theorem fieldAllowedDropDirectives
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.field responseName fieldName arguments directives selectionSet]
      [.field responseName fieldName arguments [] selectionSet] :=
  { collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hallows,
        selectionDirectivesAllowBool_empty]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_field_single schema resolvers
        variableValues (completionDepth + 1) parentType source responseName
        fieldName arguments directives selectionSet
    normalizedPlan :=
      (SelectionSetFreshPlanNormalizes.field schema resolvers variableValues
        completionDepth parentType source responseName fieldName arguments []
        selectionSet).normalizedPlan }

theorem fieldSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.field responseName fieldName arguments directives selectionSet] [] :=
  { collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hskip]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_field_single schema resolvers
        variableValues (completionDepth + 1) parentType source responseName
        fieldName arguments directives selectionSet
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source) }

theorem executablePrefixFieldConsAllowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest normalized : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections prefixFields ++
          executableFieldSelections
            [executableField parentType responseName fieldName arguments
              selectionSet] ++
          rest)
        normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++
        Selection.field responseName fieldName arguments directives selectionSet ::
        rest)
      normalized :=
  { collect_eq := by
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows, executableFieldSelections, executableFieldSelection,
        executableField, selectionDirectivesAllowBool_empty,
        GraphQL.NormalForm.collectFields_append, List.append_assoc] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_allowed
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixFields responseName fieldName arguments directives selectionSet
        rest hallows tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem executablePrefixFieldConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest normalized : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections prefixFields ++ rest)
        normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++
        Selection.field responseName fieldName arguments directives selectionSet ::
        rest)
      normalized :=
  { collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hskip, hmergeNil, GraphQL.NormalForm.collectFields_append,
        List.append_assoc] using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixFields responseName fieldName arguments directives selectionSet
        rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem inlineFragmentNone
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (child :
      selectionDirectivesAllowBool variableValues directives = true ->
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rawChild normalizedChild) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.inlineFragment none directives rawChild]
      [.inlineFragment none directives normalizedChild] := by
  refine
    { collect_eq := ?_
      rawFreshFlat := ?_
      normalizedPlan := ?_ }
  · by_cases hallows :
        selectionDirectivesAllowBool variableValues directives = true
    · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows, (child hallows).collect_eq]
    · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows]
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild
        (fun hallows => (child hallows).rawFreshFlat)
  · exact
      FreshPrefixSelectionPlan.consDisjoint
        (.inlineFragment none directives normalizedChild) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          directives normalizedChild
          (fun hallows => (child hallows).normalizedPlan.freshFlat))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)

theorem inlineFragmentNoneFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (child :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rawChild normalizedChild) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.inlineFragment none directives rawChild] normalizedChild :=
  { collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows, child.collect_eq,
        GraphQL.Execution.mergeExecutableGroups]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild (fun _hallows => child.rawFreshFlat)
    normalizedPlan := child.normalizedPlan }

theorem inlineFragmentNoneConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source (rawChild ++ rest) normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (Selection.inlineFragment none directives rawChild :: rest)
      normalized :=
  { collect_eq := by
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows] using
        (by
          simpa [GraphQL.NormalForm.collectFields_append] using
            tail.collect_eq)
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_allowed
        schema resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild rest hallows tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem inlineFragmentNoneConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rest normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (Selection.inlineFragment none directives rawChild :: rest)
      normalized :=
  { collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hskip, hmergeNil] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem inlineFragmentNoneCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    (rawChild rest : List Selection)
    (normalizeAllowed :
      selectionDirectivesAllowBool variableValues directives = true ->
        ∃ normalized,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source (rawChild ++ rest)
            normalized)
    (normalizeSkipped :
      selectionDirectivesAllowBool variableValues directives = false ->
        ∃ normalized,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source rest normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment none directives rawChild :: rest)
        normalized := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · rcases normalizeAllowed hallows with ⟨normalized, hnormalized⟩
    exact
      ⟨normalized,
        inlineFragmentNoneConsFlatten directives hallows hnormalized⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rcases normalizeSkipped hskip with ⟨normalized, hnormalized⟩
    exact
      ⟨normalized,
        inlineFragmentNoneConsSkipped directives rawChild hskip
          hnormalized⟩

theorem normalizeSelectionSet_inlineFragmentNoneCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (rawChild rest : List Selection)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source (rawChild ++ rest)
        (GraphQL.NormalForm.normalizeSelectionSet schema parentType
          (rawChild ++ rest))) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (Selection.inlineFragment none [] rawChild :: rest)
      (GraphQL.NormalForm.normalizeSelectionSet schema parentType
        (Selection.inlineFragment none [] rawChild :: rest)) := by
  simpa [GraphQL.NormalForm.normalizeSelectionSet] using
      inlineFragmentNoneConsFlatten (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source) [] rfl
      (rawChild := rawChild) (rest := rest) tail

theorem inlineFragmentNoneSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.inlineFragment none directives selectionSet] [] :=
  { collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hskip]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        directives selectionSet
        (by
          intro hallows
          rw [hskip] at hallows
          contradiction)
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source) }

theorem inlineFragmentSome
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (child :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rawChild normalizedChild) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.inlineFragment (some typeCondition) directives rawChild]
      [.inlineFragment (some typeCondition) directives normalizedChild] := by
  refine
    { collect_eq := ?_
      rawFreshFlat := ?_
      normalizedPlan := ?_ }
  · by_cases hallows :
        selectionDirectivesAllowBool variableValues directives = true
    · by_cases happly :
          doesFragmentTypeApplyBool schema parentType source typeCondition = true
      · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
          hallows, happly, (child hallows happly).collect_eq]
      · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
          hallows, happly]
    · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows]
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild
        (fun hallows happly => (child hallows happly).rawFreshFlat)
  · exact
      FreshPrefixSelectionPlan.consDisjoint
        (.inlineFragment (some typeCondition) directives normalizedChild) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          typeCondition directives normalizedChild
          (fun hallows happly =>
            (child hallows happly).normalizedPlan.freshFlat))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)

theorem inlineFragmentSomeFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    (child :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rawChild normalizedChild) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.inlineFragment (some typeCondition) directives rawChild]
      normalizedChild :=
  { collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows, happly, child.collect_eq,
        GraphQL.Execution.mergeExecutableGroups]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild
        (fun _hallows _happly => child.rawFreshFlat)
    normalizedPlan := child.normalizedPlan }

theorem inlineFragmentSomeConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source (rawChild ++ rest) normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (Selection.inlineFragment (some typeCondition) directives rawChild
        :: rest)
      normalized :=
  { collect_eq := by
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows, happly] using
        (by
          simpa [GraphQL.NormalForm.collectFields_append] using
            tail.collect_eq)
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_allowed_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild rest hallows happly tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem inlineFragmentSomeConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rest normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (Selection.inlineFragment (some typeCondition) directives rawChild
        :: rest)
      normalized :=
  { collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hskip, hmergeNil] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem inlineFragmentSomeConsDoesNotApply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rest normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (Selection.inlineFragment (some typeCondition) directives rawChild
        :: rest)
      normalized :=
  { collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_not_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild rest hallows hnotApply
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem inlineFragmentSomeCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild rest : List Selection)
    (normalizeApplies :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
        ∃ normalized,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source (rawChild ++ rest)
            normalized)
    (normalizeSkipped :
      selectionDirectivesAllowBool variableValues directives = false ->
        ∃ normalized,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source rest normalized)
    (normalizeDoesNotApply :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
        ∃ normalized,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source rest normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment (some typeCondition) directives rawChild
          :: rest)
        normalized := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · rcases normalizeApplies hallows happly with
        ⟨normalized, hnormalized⟩
      exact
        ⟨normalized,
          inlineFragmentSomeConsFlatten typeCondition directives hallows
            happly hnormalized⟩
    · have hnotApply :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases h :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      rcases normalizeDoesNotApply hallows hnotApply with
        ⟨normalized, hnormalized⟩
      exact
        ⟨normalized,
          inlineFragmentSomeConsDoesNotApply typeCondition directives
            rawChild hallows hnotApply hnormalized⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rcases normalizeSkipped hskip with ⟨normalized, hnormalized⟩
    exact
      ⟨normalized,
        inlineFragmentSomeConsSkipped typeCondition directives rawChild hskip
          hnormalized⟩

theorem normalizeSelectionSet_inlineFragmentSomeCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (rawChild rest : List Selection)
    (hfragment :
      doesFragmentTypeApplyBool schema parentType source typeCondition =
        schema.typesOverlapBool parentType typeCondition)
    (normalizeApplies :
      schema.typesOverlapBool parentType typeCondition = true ->
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source (rawChild ++ rest)
          (GraphQL.NormalForm.normalizeSelectionSet schema parentType
            (rawChild ++ rest)))
    (normalizeDoesNotApply :
      schema.typesOverlapBool parentType typeCondition = false ->
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rest
          (GraphQL.NormalForm.normalizeSelectionSet schema parentType rest)) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (Selection.inlineFragment (some typeCondition) [] rawChild :: rest)
      (GraphQL.NormalForm.normalizeSelectionSet schema parentType
        (Selection.inlineFragment (some typeCondition) [] rawChild
          :: rest)) := by
  by_cases hoverlap :
      schema.typesOverlapBool parentType typeCondition = true
  · have happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          true := by
      rw [hfragment, hoverlap]
    simpa [GraphQL.NormalForm.normalizeSelectionSet, hoverlap] using
      inlineFragmentSomeConsFlatten (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues) (completionDepth := completionDepth)
        (parentType := parentType) (source := source) typeCondition []
        rfl happly (rawChild := rawChild) (rest := rest)
        (normalizeApplies hoverlap)
  · have hoverlapFalse :
        schema.typesOverlapBool parentType typeCondition = false := by
      cases h :
          schema.typesOverlapBool parentType typeCondition
      · rfl
      · contradiction
    have hnotApply :
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          false := by
      rw [hfragment, hoverlapFalse]
    simpa [GraphQL.NormalForm.normalizeSelectionSet, hoverlapFalse] using
      inlineFragmentSomeConsDoesNotApply (schema := schema)
        (resolvers := resolvers) (variableValues := variableValues)
        (completionDepth := completionDepth) (parentType := parentType)
        (source := source) typeCondition [] rawChild rfl hnotApply
        (normalizeDoesNotApply hoverlapFalse)

theorem executablePrefixInlineFragmentNoneConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections prefixFields ++ rawChild ++ rest)
        normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++
        Selection.inlineFragment none directives rawChild :: rest)
      normalized :=
  { collect_eq := by
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows,
        GraphQL.NormalForm.collectFields_append, List.append_assoc] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_allowed
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixFields directives rawChild rest hallows tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem executablePrefixInlineFragmentNoneConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections prefixFields ++ rest) normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++
        Selection.inlineFragment none directives rawChild :: rest)
      normalized :=
  { collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hskip, hmergeNil,
        GraphQL.NormalForm.collectFields_append, List.append_assoc] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixFields directives rawChild rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem executablePrefixInlineFragmentSomeConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (happly :
      doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections prefixFields ++ rawChild ++ rest)
        normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++
        Selection.inlineFragment (some typeCondition) directives rawChild ::
        rest)
      normalized :=
  { collect_eq := by
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows, happly,
        GraphQL.NormalForm.collectFields_append, List.append_assoc] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_allowed_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixFields typeCondition directives rawChild rest hallows happly
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem executablePrefixInlineFragmentSomeConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections prefixFields ++ rest) normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++
        Selection.inlineFragment (some typeCondition) directives rawChild ::
        rest)
      normalized :=
  { collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hskip, hmergeNil,
        GraphQL.NormalForm.collectFields_append, List.append_assoc] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixFields typeCondition directives rawChild rest hskip
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem executablePrefixInlineFragmentSomeConsDoesNotApply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    (tail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections prefixFields ++ rest) normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++
        Selection.inlineFragment (some typeCondition) directives rawChild ::
        rest)
      normalized :=
  { collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil,
        GraphQL.NormalForm.collectFields_append, List.append_assoc] using
        tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_not_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixFields typeCondition directives rawChild rest hallows hnotApply
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan }

theorem inlineFragmentSomeSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.inlineFragment (some typeCondition) directives selectionSet] [] :=
  { collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hskip]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives selectionSet
        (by
          intro hallows _happly
          rw [hskip] at hallows
          contradiction)
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source) }

theorem inlineFragmentSomeDoesNotApply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply :
      doesFragmentTypeApplyBool schema parentType source typeCondition = false) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      [.inlineFragment (some typeCondition) directives selectionSet] [] :=
  { collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hallows, hnotApply]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives selectionSet
        (by
          intro _hallows happly
          rw [hnotApply] at happly
          contradiction)
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source) }

theorem executableFieldConsFresh
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (field : ExecutableField) (rest normalizedRest : List Selection)
    (hfresh :
      field.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rest).map Prod.fst)
    (hrest :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source rest normalizedRest) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelection field :: rest)
      (executableFieldSelections [field] ++ normalizedRest) := by
  apply consDisjoint
  · simpa [executableFieldSelections, executableFieldSelection] using
      SelectionSetFreshPlanNormalizes.field schema resolvers variableValues
        completionDepth parentType source field.responseName field.fieldName
        field.arguments [] field.selectionSet
  · exact hrest
  · intro responseName hhead htail
    have hheadEq : responseName = field.responseName := by
      simpa [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        executableFieldSelection, executableField,
        selectionDirectivesAllowBool_empty] using hhead
    exact hfresh (by simpa [hheadEq] using htail)

theorem executableFieldConsFreshNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (field : ExecutableField)
    (restFields : List ExecutableField) (normalizedRest : List Selection)
    (hfresh :
      field.responseName ∉ restFields.map (fun field => field.responseName))
    (hrest :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections restFields) normalizedRest) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections (field :: restFields))
      (executableFieldSelections [field] ++ normalizedRest) := by
  have hfreshCollect :
      field.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections restFields)).map Prod.fst := by
    intro hmem
    exact hfresh
      ((FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source restFields
        field.responseName).mp hmem)
  simpa [executableFieldSelections] using
    executableFieldConsFresh (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      field (executableFieldSelections restFields) normalizedRest
      hfreshCollect hrest

theorem executableFieldSinglePrefixDuplicateFreshMiddle
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : ExecutableField) (middle : List ExecutableField)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hparents :
      ∀ field, field ∈ [first] ++ (middle ++ [later]) ->
        field.parentType = parentType)
    (hmiddleNodup : (middle.map (fun field => field.responseName)).Nodup)
    (hnotMiddle :
      later.responseName ∉ middle.map (fun field => field.responseName)) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections ([first] ++ (middle ++ [later])))
      (executableFieldSelections ([first] ++ [later] ++ middle)) := by
  have hmiddleParents : ExecutableFieldsParent parentType middle := by
    intro field hfield
    exact hparents field (by simp [hfield])
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (executableFieldSelections middle)).map Prod.fst := by
    intro hmem
    have hfieldMem :
        first.responseName ∈ middle.map (fun field => field.responseName) :=
      (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middle first.responseName).mp
        hmem
    exact hnotMiddle (by simpa [hsameResponse] using hfieldMem)
  have hmiddlePlan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source (executableFieldSelections middle) :=
    FreshPrefixSelectionPlan.of_executableFieldSelections_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source middle
      hmiddleNodup hmiddleParents
  have hpairResponses :
      ExecutableFieldsResponseName first.responseName [first, later] := by
    intro field hfield
    simp at hfield
    rcases hfield with hfield | hfield
    · subst field
      rfl
    · subst field
      exact hsameResponse
  have hpairParents :
      ExecutableFieldsParent parentType [first, later] := by
    intro field hfield
    simp at hfield
    rcases hfield with hfield | hfield
    · subst field
      exact hparents first (by simp)
    · subst field
      exact hparents later (by simp)
  have hpairCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first, later]) =
        [(first.responseName, [first, later])] :=
    collectFields_executableFieldSelections_same_group schema variableValues
      parentType source first.responseName [first, later] hpairResponses
      hpairParents
  have hpairMiddleDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first, later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections middle)) := by
    intro responseName hleft hright
    rw [hpairCollect] at hleft
    simp at hleft
    have hmiddleMem :
        responseName ∈ middle.map (fun field => field.responseName) :=
      (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middle responseName).mp
        hright
    exact hnotMiddle (by simpa [hsameResponse, hleft] using hmiddleMem)
  refine
    { collect_eq := ?_
      rawFreshFlat := ?_
      normalizedPlan := ?_ }
  · exact
      collectFields_executableFieldSelections_single_prefix_duplicate_fresh_middle
        schema variableValues parentType source first later middle
        hsameResponse hmiddleNodup hmiddleParents hnotMiddle
  · have hraw :
        VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections [first] ++
            executableFieldSelections middle ++
            executableFieldSelections [later]) :=
      VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
        resolvers variableValues completionDepth parentType source first later
        (executableFieldSelections middle) hsameResponse hlaterLookup
        hnotMiddleCollect hmiddlePlan.freshFlat
    simpa [executableFieldSelections, List.map_append, List.append_assoc]
      using hraw
  · have hnormalizedPlan :
        FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          (executableFieldSelections [first, later] ++
            executableFieldSelections middle) :=
      FreshPrefixSelectionPlan.appendDisjoint
        (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
        (executableFieldSelections [first, later])
        (executableFieldSelections middle)
        (.sameGroup first.responseName [first, later] hpairResponses
          hpairParents)
        hmiddlePlan
        hpairMiddleDisjoint
    simpa [executableFieldSelections, List.append_assoc] using hnormalizedPlan

theorem executableFieldPrefixDuplicateFreshMiddle
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hparents :
      ∀ field, field ∈ prefixFields ++ [later] ->
        field.parentType = parentType)
    (hnotMiddle :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source middle) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections prefixFields ++ middle ++
        executableFieldSelections [later])
      (executableFieldSelections (prefixFields ++ [later]) ++
        executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle))) := by
  let collectedMiddle :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle))
  have hprefixLaterResponse :
      ExecutableFieldsResponseName responseName (prefixFields ++ [later]) := by
    intro field hfield
    rcases List.mem_append.mp hfield with hprefix | hlater
    · exact hprefixResponse field hprefix
    · rcases List.mem_singleton.mp hlater
      exact hlaterResponse
  have hprefixLaterParents :
      ExecutableFieldsParent parentType (prefixFields ++ [later]) := by
    intro field hfield
    exact hparents field hfield
  have hprefixCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (prefixFields ++ [later])) =
        [(responseName, prefixFields ++ [later])] :=
    by
      cases prefixFields with
      | nil =>
          contradiction
      | cons firstPrefix restPrefix =>
          simpa using
            collectFields_executableFieldSelections_same_group schema
              variableValues parentType source responseName
              ((firstPrefix :: restPrefix) ++ [later])
              hprefixLaterResponse hprefixLaterParents
  have hmiddleCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle =
        GraphQL.Execution.collectFields schema variableValues parentType source
          middle := by
    dsimp [collectedMiddle]
    exact
      collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source middle
  have hprefixMiddleDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (prefixFields ++ [later])))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle) := by
    intro candidate hleft hright
    rw [hprefixCollect] at hleft
    rw [hmiddleCollect] at hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  refine
    { collect_eq := ?_
      rawFreshFlat := ?_
      normalizedPlan := ?_ }
  · simpa [collectedMiddle] using
      collectFields_group_duplicate_field_middle_append_eq_collected_middle
        schema variableValues parentType source responseName prefixFields later
        middle [] hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
        schema resolvers variableValues completionDepth parentType source
        responseName prefixFields later middle hprefixNonempty
        hprefixResponse hlaterResponse hlaterLookup hnotMiddle hmiddle
  · have hnormalizedPlan :
        FreshPrefixSelectionPlan schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections (prefixFields ++ [later]) ++
            collectedMiddle) :=
      FreshPrefixSelectionPlan.appendDisjoint
        (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
        (executableFieldSelections (prefixFields ++ [later]))
        collectedMiddle
        (.sameGroup responseName (prefixFields ++ [later])
          hprefixLaterResponse hprefixLaterParents)
        (FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
          variableValues completionDepth parentType source middle)
        hprefixMiddleDisjoint
    simpa [collectedMiddle] using hnormalizedPlan

theorem duplicateFieldPrefixBlockNormalizeTrans_of_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (middle suffix normalizedMiddle normalizedTail : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source middle normalizedMiddle)
    (htail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections (prefixFields ++ [later]) ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)
        normalizedTail) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      ((executableFieldSelections prefixFields ++ middle ++
          executableFieldSelections [later]) ++ suffix)
      normalizedTail :=
  { collect_eq := by
      calc
        GraphQL.Execution.collectFields schema variableValues parentType source
            ((executableFieldSelections prefixFields ++ middle ++
                executableFieldSelections [later]) ++ suffix)
          =
        GraphQL.Execution.collectFields schema variableValues parentType source
            ((executableFieldSelections (prefixFields ++ [later]) ++
                executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle))) ++
              suffix) :=
            collectFields_group_duplicate_field_middle_append_eq_collected_middle
              schema variableValues parentType source responseName prefixFields
              later middle suffix hprefixNonempty hprefixResponse
              hlaterResponse hnotMiddle
        _ =
        GraphQL.Execution.collectFields schema variableValues parentType source
            normalizedTail :=
            htail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_group_duplicate_field_middle_append_of_normalized
        schema resolvers variableValues completionDepth parentType source
        responseName prefixFields later middle suffix hprefixNonempty
        hprefixResponse hlaterResponse hlaterLookup hnotMiddle
        hmiddle.rawFreshFlat htail.rawFreshFlat
    normalizedPlan := htail.normalizedPlan }

theorem duplicateFieldBlockNormalize
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source middle)
    (hnormalized :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      ((executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) ++ suffix)
      ((executableFieldSelections [first, later] ++
          executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle))) ++
        suffix) :=
  { collect_eq :=
      collectFields_duplicate_field_middle_append_eq_collected_middle schema
        variableValues parentType source first later middle suffix
        hsameResponse hnotMiddle
    rawFreshFlat :=
      (FreshPrefixSelectionPlan.duplicateFieldBlockNormalize first later middle
        suffix hsameResponse hlaterLookup hnotMiddle hmiddle
        hnormalized).freshFlat
    normalizedPlan := hnormalized }

theorem duplicateFieldBlockNormalizeTrans
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : ExecutableField) (middle suffix normalizedTail :
      List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source middle)
    (hnormalized :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix))
    (htail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)
        normalizedTail) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      ((executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) ++ suffix)
      normalizedTail :=
  trans
    (duplicateFieldBlockNormalize schema resolvers variableValues
      completionDepth parentType source first later middle suffix
      hsameResponse hlaterLookup hnotMiddle hmiddle hnormalized)
    htail

theorem duplicateFieldBlockNormalizeTrans_of_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : ExecutableField) (middle suffix normalizedMiddle
      normalizedTail : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source middle normalizedMiddle)
    (htail :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)
        normalizedTail) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      ((executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) ++ suffix)
      normalizedTail :=
  { collect_eq := by
      calc
        GraphQL.Execution.collectFields schema variableValues parentType source
            ((executableFieldSelections [first] ++ middle ++
                executableFieldSelections [later]) ++ suffix)
          =
        GraphQL.Execution.collectFields schema variableValues parentType source
            ((executableFieldSelections [first, later] ++
                executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle))) ++
              suffix) :=
            collectFields_duplicate_field_middle_append_eq_collected_middle
              schema variableValues parentType source first later middle suffix
              hsameResponse hnotMiddle
        _ =
        GraphQL.Execution.collectFields schema variableValues parentType source
            normalizedTail :=
            htail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_normalized
        schema resolvers variableValues completionDepth parentType source first
        later middle suffix hsameResponse hlaterLookup hnotMiddle
        hmiddle.rawFreshFlat htail.rawFreshFlat
    normalizedPlan := htail.normalizedPlan }

theorem executableFieldDuplicateBlockNormalizeTrans
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : ExecutableField)
    (middleFields suffixFields : List ExecutableField)
    (normalized : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        middleFields.map (fun field => field.responseName))
    (hmiddle :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections middleFields))
    (hintermediatePlan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections middleFields)))) ++
          executableFieldSelections suffixFields))
    (hnormalized :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections middleFields)))) ++
          executableFieldSelections suffixFields)
        normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections
        (first :: (middleFields ++ later :: suffixFields)))
      normalized := by
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (executableFieldSelections middleFields)).map Prod.fst := by
    intro hmem
    exact hnotMiddle
      ((FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middleFields
        first.responseName).mp hmem)
  have hmiddlePlan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source (executableFieldSelections middleFields) :=
    FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
      completionDepth parentType source hmiddle
  simpa [executableFieldSelections, List.map_append, List.append_assoc] using
    duplicateFieldBlockNormalizeTrans (schema := schema)
      (resolvers := resolvers) (variableValues := variableValues)
      (completionDepth := completionDepth) (parentType := parentType)
      (source := source) first later (executableFieldSelections middleFields)
      (executableFieldSelections suffixFields) normalized hsameResponse
      hlaterLookup hnotMiddleCollect hmiddlePlan hintermediatePlan hnormalized

theorem executableFieldDuplicateBlockNormalizeTrans_of_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : ExecutableField)
    (middleFields suffixFields : List ExecutableField)
    (normalizedMiddle normalized : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        middleFields.map (fun field => field.responseName))
    (hmiddle :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections middleFields) normalizedMiddle)
    (hnormalized :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections middleFields)))) ++
          executableFieldSelections suffixFields)
        normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections
        (first :: (middleFields ++ later :: suffixFields)))
      normalized := by
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (executableFieldSelections middleFields)).map Prod.fst := by
    intro hmem
    exact hnotMiddle
      ((FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middleFields
        first.responseName).mp hmem)
  simpa [executableFieldSelections, List.map_append, List.append_assoc] using
    duplicateFieldBlockNormalizeTrans_of_middleNormalizes (schema := schema)
      (resolvers := resolvers) (variableValues := variableValues)
      (completionDepth := completionDepth) (parentType := parentType)
      (source := source) first later (executableFieldSelections middleFields)
      (executableFieldSelections suffixFields) normalizedMiddle normalized
      hsameResponse hlaterLookup hnotMiddleCollect hmiddle hnormalized

theorem executableFieldPrefixDuplicateBlockNormalizeTrans_of_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (middleFields suffixFields : List ExecutableField)
    (normalizedMiddle normalized : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      responseName ∉ middleFields.map (fun field => field.responseName))
    (hmiddle :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections middleFields) normalizedMiddle)
    (hnormalized :
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections (prefixFields ++ [later]) ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections middleFields)))) ++
          executableFieldSelections suffixFields)
        normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections
        (prefixFields ++ middleFields ++ later :: suffixFields))
      normalized := by
  have hnotMiddleCollect :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (executableFieldSelections middleFields)).map Prod.fst := by
    intro hmem
    exact hnotMiddle
      ((collectFields_executableFieldSelections_key_mem_global
        schema variableValues parentType source middleFields responseName).mp
        hmem)
  simpa [executableFieldSelections, List.map_append, List.append_assoc] using
    duplicateFieldPrefixBlockNormalizeTrans_of_middleNormalizes
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues)
      (completionDepth := completionDepth) (parentType := parentType)
      (source := source) responseName prefixFields later
      (executableFieldSelections middleFields)
      (executableFieldSelections suffixFields) normalizedMiddle normalized
      hprefixNonempty hprefixResponse hlaterResponse hlaterLookup
      hnotMiddleCollect hmiddle hnormalized

theorem executableFieldPrefixNormalizesOfCases_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields rest : List ExecutableField)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hprefixParents :
      ∀ field, field ∈ prefixFields -> field.parentType = parentType)
    (hrestLookups :
      ∀ field, field ∈ rest ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition)
    (hfresh :
      responseName ∉ rest.map (fun field => field.responseName) ->
        ∃ normalizedRest,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source
            (executableFieldSelections rest) normalizedRest)
    (hmiddle :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = responseName ->
        responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalizedMiddle,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections middle) normalizedMiddle)
    (hduplicate :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = responseName ->
        responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              ((executableFieldSelections (prefixFields ++ [later]) ++
                  executableFieldSelections
                    (collectedExecutableFields
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (executableFieldSelections middle)))) ++
                executableFieldSelections suffix)
              normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (prefixFields ++ rest)) normalized := by
  by_cases hmem :
      responseName ∈ rest.map (fun field => field.responseName)
  · rcases
      FreshPrefixSelectionDerivation.executableFields_first_responseName_split
        responseName rest hmem with
      ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
    have hlaterLookup :
        ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
          some fieldDefinition := by
      exact hrestLookups later (by
        rw [hsplit]
        simp)
    rcases hmiddle middle later suffix hsplit hlater hnotMiddle with
      ⟨normalizedMiddle, hmiddleStep⟩
    rcases hduplicate middle later suffix hsplit hlater hnotMiddle with
      ⟨normalized, hnormalizedStep⟩
    refine ⟨normalized, ?_⟩
    rw [hsplit]
    simpa [List.append_assoc] using
      executableFieldPrefixDuplicateBlockNormalizeTrans_of_middleNormalizes
        responseName prefixFields later middle suffix normalizedMiddle
        normalized hprefixNonempty hprefixResponse hlater hlaterLookup
        hnotMiddle hmiddleStep hnormalizedStep
  · rcases hfresh hmem with ⟨normalizedRest, hrest⟩
    have hprefix :
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections prefixFields)
          (executableFieldSelections prefixFields) :=
      SelectionSetFreshPlanNormalizes.of_plan
        (.sameGroup responseName prefixFields hprefixResponse hprefixParents)
    have hprefixCollect :
        GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections prefixFields) =
          [(responseName, prefixFields)] := by
      cases prefixFields with
      | nil =>
          contradiction
      | cons firstPrefix restPrefix =>
          simpa using
            collectFields_executableFieldSelections_same_group schema
              variableValues parentType source responseName
              (firstPrefix :: restPrefix) hprefixResponse hprefixParents
    have hdisjoint :
        GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (executableFieldSelections prefixFields))
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (executableFieldSelections rest)) := by
      intro candidate hleft hright
      rw [hprefixCollect] at hleft
      simp at hleft
      have hrightName :
          candidate ∈ rest.map (fun field => field.responseName) :=
        (collectFields_executableFieldSelections_key_mem_global
          schema variableValues parentType source rest candidate).mp hright
      exact hmem (by simpa [hleft] using hrightName)
    exact
      ⟨executableFieldSelections prefixFields ++ normalizedRest,
        by
          simpa [executableFieldSelections, List.map_append] using
            SelectionSetFreshPlanNormalizes.appendDisjoint hprefix hrest
              hdisjoint⟩

theorem executableFieldPrefixNormalizes_of_smaller
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields rest : List ExecutableField)
    (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse :
      ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hwholeParents :
      ExecutableFieldsParent parentType (prefixFields ++ rest))
    (hwholeLookups :
      ∀ field, field ∈ prefixFields ++ rest ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition)
    (normalizeSmaller :
      ∀ fields,
        fields.length < (prefixFields ++ rest).length ->
        ExecutableFieldsParent parentType fields ->
        (∀ field, field ∈ fields ->
          ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
            some fieldDefinition) ->
          ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections fields) normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (prefixFields ++ rest)) normalized := by
  let total := (prefixFields ++ rest).length
  have aux :
      ∀ m (prefixFields rest : List ExecutableField),
        rest.length = m ->
        prefixFields ≠ [] ->
        (∀ field, field ∈ prefixFields -> field.responseName = responseName) ->
        (prefixFields ++ rest).length = total ->
        ExecutableFieldsParent parentType (prefixFields ++ rest) ->
        (∀ field, field ∈ prefixFields ++ rest ->
          ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
            some fieldDefinition) ->
          ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections (prefixFields ++ rest)) normalized := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro prefixFields rest hrestLen hprefixNonempty hprefixResponse
          htotal hparents hlookups
        by_cases hmem :
            responseName ∈ rest.map (fun field => field.responseName)
        · rcases
            FreshPrefixSelectionDerivation.executableFields_first_responseName_split
              responseName rest hmem with
            ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
          let collectedMiddle : List ExecutableField :=
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                parentType source (executableFieldSelections middle))
          let transformedRest : List ExecutableField :=
            collectedMiddle ++ suffix
          have hmiddleParents :
              ExecutableFieldsParent parentType middle := by
            intro field hfield
            exact hparents field (by
              rw [hsplit]
              simp [hfield])
          have hmiddleLookups :
              ∀ field, field ∈ middle ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            exact hlookups field (by
              rw [hsplit]
              simp [hfield])
          have hlaterLookup :
              ∃ fieldDefinition,
                schema.lookupField parentType later.fieldName =
                  some fieldDefinition := by
            exact hlookups later (by
              rw [hsplit]
              simp)
          have hmiddleLt :
              middle.length < total := by
            rw [← htotal, hsplit]
            simp [List.length_append]
            omega
          rcases normalizeSmaller middle hmiddleLt hmiddleParents
              hmiddleLookups with
            ⟨normalizedMiddle, hmiddleStep⟩
          have hcollectedMiddleParents :
              ExecutableFieldsParent parentType collectedMiddle := by
            dsimp [collectedMiddle]
            exact
              FreshPrefixSelectionDerivation.ExecutableFieldsParent_collectedExecutableFields
                (collectFields_parent schema variableValues parentType source
                  (executableFieldSelections middle))
          have hsuffixParents :
              ExecutableFieldsParent parentType suffix := by
            intro field hfield
            exact hparents field (by
              rw [hsplit]
              simp [hfield])
          have hcollectedMiddleLookups :
              ∀ field, field ∈ collectedMiddle ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            dsimp [collectedMiddle]
            exact
              collectedExecutableFields_collectFields_executableFieldSelections_lookup
                schema variableValues parentType source middle
                hmiddleParents hmiddleLookups
          have hsuffixLookups :
              ∀ field, field ∈ suffix ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            exact hlookups field (by
              rw [hsplit]
              simp [hfield])
          have htransformedParents :
              ExecutableFieldsParent parentType transformedRest := by
            intro field hfield
            dsimp [transformedRest] at hfield
            rcases List.mem_append.mp hfield with hcollected | hsuffix
            · exact hcollectedMiddleParents field hcollected
            · exact hsuffixParents field hsuffix
          have htransformedLookups :
              ∀ field, field ∈ transformedRest ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            dsimp [transformedRest] at hfield
            rcases List.mem_append.mp hfield with hcollected | hsuffix
            · exact hcollectedMiddleLookups field hcollected
            · exact hsuffixLookups field hsuffix
          have hnewWholeParents :
                ExecutableFieldsParent parentType
                  ((prefixFields ++ [later]) ++ transformedRest) := by
              intro field hfield
              rcases List.mem_append.mp hfield with hprefixLater | htail
              · rcases List.mem_append.mp hprefixLater with hprefix | hlaterMem
                · exact hparents field (by
                    rw [hsplit]
                    simp [hprefix])
                · rcases List.mem_singleton.mp hlaterMem
                  exact hparents later (by
                    rw [hsplit]
                    simp)
              · exact htransformedParents field htail
          have hcollectedLen :
              collectedMiddle.length = middle.length := by
            dsimp [collectedMiddle]
            exact
              collectedExecutableFields_collectFields_executableFieldSelections_length
                schema variableValues parentType source middle
          have htransformedLt :
              transformedRest.length < m := by
            dsimp [transformedRest]
            rw [List.length_append, hcollectedLen]
            rw [← hrestLen, hsplit]
            simp [List.length_append]
          have hnewTotal :
              ((prefixFields ++ [later]) ++ transformedRest).length = total := by
            dsimp [transformedRest]
            rw [List.length_append, List.length_append]
            rw [List.length_append, hcollectedLen]
            rw [← htotal, hsplit]
            simp [List.length_append]
            omega
          have hnewPrefixNonempty : prefixFields ++ [later] ≠ [] := by
            simp
          have hnewPrefixResponse :
              ∀ field, field ∈ prefixFields ++ [later] ->
                field.responseName = responseName := by
            intro field hfield
            rcases List.mem_append.mp hfield with hprefix | hlaterMem
            · exact hprefixResponse field hprefix
            · rcases List.mem_singleton.mp hlaterMem
              exact hlater
          have hnewWholeLookups :
              ∀ field, field ∈ (prefixFields ++ [later]) ++ transformedRest ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            rcases List.mem_append.mp hfield with hprefixLater | htail
            · rcases List.mem_append.mp hprefixLater with hprefix | hlaterMem
              · exact hlookups field (by
                  rw [hsplit]
                  simp [hprefix])
              · rcases List.mem_singleton.mp hlaterMem
                exact hlaterLookup
            · exact htransformedLookups field htail
          rcases
              ih transformedRest.length htransformedLt
                (prefixFields ++ [later]) transformedRest rfl
                hnewPrefixNonempty hnewPrefixResponse hnewTotal
                hnewWholeParents hnewWholeLookups with
            ⟨normalizedTail, htailStep⟩
          have htailStep' :
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                ((executableFieldSelections (prefixFields ++ [later]) ++
                    executableFieldSelections collectedMiddle) ++
                  executableFieldSelections suffix)
                normalizedTail := by
            simpa [transformedRest, executableFieldSelections,
              List.map_append, List.append_assoc] using htailStep
          refine ⟨normalizedTail, ?_⟩
          rw [hsplit]
          simpa [transformedRest, collectedMiddle, executableFieldSelections,
            List.map_append, List.append_assoc] using
            executableFieldPrefixDuplicateBlockNormalizeTrans_of_middleNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth)
              (parentType := parentType) (source := source)
              responseName prefixFields later middle suffix normalizedMiddle
              normalizedTail hprefixNonempty hprefixResponse hlater
              hlaterLookup hnotMiddle hmiddleStep htailStep'
        · have hprefixParents :
              ExecutableFieldsParent parentType prefixFields := by
            intro field hfield
            exact hparents field (by simp [hfield])
          have hprefix :
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (executableFieldSelections prefixFields)
                (executableFieldSelections prefixFields) :=
            SelectionSetFreshPlanNormalizes.of_plan
              (.sameGroup responseName prefixFields hprefixResponse
                hprefixParents)
          have hrestParents :
              ExecutableFieldsParent parentType rest := by
            intro field hfield
            exact hparents field (by simp [hfield])
          have hrestLookups :
              ∀ field, field ∈ rest ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            exact hlookups field (by simp [hfield])
          have hrestLt :
              rest.length < total := by
            rw [← htotal]
            cases prefixFields with
            | nil =>
                contradiction
            | cons firstPrefix restPrefix =>
                simp [List.length_append]
                omega
          rcases normalizeSmaller rest hrestLt hrestParents hrestLookups with
            ⟨normalizedRest, hrestStep⟩
          have hprefixCollect :
              GraphQL.Execution.collectFields schema variableValues parentType
                  source (executableFieldSelections prefixFields) =
                [(responseName, prefixFields)] := by
            cases prefixFields with
            | nil =>
                contradiction
            | cons firstPrefix restPrefix =>
                simpa using
                  collectFields_executableFieldSelections_same_group schema
                    variableValues parentType source responseName
                    (firstPrefix :: restPrefix) hprefixResponse
                    hprefixParents
          have hdisjoint :
              GraphQL.NormalForm.executableGroupNamesDisjoint
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source (executableFieldSelections prefixFields))
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source (executableFieldSelections rest)) := by
            intro candidate hleft hright
            rw [hprefixCollect] at hleft
            simp at hleft
            have hrightName :
                candidate ∈ rest.map (fun field => field.responseName) :=
              (collectFields_executableFieldSelections_key_mem_global
                schema variableValues parentType source rest candidate).mp
                hright
            exact hmem (by simpa [hleft] using hrightName)
          exact
            ⟨executableFieldSelections prefixFields ++ normalizedRest,
              by
                simpa [executableFieldSelections, List.map_append] using
                  SelectionSetFreshPlanNormalizes.appendDisjoint hprefix
                    hrestStep hdisjoint⟩
  exact aux rest.length prefixFields rest rfl hprefixNonempty
    hprefixResponse rfl hwholeParents hwholeLookups

theorem executableFieldsNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (fields : List ExecutableField)
    (hparents : ExecutableFieldsParent parentType fields)
    (hlookups :
      ∀ field, field ∈ fields ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections fields) normalized := by
  have aux :
      ∀ n (fields : List ExecutableField),
          fields.length = n ->
          ExecutableFieldsParent parentType fields ->
          (∀ field, field ∈ fields ->
            ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName =
                some fieldDefinition) ->
            ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections fields) normalized := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
          intro fields hlen hparents hlookups
          cases fields with
          | nil =>
              exact
                ⟨[],
                  SelectionSetFreshPlanNormalizes.nil schema resolvers
                    variableValues completionDepth parentType source⟩
          | cons first rest =>
              have hwholeParents :
                  ExecutableFieldsParent parentType ([first] ++ rest) := by
                simpa using hparents
              have hwholeLookups :
                  ∀ field, field ∈ [first] ++ rest ->
                    ∃ fieldDefinition,
                      schema.lookupField parentType field.fieldName =
                        some fieldDefinition := by
                simpa using hlookups
              rcases
                  executableFieldPrefixNormalizes_of_smaller
                    (schema := schema) (resolvers := resolvers)
                    (variableValues := variableValues)
                    (completionDepth := completionDepth)
                    (parentType := parentType) (source := source)
                    first.responseName [first] rest
                    (by simp)
                    (by
                      intro field hfield
                      simp at hfield
                      subst field
                      rfl)
                    hwholeParents hwholeLookups
                    (by
                      intro smaller hlt hsmallerParents hsmallerLookups
                      exact
                        ih smaller.length
                          (by
                            rw [← hlen]
                            simpa [List.length_append] using hlt)
                          smaller rfl hsmallerParents hsmallerLookups) with
              ⟨normalized, hnormalized⟩
              exact
                ⟨normalized,
                  by
                    simpa [executableFieldSelections] using hnormalized⟩
  exact aux fields.length fields rfl hparents hlookups

private theorem selectionSet_size_append (left right : List Selection) :
    SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

theorem executablePrefixRawNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List ExecutableField)
    (hparents : ExecutableFieldsParent parentType prefixFields)
    (hprefixLookups :
      ∀ field, field ∈ prefixFields ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition) :
    (selectionSet : List Selection) ->
    executionSelectionSetLookupValid schema parentType selectionSet ->
      ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections prefixFields ++ selectionSet) normalized
  | [], _hlookupValid => by
      rcases
          executableFieldsNormalizes (schema := schema) (resolvers := resolvers)
            (variableValues := variableValues)
            (completionDepth := completionDepth) (parentType := parentType)
            (source := source) prefixFields hparents hprefixLookups with
        ⟨normalized, hnormalized⟩
      exact ⟨normalized, by simpa using hnormalized⟩
  | .field responseName fieldName arguments directives selectionSet :: rest,
      hlookupValid => by
      unfold executionSelectionSetLookupValid at hlookupValid
      have hfieldLookup :
          ∃ fieldDefinition, schema.lookupField parentType fieldName =
            some fieldDefinition := by
        simpa [executionSelectionLookupValid] using
          hlookupValid
            (.field responseName fieldName arguments directives selectionSet)
            (by simp)
      have hrestLookup :
          executionSelectionSetLookupValid schema parentType rest := by
        unfold executionSelectionSetLookupValid
        intro selection hselection
        exact hlookupValid selection (by simp [hselection])
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · let field :=
          executableField parentType responseName fieldName arguments
            selectionSet
        have hparents' :
            ExecutableFieldsParent parentType (prefixFields ++ [field]) := by
          intro candidate hcandidate
          rcases List.mem_append.mp hcandidate with hprefix | hfield
          · exact hparents candidate hprefix
          · rcases List.mem_singleton.mp hfield
            simp [field, executableField]
        have hlookups' :
            ∀ candidate, candidate ∈ prefixFields ++ [field] ->
              ∃ fieldDefinition,
                schema.lookupField parentType candidate.fieldName =
                  some fieldDefinition := by
          intro candidate hcandidate
          rcases List.mem_append.mp hcandidate with hprefix | hfield
          · exact hprefixLookups candidate hprefix
          · rcases List.mem_singleton.mp hfield with rfl
            simpa [field, executableField] using hfieldLookup
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) (prefixFields ++ [field]) hparents'
              hlookups' rest hrestLookup with
          ⟨normalized, tail⟩
        have tail' :
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections prefixFields ++
                executableFieldSelections
                  [executableField parentType responseName fieldName arguments
                    selectionSet] ++
                rest)
              normalized := by
          simpa [field, executableFieldSelections, List.map_append,
            List.append_assoc] using tail
        exact
          ⟨normalized,
            executablePrefixFieldConsAllowed prefixFields responseName
              fieldName arguments directives selectionSet rest normalized
              hallows tail'⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hparents hprefixLookups rest
              hrestLookup with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            executablePrefixFieldConsSkipped prefixFields responseName
              fieldName arguments directives selectionSet rest normalized
              hskip tail⟩
  | .inlineFragment none directives rawChild :: rest, hlookupValid => by
      unfold executionSelectionSetLookupValid at hlookupValid
      have hchildLookup :
          executionSelectionSetLookupValid schema parentType rawChild := by
        simpa [executionSelectionLookupValid] using
          hlookupValid (.inlineFragment none directives rawChild) (by simp)
      have hrestLookup :
          executionSelectionSetLookupValid schema parentType rest := by
        unfold executionSelectionSetLookupValid
        intro selection hselection
        exact hlookupValid selection (by simp [hselection])
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · have happendLookup :
            executionSelectionSetLookupValid schema parentType
              (rawChild ++ rest) := by
          unfold executionSelectionSetLookupValid at hchildLookup hrestLookup
          unfold executionSelectionSetLookupValid
          intro selection hselection
          rcases List.mem_append.mp hselection with hchild | hrest
          · exact hchildLookup selection hchild
          · exact hrestLookup selection hrest
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hparents hprefixLookups
              (rawChild ++ rest) happendLookup with
          ⟨normalized, tail⟩
        have tail' :
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections prefixFields ++ rawChild ++ rest)
              normalized := by
          simpa [List.append_assoc] using tail
        exact
          ⟨normalized,
            executablePrefixInlineFragmentNoneConsFlatten prefixFields
              directives hallows tail'⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hparents hprefixLookups rest
              hrestLookup with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            executablePrefixInlineFragmentNoneConsSkipped prefixFields
              directives rawChild hskip tail⟩
  | .inlineFragment (some typeCondition) directives rawChild :: rest,
      hlookupValid => by
      unfold executionSelectionSetLookupValid at hlookupValid
      have hchildLookup :
          executionSelectionSetLookupValid schema parentType rawChild := by
        simpa [executionSelectionLookupValid] using
          hlookupValid (.inlineFragment (some typeCondition) directives rawChild)
            (by simp)
      have hrestLookup :
          executionSelectionSetLookupValid schema parentType rest := by
        unfold executionSelectionSetLookupValid
        intro selection hselection
        exact hlookupValid selection (by simp [hselection])
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · by_cases happly :
            doesFragmentTypeApplyBool schema parentType source typeCondition =
              true
        · have happendLookup :
              executionSelectionSetLookupValid schema parentType
                (rawChild ++ rest) := by
            unfold executionSelectionSetLookupValid at hchildLookup hrestLookup
            unfold executionSelectionSetLookupValid
            intro selection hselection
            rcases List.mem_append.mp hselection with hchild | hrest
            · exact hchildLookup selection hchild
            · exact hrestLookup selection hrest
          rcases
              executablePrefixRawNormalizes
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth) (parentType := parentType)
                (source := source) prefixFields hparents hprefixLookups
                (rawChild ++ rest) happendLookup with
            ⟨normalized, tail⟩
          have tail' :
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (executableFieldSelections prefixFields ++ rawChild ++ rest)
                normalized := by
            simpa [List.append_assoc] using tail
          exact
            ⟨normalized,
              executablePrefixInlineFragmentSomeConsFlatten prefixFields
                typeCondition directives hallows happly tail'⟩
        · have hnotApply :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                false := by
            cases h :
                doesFragmentTypeApplyBool schema parentType source typeCondition
            · rfl
            · exact False.elim (happly h)
          rcases
              executablePrefixRawNormalizes
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth) (parentType := parentType)
                (source := source) prefixFields hparents hprefixLookups rest
                hrestLookup with
            ⟨normalized, tail⟩
          exact
            ⟨normalized,
              executablePrefixInlineFragmentSomeConsDoesNotApply prefixFields
                typeCondition directives rawChild hallows hnotApply tail⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hparents hprefixLookups rest
              hrestLookup with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            executablePrefixInlineFragmentSomeConsSkipped prefixFields
              typeCondition directives rawChild hskip tail⟩
termination_by selectionSet _ => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [selectionSet_size_append, SelectionSet.size, Selection.size]
    try omega

theorem exists_allFields_directiveFree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    executionSelectionSetLookupValid schema parentType selectionSet ->
      ∃ normalizedSelectionSet,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source selectionSet
          normalizedSelectionSet := by
  intro hall hfree hlookupValid
  let fields :=
    selectionSet.map
      (FreshPrefixSelectionDerivation.executableFieldOfSelection parentType)
  have hselectionEq : executableFieldSelections fields = selectionSet := by
    dsimp [fields]
    exact
      FreshPrefixSelectionDerivation.executableFieldSelections_map_executableFieldOfSelection
        parentType selectionSet hall hfree
  have hparents : ExecutableFieldsParent parentType fields := by
    dsimp [fields]
    exact
      FreshPrefixSelectionDerivation.executableFieldsParent_map_executableFieldOfSelection
        parentType selectionSet
  have hlookups :
      ∀ field, field ∈ fields ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition := by
    intro field hfield
    dsimp [fields] at hfield
    rcases List.mem_map.mp hfield with ⟨selection, hselection, hfieldEq⟩
    have hselectionField : Selection.isField selection :=
      hall selection hselection
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        rcases hfieldEq
        have hselectionLookup :
            executionSelectionLookupValid schema parentType
              (.field responseName fieldName arguments directives
                childSelectionSet) := by
          unfold executionSelectionSetLookupValid at hlookupValid
          exact hlookupValid
            (.field responseName fieldName arguments directives
              childSelectionSet)
            hselection
        simpa [FreshPrefixSelectionDerivation.executableFieldOfSelection,
          executableField, executionSelectionLookupValid] using
          hselectionLookup
    | inlineFragment typeCondition directives childSelectionSet =>
        simp [Selection.isField] at hselectionField
  rcases
      executableFieldsNormalizes (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth) (parentType := parentType)
        (source := source) fields hparents hlookups with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact
    ⟨normalizedSelectionSet,
      by
        simpa [hselectionEq] using hnormalization⟩

theorem executableFieldHeadDuplicateNormalizesOfMem
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : ExecutableField) (rest : List ExecutableField)
    (hmem :
      first.responseName ∈ rest.map (fun field => field.responseName))
    (hrestLookups :
      ∀ field, field ∈ rest ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition)
    (hmiddle :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          FreshPrefixSelectionDerivation schema variableValues parentType source
            (executableFieldSelections middle))
    (hnormalized :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalized,
            FreshPrefixSelectionPlan schema resolvers variableValues
              completionDepth parentType source
              ((executableFieldSelections [first, later] ++
                  executableFieldSelections
                    (collectedExecutableFields
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (executableFieldSelections middle)))) ++
                executableFieldSelections suffix)
            ∧
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              ((executableFieldSelections [first, later] ++
                  executableFieldSelections
                    (collectedExecutableFields
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (executableFieldSelections middle)))) ++
                executableFieldSelections suffix)
              normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (first :: rest)) normalized := by
  rcases
      FreshPrefixSelectionDerivation.executableFields_first_responseName_split
        first.responseName rest hmem with
      ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
  have hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition := by
    exact hrestLookups later (by rw [hsplit]; simp)
  rcases hnormalized middle later suffix hsplit hlater hnotMiddle with
    ⟨normalized, hintermediatePlan, hnormalizedStep⟩
  refine ⟨normalized, ?_⟩
  rw [hsplit]
  exact executableFieldDuplicateBlockNormalizeTrans first later middle suffix
    normalized hlater hlaterLookup hnotMiddle
    (hmiddle middle later suffix hsplit hlater hnotMiddle)
    hintermediatePlan hnormalizedStep

theorem executableFieldHeadDuplicateNormalizesOfMem_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : ExecutableField) (rest : List ExecutableField)
    (hmem :
      first.responseName ∈ rest.map (fun field => field.responseName))
    (hrestLookups :
      ∀ field, field ∈ rest ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition)
    (hmiddle :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalizedMiddle,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections middle) normalizedMiddle)
    (hnormalized :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              ((executableFieldSelections [first, later] ++
                  executableFieldSelections
                    (collectedExecutableFields
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (executableFieldSelections middle)))) ++
                executableFieldSelections suffix)
              normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (first :: rest)) normalized := by
  rcases
      FreshPrefixSelectionDerivation.executableFields_first_responseName_split
        first.responseName rest hmem with
      ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
  have hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition := by
    exact hrestLookups later (by rw [hsplit]; simp)
  rcases hmiddle middle later suffix hsplit hlater hnotMiddle with
    ⟨normalizedMiddle, hmiddleStep⟩
  rcases hnormalized middle later suffix hsplit hlater hnotMiddle with
    ⟨normalized, hnormalizedStep⟩
  refine ⟨normalized, ?_⟩
  rw [hsplit]
  exact
    executableFieldDuplicateBlockNormalizeTrans_of_middleNormalizes first
      later middle suffix normalizedMiddle normalized hlater hlaterLookup
      hnotMiddle hmiddleStep hnormalizedStep

theorem executableFieldHeadNormalizesOfCases
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : ExecutableField) (rest : List ExecutableField)
    (hrestLookups :
      ∀ field, field ∈ rest ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition)
    (hfresh :
      first.responseName ∉ rest.map (fun field => field.responseName) ->
        ∃ normalizedRest,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source
            (executableFieldSelections rest) normalizedRest)
    (hmiddle :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          FreshPrefixSelectionDerivation schema variableValues parentType source
            (executableFieldSelections middle))
    (hduplicate :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalized,
            FreshPrefixSelectionPlan schema resolvers variableValues
              completionDepth parentType source
              ((executableFieldSelections [first, later] ++
                  executableFieldSelections
                    (collectedExecutableFields
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (executableFieldSelections middle)))) ++
                executableFieldSelections suffix)
            ∧
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              ((executableFieldSelections [first, later] ++
                  executableFieldSelections
                    (collectedExecutableFields
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (executableFieldSelections middle)))) ++
                executableFieldSelections suffix)
              normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (first :: rest)) normalized := by
  by_cases hmem :
      first.responseName ∈ rest.map (fun field => field.responseName)
  · exact executableFieldHeadDuplicateNormalizesOfMem first rest hmem
      hrestLookups hmiddle hduplicate
  · rcases hfresh hmem with ⟨normalizedRest, hrest⟩
    exact
      ⟨executableFieldSelections [first] ++ normalizedRest,
        executableFieldConsFreshNormalizes first rest normalizedRest hmem
          hrest⟩

theorem executableFieldHeadNormalizesOfCases_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : ExecutableField) (rest : List ExecutableField)
    (hrestLookups :
      ∀ field, field ∈ rest ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition)
    (hfresh :
      first.responseName ∉ rest.map (fun field => field.responseName) ->
        ∃ normalizedRest,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source
            (executableFieldSelections rest) normalizedRest)
    (hmiddle :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalizedMiddle,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections middle) normalizedMiddle)
    (hduplicate :
      ∀ middle later suffix,
        rest = middle ++ later :: suffix ->
        later.responseName = first.responseName ->
        first.responseName ∉ middle.map (fun field => field.responseName) ->
          ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              ((executableFieldSelections [first, later] ++
                  executableFieldSelections
                    (collectedExecutableFields
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (executableFieldSelections middle)))) ++
                executableFieldSelections suffix)
              normalized) :
    ∃ normalized,
      SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (first :: rest)) normalized := by
  by_cases hmem :
      first.responseName ∈ rest.map (fun field => field.responseName)
  · exact executableFieldHeadDuplicateNormalizesOfMem_middleNormalizes first
      rest hmem hrestLookups hmiddle hduplicate
  · rcases hfresh hmem with ⟨normalizedRest, hrest⟩
    exact
      ⟨executableFieldSelections [first] ++ normalizedRest,
        executableFieldConsFreshNormalizes first rest normalizedRest hmem
          hrest⟩

theorem duplicateFieldBlockNormalizeHeadDisjointMiddle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source middle)
    (hnormalized :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      ((executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) ++ suffix)
      ((executableFieldSelections [first, later] ++
          executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle))) ++
        suffix) :=
  duplicateFieldBlockNormalize schema resolvers variableValues completionDepth
    parentType source first later middle suffix hsameResponse hlaterLookup
    hnotMiddle
    (FreshPrefixSelectionPlan.of_headDisjointTree schema resolvers
      variableValues completionDepth parentType source middle hmiddle)
    hnormalized

theorem duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hparents : ExecutableFieldsParent parentType [first, later])
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix))
    (hmiddle :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source middle)
    (hsuffix :
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source suffix) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source
      ((executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) ++ suffix)
      ((executableFieldSelections [first, later] ++
          executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle))) ++
        suffix) :=
  duplicateFieldBlockNormalizeHeadDisjointMiddle schema resolvers
    variableValues completionDepth parentType source first later middle suffix
    hsameResponse hlaterLookup hnotMiddle hmiddle
    (FreshPrefixSelectionPlan.duplicateFieldBlockNormalizePlan_of_headDisjointSuffix
      schema resolvers variableValues completionDepth parentType source first
      later middle suffix hsameResponse hparents hnotMiddle hdisjoint hsuffix)

end SelectionSetFreshPlanNormalizes

theorem VisitSubfieldsFlatCollectsFreshPrefixes_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues 0
      parentType source selectionSet :=
  fun fields _hfresh =>
    VisitSubfieldsFlatCollects_depth_zero schema resolvers variableValues
      parentType source selectionSet fields

theorem VisitSubfieldsFlatCollectsFreshPrefixes_all
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    executionSelectionSetLookupValid schema parentType selectionSet ->
    VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
      depth parentType source selectionSet := by
  intro hlookupValid
  cases depth with
  | zero =>
      exact
        VisitSubfieldsFlatCollectsFreshPrefixes_depth_zero schema resolvers
          variableValues parentType source selectionSet
  | succ completionDepth =>
      have hparents :
          ExecutableFieldsParent parentType ([] : List ExecutableField) := by
        intro field hfield
        simp at hfield
      rcases
          SelectionSetFreshPlanNormalizes.executablePrefixRawNormalizes
            (schema := schema) (resolvers := resolvers)
            (variableValues := variableValues)
            (completionDepth := completionDepth) (parentType := parentType)
            (source := source) ([] : List ExecutableField) hparents
            (by
              intro field hfield
              simp at hfield)
            selectionSet hlookupValid with
        ⟨normalized, hnormalized⟩
      simpa [executableFieldSelections] using hnormalized.rawFreshFlat

inductive SelectionSetFreshPlanNormalizationTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    List Selection -> List Selection -> Prop where
  | nil :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source [] []
  | ofNormalizes {raw normalized : List Selection}
      (normalization :
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source raw normalized) :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source raw normalized
  | ofPlan {selectionSet : List Selection}
      (plan :
        FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source selectionSet) :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet
  | ofHeadDisjointTree {selectionSet : List Selection}
      (tree :
        SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet) :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet
  | executableFieldSelectionsResponseNamesNodup
      (fields : List ExecutableField)
      (hnodup : (fields.map (fun field => field.responseName)).Nodup)
      (hparents : ExecutableFieldsParent parentType fields) :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source (executableFieldSelections fields)
        (executableFieldSelections fields)
  | appendDisjoint
      {rawLeft rawRight normalizedLeft normalizedRight : List Selection} :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source rawLeft normalizedLeft ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source rawRight normalizedRight ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rawLeft)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rawRight) ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source (rawLeft ++ rawRight)
        (normalizedLeft ++ normalizedRight)
  | consDisjoint
      {selection : Selection} {rest normalizedSelection normalizedRest :
        List Selection} :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source [selection] normalizedSelection ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source rest normalizedRest ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [selection])
        (GraphQL.Execution.collectFields schema variableValues parentType source
          rest) ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source (selection :: rest)
        (normalizedSelection ++ normalizedRest)
  | field (responseName fieldName : Name) (arguments : List Argument)
      (directives : List DirectiveApplication) (selectionSet : List Selection) :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet]
        [.field responseName fieldName arguments directives selectionSet]
  | fieldSkipped (responseName fieldName : Name) (arguments : List Argument)
      (directives : List DirectiveApplication) (selectionSet : List Selection) :
      selectionDirectivesAllowBool variableValues directives = false ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet] []
  | inlineFragmentNone (directives : List DirectiveApplication)
      {rawChild normalizedChild : List Selection} :
      (selectionDirectivesAllowBool variableValues directives = true ->
        SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source rawChild normalizedChild) ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment none directives rawChild]
        [.inlineFragment none directives normalizedChild]
  | inlineFragmentNoneFlatten (directives : List DirectiveApplication)
      {rawChild normalizedChild : List Selection} :
      selectionDirectivesAllowBool variableValues directives = true ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source rawChild normalizedChild ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment none directives rawChild] normalizedChild
  | inlineFragmentNoneSkipped (directives : List DirectiveApplication)
      (selectionSet : List Selection) :
      selectionDirectivesAllowBool variableValues directives = false ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment none directives selectionSet] []
  | inlineFragmentSome (typeCondition : Name)
      (directives : List DirectiveApplication)
      {rawChild normalizedChild : List Selection} :
      (selectionDirectivesAllowBool variableValues directives = true ->
        doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
          SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
            completionDepth parentType source rawChild normalizedChild) ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives rawChild]
        [.inlineFragment (some typeCondition) directives normalizedChild]
  | inlineFragmentSomeFlatten (typeCondition : Name)
      (directives : List DirectiveApplication)
      {rawChild normalizedChild : List Selection} :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source rawChild normalizedChild ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives rawChild]
        normalizedChild
  | inlineFragmentSomeSkipped (typeCondition : Name)
      (directives : List DirectiveApplication) (selectionSet : List Selection) :
      selectionDirectivesAllowBool variableValues directives = false ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives selectionSet] []
  | inlineFragmentSomeDoesNotApply (typeCondition : Name)
      (directives : List DirectiveApplication) (selectionSet : List Selection) :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = false ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives selectionSet] []
  | executableFieldSinglePrefixDuplicateFreshMiddle
      (first later : ExecutableField) (middle : List ExecutableField) :
      later.responseName = first.responseName ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      (∀ field, field ∈ [first] ++ (middle ++ [later]) ->
        field.parentType = parentType) ->
      (middle.map (fun field => field.responseName)).Nodup ->
      later.responseName ∉ middle.map (fun field => field.responseName) ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections ([first] ++ (middle ++ [later])))
        (executableFieldSelections ([first] ++ [later] ++ middle))
  | duplicateFieldBlockNormalize
      (first later : ExecutableField) (middle suffix : List Selection) :
      later.responseName = first.responseName ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source middle ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix) ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) ++ suffix)
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)
  | duplicateFieldBlockNormalizeHeadDisjointMiddle
      (first later : ExecutableField) (middle suffix : List Selection) :
      later.responseName = first.responseName ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst ->
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source middle ->
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix) ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) ++ suffix)
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)
  | duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix
      (first later : ExecutableField) (middle suffix : List Selection) :
      later.responseName = first.responseName ->
      ExecutableFieldsParent parentType [first, later] ->
      (∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition) ->
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst ->
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix) ->
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source middle ->
      SelectionSetCollectFieldsHeadDisjointTree schema variableValues
        parentType source suffix ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) ++ suffix)
        ((executableFieldSelections [first, later] ++
            executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source middle))) ++
          suffix)

namespace SelectionSetFreshPlanNormalizationTree

theorem normalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw normalized : List Selection} :
    SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
      completionDepth parentType source raw normalized ->
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source raw normalized := by
  intro tree
  induction tree with
  | nil =>
      exact SelectionSetFreshPlanNormalizes.nil schema resolvers variableValues
        completionDepth parentType source
  | ofNormalizes normalization =>
      exact normalization
  | ofPlan plan =>
      exact SelectionSetFreshPlanNormalizes.of_plan plan
  | ofHeadDisjointTree tree =>
      exact SelectionSetFreshPlanNormalizes.of_headDisjointTree schema
        resolvers variableValues completionDepth parentType source tree
  | executableFieldSelectionsResponseNamesNodup fields hnodup hparents =>
      exact
        SelectionSetFreshPlanNormalizes.of_executableFieldSelections_responseNamesNodup
          schema resolvers variableValues completionDepth parentType source
          fields hnodup hparents
  | appendDisjoint left right hdisjoint ihleft ihright =>
      exact SelectionSetFreshPlanNormalizes.appendDisjoint ihleft ihright
        hdisjoint
  | consDisjoint head tail hdisjoint ihhead ihtail =>
      exact SelectionSetFreshPlanNormalizes.consDisjoint ihhead ihtail
        hdisjoint
  | field responseName fieldName arguments directives selectionSet =>
      exact SelectionSetFreshPlanNormalizes.field schema resolvers
        variableValues completionDepth parentType source responseName fieldName
        arguments directives selectionSet
  | fieldSkipped responseName fieldName arguments directives selectionSet
      hskip =>
      exact SelectionSetFreshPlanNormalizes.fieldSkipped responseName fieldName
        arguments directives selectionSet hskip
  | inlineFragmentNone directives child ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentNone directives
        (fun hallows => ihchild hallows)
  | inlineFragmentNoneFlatten directives hallows child ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentNoneFlatten
        directives hallows ihchild
  | inlineFragmentNoneSkipped directives selectionSet hskip =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentNoneSkipped directives
        selectionSet hskip
  | inlineFragmentSome typeCondition directives child ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSome typeCondition
        directives (fun hallows happly => ihchild hallows happly)
  | inlineFragmentSomeFlatten typeCondition directives hallows happly child
      ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSomeFlatten
        typeCondition directives hallows happly ihchild
  | inlineFragmentSomeSkipped typeCondition directives selectionSet hskip =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSomeSkipped
        typeCondition directives selectionSet hskip
  | inlineFragmentSomeDoesNotApply typeCondition directives selectionSet
      hallows hnotApply =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSomeDoesNotApply
        typeCondition directives selectionSet hallows hnotApply
  | executableFieldSinglePrefixDuplicateFreshMiddle first later middle
      hsameResponse hlaterLookup hparents hmiddleNodup hnotMiddle =>
      exact
        SelectionSetFreshPlanNormalizes.executableFieldSinglePrefixDuplicateFreshMiddle
          first later middle hsameResponse hlaterLookup hparents hmiddleNodup
          hnotMiddle
  | duplicateFieldBlockNormalize first later middle suffix hsameResponse
      hlaterLookup hnotMiddle hmiddle hnormalized =>
      exact SelectionSetFreshPlanNormalizes.duplicateFieldBlockNormalize schema
        resolvers variableValues completionDepth parentType source first later
        middle suffix hsameResponse hlaterLookup hnotMiddle hmiddle
        hnormalized
  | duplicateFieldBlockNormalizeHeadDisjointMiddle first later middle suffix
      hsameResponse hlaterLookup hnotMiddle hmiddle hnormalized =>
      exact
        SelectionSetFreshPlanNormalizes.duplicateFieldBlockNormalizeHeadDisjointMiddle
          schema resolvers variableValues completionDepth parentType source
          first later middle suffix hsameResponse hlaterLookup hnotMiddle hmiddle
          hnormalized
  | duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix first later middle
      suffix hsameResponse hparents hlaterLookup hnotMiddle hdisjoint hmiddle
      hsuffix =>
      exact
        SelectionSetFreshPlanNormalizes.duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix
          schema resolvers variableValues completionDepth parentType source
          first later middle suffix hsameResponse hparents hlaterLookup
          hnotMiddle hdisjoint hmiddle hsuffix

theorem of_derivation
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (derivation :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        selectionSet) :
    SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
      completionDepth parentType source selectionSet selectionSet :=
  .ofPlan
    (FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
      completionDepth parentType source derivation)

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
      completionDepth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet)))
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))) :=
  .ofPlan
    (FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
      variableValues completionDepth parentType source selectionSet)

theorem of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.responseNamesNodup selectionSet ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet :=
  fun hall hfree hnodup =>
    .ofPlan
      (FreshPrefixSelectionPlan.of_allFields_directiveFree_responseNamesNodup
        schema resolvers variableValues completionDepth parentType source
        selectionSet hall hfree hnodup)

theorem of_allFields_directiveFree_normal
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    NormalForm.selectionSetNormal schema selectionSet ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet := by
  intro hall hfree hnormal
  have hnodup : NormalForm.responseNamesNodup selectionSet := by
    have hnonRedundant : NormalForm.selectionSetNonRedundant selectionSet :=
      hnormal.2
    unfold NormalForm.selectionSetNonRedundant at hnonRedundant
    exact hnonRedundant.1
  exact
    of_allFields_directiveFree_responseNamesNodup schema resolvers
      variableValues completionDepth parentType source selectionSet hall hfree
      hnodup

theorem of_rawFreshFlat_collectedCollectFields
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw : List Selection}
    (hrawFreshFlat :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source raw) :
    SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
      completionDepth parentType source raw
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source raw))) :=
  .ofNormalizes
    (SelectionSetFreshPlanNormalizes.of_rawFreshFlat_collectedCollectFields
      hrawFreshFlat)

theorem fieldAllowedDropDirectives
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true) :
    SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
      completionDepth parentType source
      [.field responseName fieldName arguments directives selectionSet]
      [.field responseName fieldName arguments [] selectionSet] :=
  .ofNormalizes
    (SelectionSetFreshPlanNormalizes.fieldAllowedDropDirectives responseName
      fieldName arguments directives selectionSet hallows)

theorem of_normalizeSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionSetDirectiveFree selectionSet ->
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        (NormalForm.normalizeSelectionSet schema parentType selectionSet)
        (NormalForm.normalizeSelectionSet schema parentType selectionSet) :=
  fun hfree =>
    .ofNormalizes
      (SelectionSetFreshPlanNormalizes.of_normalizeSelectionSet schema
        resolvers variableValues completionDepth parentType source
        selectionSet hfree)

theorem exists_fieldExecutable
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection) :
    ∃ normalizedSelectionSet,
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet]
        normalizedSelectionSet := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · exact
      ⟨[.field responseName fieldName arguments [] selectionSet],
        fieldAllowedDropDirectives responseName fieldName arguments
          directives selectionSet hallows⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      ⟨[], .fieldSkipped responseName fieldName arguments directives
        selectionSet hskip⟩

theorem exists_allFields_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ selectionSet,
      NormalForm.selectionsAllFields selectionSet ->
      NormalForm.responseNamesNodup selectionSet ->
        ∃ normalizedSelectionSet,
          SelectionSetFreshPlanNormalizationTree schema resolvers
            variableValues completionDepth parentType source selectionSet
            normalizedSelectionSet
  | [], _hall, _hnodup => by
      exact ⟨[], .nil⟩
  | selection :: rest, hall, hnodup => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hnodupCons :
              (responseName :: rest.filterMap Selection.responseName?).Nodup := by
            simpa [NormalForm.responseNamesNodup, Selection.responseName?]
              using hnodup
          have hresponseFresh :
              responseName ∉ rest.filterMap Selection.responseName? :=
            (List.nodup_cons.mp hnodupCons).1
          have hrestNodup : NormalForm.responseNamesNodup rest := by
            simpa [NormalForm.responseNamesNodup] using
              (List.nodup_cons.mp hnodupCons).2
          rcases
              exists_allFields_responseNamesNodup schema resolvers
                variableValues completionDepth parentType source rest
                hrestAll hrestNodup with
            ⟨normalizedRest, hrestTree⟩
          by_cases hallows :
              selectionDirectivesAllowBool variableValues directives = true
          · have hheadTree :
                SelectionSetFreshPlanNormalizationTree schema resolvers
                  variableValues completionDepth parentType source
                  [.field responseName fieldName arguments directives
                    selectionSet]
                  [.field responseName fieldName arguments [] selectionSet] :=
              fieldAllowedDropDirectives responseName fieldName arguments
                directives selectionSet hallows
            have hrestFree :
                NormalForm.selectionSetResponseNameFree schema parentType
                  responseName rest :=
              FreshPrefixSelectionDerivation.selectionSetResponseNameFree_of_allFields_responseNamesNodup
                schema parentType responseName rest hrestAll hresponseFresh
            have hrestNotMem :
                responseName ∉
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest).map Prod.fst :=
              FreshPrefixSelectionDerivation.collectFields_responseName_not_mem_of_allFields_responseNameFree
                schema variableValues parentType source responseName rest
                hrestAll hrestFree
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    [.field responseName fieldName arguments directives
                      selectionSet])
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest) := by
              intro candidate hleft hright
              have hleftEq : candidate = responseName := by
                simpa [GraphQL.Execution.collectFields,
                  GraphQL.Execution.collectSelection,
                  GraphQL.Execution.mergeExecutableGroups, hallows] using hleft
              exact hrestNotMem (by simpa [hleftEq] using hright)
            exact
              ⟨[.field responseName fieldName arguments [] selectionSet]
                  ++ normalizedRest,
                .consDisjoint hheadTree hrestTree hdisjoint⟩
          · have hskip :
                selectionDirectivesAllowBool variableValues directives =
                  false := by
              cases h :
                  selectionDirectivesAllowBool variableValues directives
              · rfl
              · contradiction
            have hheadTree :
                SelectionSetFreshPlanNormalizationTree schema resolvers
                  variableValues completionDepth parentType source
                  [.field responseName fieldName arguments directives
                    selectionSet] [] :=
              .fieldSkipped responseName fieldName arguments directives
                selectionSet hskip
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    [.field responseName fieldName arguments directives
                      selectionSet])
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest) := by
              intro candidate hleft _hright
              simp [GraphQL.Execution.collectFields,
                GraphQL.Execution.collectSelection,
                GraphQL.Execution.mergeExecutableGroups, hskip] at hleft
            exact
              ⟨normalizedRest,
                by
                  simpa using
                    (SelectionSetFreshPlanNormalizationTree.consDisjoint
                      hheadTree hrestTree hdisjoint)⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem exists_allFields_directiveFree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) :
    NormalForm.selectionsAllFields selectionSet ->
    NormalForm.selectionSetDirectiveFree selectionSet ->
    executionSelectionSetLookupValid schema parentType selectionSet ->
      ∃ normalizedSelectionSet,
        SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source selectionSet
          normalizedSelectionSet := by
  intro hall hfree hlookupValid
  rcases
      SelectionSetFreshPlanNormalizes.exists_allFields_directiveFree schema
        resolvers variableValues completionDepth parentType source selectionSet
        hall hfree hlookupValid with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact ⟨normalizedSelectionSet, .ofNormalizes hnormalization⟩

theorem exists_inlineFragmentNone
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (child :
      selectionDirectivesAllowBool variableValues directives = true ->
        ∃ normalizedChild,
          SelectionSetFreshPlanNormalizationTree schema resolvers
            variableValues completionDepth parentType source selectionSet
            normalizedChild) :
    ∃ normalizedSelectionSet,
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment none directives selectionSet]
        normalizedSelectionSet := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · rcases child hallows with ⟨normalizedChild, hchild⟩
    exact ⟨normalizedChild, .inlineFragmentNoneFlatten directives hallows hchild⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact ⟨[], .inlineFragmentNoneSkipped directives selectionSet hskip⟩

theorem exists_inlineFragmentSome
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (child :
      selectionDirectivesAllowBool variableValues directives = true ->
      doesFragmentTypeApplyBool schema parentType source typeCondition = true ->
        ∃ normalizedChild,
          SelectionSetFreshPlanNormalizationTree schema resolvers
            variableValues completionDepth parentType source selectionSet
            normalizedChild) :
    ∃ normalizedSelectionSet,
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives selectionSet]
        normalizedSelectionSet := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · rcases child hallows happly with ⟨normalizedChild, hchild⟩
      exact
        ⟨normalizedChild,
          .inlineFragmentSomeFlatten typeCondition directives hallows happly
            hchild⟩
    · have hnotApply :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases h :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      exact
        ⟨[],
          .inlineFragmentSomeDoesNotApply typeCondition directives selectionSet
            hallows hnotApply⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      ⟨[], .inlineFragmentSomeSkipped typeCondition directives selectionSet hskip⟩

theorem transNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw middle normalized : List Selection}
    (left :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source raw middle)
    (right :
      SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source middle normalized) :
    SelectionSetFreshPlanNormalizes schema resolvers variableValues
      completionDepth parentType source raw normalized :=
  SelectionSetFreshPlanNormalizes.trans left.normalizes right.normalizes

end SelectionSetFreshPlanNormalizationTree

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_allOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition)
    (hnotMiddle :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle).map Prod.fst)
    (hmiddle :
      VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues
        (completionDepth + 1) parentType source middle) :
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later]) (.object []) := by
  obtain ⟨suffix, hsuffix⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)))
      []
  exact
    VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
      schema resolvers variableValues completionDepth parentType source first
      later middle
        (executeField schema resolvers variableValues completionDepth source
          none
          (executableField parentType first.responseName first.fieldName
            first.arguments first.selectionSet))
        (executeField schema resolvers variableValues completionDepth source
          (some
            (executeField schema resolvers variableValues completionDepth source
              none
              (executableField parentType first.responseName first.fieldName
                first.arguments first.selectionSet)))
          (executableField parentType later.responseName later.fieldName
            later.arguments later.selectionSet))
      suffix hsameResponse hlaterLookup hnotMiddle rfl rfl hsuffix
      (hmiddle _)

theorem CollectedGroupsFieldValidationMergeCompatible_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)} :
    CollectedGroupsFieldValidationMergeCompatible (group :: groups) ->
      CollectedGroupsFieldValidationMergeCompatible groups := by
  intro hcompatible responseName fields hmem
  exact hcompatible responseName fields (by simp [hmem])

structure FieldGroupAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) : Prop where
  childEquivalent :
    ∀ selectionSet childDepth runtimeType identity,
      childDepth < depth ->
        ExecutionStateEquivalent
          { window :=
            { schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := childDepth
              parentType := runtimeType
              source := .object runtimeType identity
              selectionSet := selectionSet }
            initial := .object [] }
  absorbs :
    ∀ (prefixFields : List ExecutableField) (later : ExecutableField)
      childDepth runtimeType identity,
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
            (.object [])))
  errorNeutral :
    ∀ (prefixFields : List ExecutableField) (later : ExecutableField)
      childDepth runtimeType identity,
      childDepth < depth ->
        VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
          runtimeType (.object runtimeType identity) later.selectionSet
          (visitSubfields schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
            (.object []))

def FieldGroupAppendInvariant.depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) :
    FieldGroupAppendInvariant schema resolvers variableValues 0 :=
  { childEquivalent := by
      intro _selectionSet childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    absorbs := by
      intro _prefixFields _later childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    errorNeutral := by
      intro _prefixFields _later childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt) }

def ExecutedFieldAppendPlanState.of_appendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    (hinvariant :
      FieldGroupAppendInvariant schema resolvers variableValues depth)
    (field : ExecutableField) (fields : List ExecutableField) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields :=
  ExecutedFieldAppendPlanState.of_all_prefixes
    (by
      intro prefixTail childDepth runtimeType identity hlt _hincludes
      exact hinvariant.childEquivalent
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        childDepth runtimeType identity hlt)
    (by
      intro prefixTail later _hlater childDepth runtimeType identity hlt
      exact hinvariant.absorbs (field :: prefixTail) later childDepth
        runtimeType identity hlt)
    (by
      intro prefixTail later _hlater childDepth runtimeType identity hlt
      exact hinvariant.errorNeutral (field :: prefixTail) later childDepth
        runtimeType identity hlt)
    (by
      intro prefixTail later _hlater childDepth runtimeType identity hlt
        _hincludes
      exact hinvariant.childEquivalent
        (GraphQL.Execution.mergedFieldSelectionSet
          ((field :: prefixTail) ++ [later]))
        childDepth runtimeType identity hlt)

structure CollectedFieldGroupAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (groups : List (Name × List ExecutableField)) : Prop where
  prefixChildren :
    ∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
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
    ∀ responseName field fields prefixTail later,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
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
                (.object [])))
  errorNeutral :
    ∀ responseName field fields prefixTail later,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      later ∈ fields ->
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
  extendedChildren :
    ∀ responseName field fields prefixTail later,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
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
              initial := .object [] }

def CollectedFieldGroupAppendInvariant.depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (groups : List (Name × List ExecutableField)) :
    CollectedFieldGroupAppendInvariant schema resolvers variableValues 0 groups :=
  { prefixChildren := by
      intro _responseName _field _fields _prefixTail _hgroup _hprefix
        childDepth _runtimeType _identity hlt _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    absorbs := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    errorNeutral := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    extendedChildren := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt) }

structure CollectedFieldGroupContainedAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField)) : Prop where
  prefixChildren :
    ∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
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
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    (field :: prefixTail) }
              initial := .object [] }
  absorbs :
    ∀ responseName field fields prefixTail later,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      later ∈ fields ->
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
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
    ∀ responseName field fields prefixTail later,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      later ∈ fields ->
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
        ValueContainsObject
          (resolvers.resolve field.parentType field.fieldName field.arguments
            source)
          runtimeType identity ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))
  extendedChildren :
    ∀ responseName field fields prefixTail later,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      later ∈ fields ->
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
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((field :: prefixTail) ++ [later]) }
              initial := .object [] }

def CollectedFieldGroupContainedAppendInvariant.depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField)) :
    CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
      0 source groups :=
  { prefixChildren := by
      intro _responseName _field _fields _prefixTail _hgroup _hprefix
        childDepth _runtimeType _identity hlt _hcontains _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    absorbs := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt _hcontains
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    errorNeutral := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt _hcontains
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    extendedChildren := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt _hcontains _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt) }

def CollectedFieldGroupContainedAppendInvariant.of_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (source : ResolverValue ObjectIdentity)
    (hinvariant :
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups) :
    CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
      depth source groups :=
  { prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt _hcontains hincludes
      exact hinvariant.prefixChildren responseName field fields prefixTail
        hgroup hprefix childDepth runtimeType identity hlt hincludes
    absorbs := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains
      exact hinvariant.absorbs responseName field fields prefixTail later
        hgroup hprefix hlater childDepth runtimeType identity hlt
    errorNeutral := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains
      exact hinvariant.errorNeutral responseName field fields prefixTail later
        hgroup hprefix hlater childDepth runtimeType identity hlt
    extendedChildren := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains hincludes
      exact hinvariant.extendedChildren responseName field fields prefixTail
        later hgroup hprefix hlater childDepth runtimeType identity hlt }

theorem visitSubfields_absorbs_from_empty_object_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (childDepth : Nat) (runtimeType : Name) (identity : ObjectIdentity)
    (prefixSelectionSet laterSelectionSet : List Selection) :
    ResponseAbsorbs
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) prefixSelectionSet (.object []))
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) laterSelectionSet
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) prefixSelectionSet (.object []))) := by
  let base :=
    visitSubfields schema resolvers variableValues childDepth runtimeType
      (.object runtimeType identity) prefixSelectionSet (.object [])
  have hbaseReady : ResponseMergeReady base := by
    exact visitSubfields_response_ready schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity) prefixSelectionSet
      [] ResponseMergeReady_empty_object
  have hbaseAbsorbs : ResponseAbsorbs base base :=
    ResponseAbsorbs_refl_of_ready base hbaseReady
  obtain ⟨baseFields, hbaseObject⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues childDepth
      runtimeType (.object runtimeType identity) prefixSelectionSet []
  have hbaseFieldsReady : ResponseMergeReady (.object baseFields) := by
    rw [← hbaseObject]
    exact hbaseReady
  have hlocal :
      VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) laterSelectionSet
        base := by
    dsimp [base]
    rw [hbaseObject]
    exact
      visitSubfields_local_absorbs_from_ready schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity)
        laterSelectionSet baseFields hbaseFieldsReady
  exact
    visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity) base
      laterSelectionSet base
      (visitSubfields_absorbs_from_local_steps schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) base
        laterSelectionSet base hbaseReady hbaseAbsorbs hlocal)

def CollectedFieldGroupContainedAppendInvariant.of_prefixChildren
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hchildren :
      ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈ groups ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        ∀ childDepth runtimeType identity,
          childDepth < depth ->
          ValueContainsObject
            (resolvers.resolve field.parentType field.fieldName
              field.arguments source)
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
                  selectionSet :=
                    GraphQL.Execution.mergedFieldSelectionSet
                      (field :: prefixTail) }
                initial := .object [] })
    (herrors :
      ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
        later ∈ fields ->
        ∀ childDepth runtimeType identity,
          childDepth < depth ->
          ValueContainsObject
            (resolvers.resolve field.parentType field.fieldName
              field.arguments source)
            runtimeType identity ->
            VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (field :: prefixTail))
                (.object []))) :
    CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
      depth source groups :=
  { prefixChildren := hchildren
    absorbs := by
      intro _responseName field _fields prefixTail later _hgroup _hprefix
        _hlater childDepth runtimeType identity _hlt _hcontains
      exact
        visitSubfields_absorbs_from_empty_object_prefix schema resolvers
          variableValues childDepth runtimeType identity
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
          later.selectionSet
    errorNeutral := herrors
    extendedChildren := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt hcontains hincludes
      exact
        hchildren responseName field fields (prefixTail ++ [later]) hgroup
          (by
            intro candidate hcandidate
            rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
            · exact hprefix candidate hprefixMem
            · rcases List.mem_singleton.mp hlaterMem
              exact hlater)
          childDepth runtimeType identity hlt hcontains hincludes }

def ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hinvariant :
      CollectedFieldGroupContainedAppendInvariant schema resolvers
        variableValues depth source groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail remaining : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
    (hremaining : ∀ later, later ∈ remaining -> later ∈ fields) :
    ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
      variableValues depth parentType source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      prefixTail remaining := by
  cases remaining with
  | nil =>
      simp [ExecutableFieldsMergedCompleteContainedAppendSteps]
  | cons later rest =>
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      have hlater : later ∈ field :: fields :=
        List.mem_cons_of_mem field hlaterFields
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
          resolvers.resolve later.parentType later.fieldName later.arguments
              source =
          resolvers.resolve field.parentType field.fieldName field.arguments
              source :=
        (hgroupStable field later (by simp) hlater hsameResponse).symm
      have hprefixNext :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            candidate ∈ fields := by
        intro candidate hcandidate
        rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
        · exact hprefix candidate hprefixMem
        · rcases List.mem_singleton.mp hlaterMem
          exact hlaterFields
      have hremainingRest :
          ∀ candidate, candidate ∈ rest -> candidate ∈ fields := by
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])
      simp [ExecutableFieldsMergedCompleteContainedAppendSteps]
      exact
        ⟨hlaterResponse, hlaterParent, hfieldName, hresolveLater,
          hinvariant.prefixChildren responseName field fields prefixTail hgroup
            hprefix,
          hinvariant.absorbs responseName field fields prefixTail later hgroup
            hprefix hlaterFields,
          hinvariant.errorNeutral responseName field fields prefixTail later
            hgroup hprefix hlaterFields,
          hinvariant.extendedChildren responseName field fields prefixTail
            later hgroup hprefix hlaterFields,
          ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant_from_prefix
            hinvariant hresponses hparents hcompatible hstable responseName
            field fields (prefixTail ++ [later]) rest hgroup hprefixNext
            hremainingRest⟩

def ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hinvariant :
      CollectedFieldGroupContainedAppendInvariant schema resolvers
        variableValues depth source groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups) :
    ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
      variableValues depth parentType source responseName field
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      [] fields :=
  ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant_from_prefix
    hinvariant hresponses hparents hcompatible hstable responseName field
    fields [] fields hgroup
    (by intro candidate hmem; simp at hmem)
    (by intro later hlater; exact hlater)

structure CollectedFieldGroupLocalAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (groups : List (Name × List ExecutableField)) : Prop where
  prefixChildren :
    ∀ responseName field fields prefixTail,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
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
  errorNeutral :
    ∀ responseName field fields prefixTail later,
      (responseName, field :: fields) ∈ groups ->
      (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
      later ∈ fields ->
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (.object []))

def CollectedFieldGroupLocalAppendInvariant.of_child_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hchildren :
      ∀ childDepth runtimeType identity selectionSet,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := selectionSet }
              initial := .object [] })
    (herrors :
      ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups ->
        (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields) ->
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
                (.object []))) :
    CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues depth
      groups :=
  { prefixChildren := by
      intro _responseName field _fields prefixTail _hgroup _hprefix childDepth
        runtimeType identity hlt _hincludes
      exact hchildren childDepth runtimeType identity
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) hlt
    errorNeutral := herrors }

def CollectedFieldGroupContainedAppendInvariant.of_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (source : ResolverValue ObjectIdentity)
    (hinvariant :
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups) :
    CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
      depth source groups :=
  { prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt _hcontains hincludes
      exact hinvariant.prefixChildren responseName field fields prefixTail
        hgroup hprefix childDepth runtimeType identity hlt hincludes
    absorbs := by
      intro _responseName field _fields prefixTail later _hgroup _hprefix
        _hlater childDepth runtimeType identity _hlt _hcontains
      exact
        visitSubfields_absorbs_from_empty_object_prefix schema resolvers
          variableValues childDepth runtimeType identity
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
          later.selectionSet
    errorNeutral := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains
      exact hinvariant.errorNeutral responseName field fields prefixTail later
        hgroup hprefix hlater childDepth runtimeType identity hlt
    extendedChildren := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains hincludes
      simpa [List.cons_append] using
        hinvariant.prefixChildren responseName field fields
          (prefixTail ++ [later]) hgroup
          (by
            intro candidate hcandidate
            rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
            · exact hprefix candidate hprefixMem
            · rcases List.mem_singleton.mp hlaterMem
              exact hlater)
          childDepth runtimeType identity hlt hincludes }

def ExecutedFieldAppendPlanState.of_collectedAppendInvariant_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant :
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail remaining : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
    (hremaining : ∀ later, later ∈ remaining -> later ∈ fields) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail remaining := by
  cases remaining with
  | nil =>
      exact
        ExecutedFieldAppendPlanState.nil
          (by
            intro childDepth runtimeType identity hlt _hincludes
            exact hinvariant.prefixChildren responseName field fields
              prefixTail hgroup hprefix childDepth runtimeType identity hlt
              _hincludes)
  | cons later rest =>
      have hlater : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons
      · intro childDepth runtimeType identity hlt _hincludes
        exact hinvariant.prefixChildren responseName field fields prefixTail
          hgroup hprefix childDepth runtimeType identity hlt _hincludes
      · exact List.mem_cons_of_mem field hlater
      · exact hinvariant.absorbs responseName field fields prefixTail later
          hgroup hprefix hlater
      · exact hinvariant.errorNeutral responseName field fields prefixTail
          later hgroup hprefix hlater
      · intro childDepth runtimeType identity hlt _hincludes
        simpa [List.cons_append] using
          hinvariant.prefixChildren responseName field fields
            (prefixTail ++ [later]) hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            childDepth runtimeType identity hlt _hincludes
      · exact
          ExecutedFieldAppendPlanState.of_collectedAppendInvariant_from_prefix
            hinvariant responseName field fields (prefixTail ++ [later]) rest
            hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            (by
              intro candidate hcandidate
              exact hremaining candidate (by simp [hcandidate]))

def ExecutedFieldAppendPlanState.of_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant :
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields :=
  ExecutedFieldAppendPlanState.of_collectedAppendInvariant_from_prefix
    hinvariant responseName field fields [] fields hgroup
    (by intro candidate hmem; simp at hmem)
    (by intro later hlater; exact hlater)

def ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant :
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail remaining : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
    (hremaining : ∀ later, later ∈ remaining -> later ∈ fields) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields prefixTail remaining := by
  cases remaining with
  | nil =>
      exact
        ExecutedFieldAppendPlanState.nil
          (by
            intro childDepth runtimeType identity hlt _hincludes
            exact hinvariant.prefixChildren responseName field fields
              prefixTail hgroup hprefix childDepth runtimeType identity hlt
              _hincludes)
  | cons later rest =>
      have hlater : later ∈ fields := hremaining later (by simp)
      let base :=
        fun childDepth runtimeType identity =>
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
            (.object [])
      apply ExecutedFieldAppendPlanState.cons
      · intro childDepth runtimeType identity hlt _hincludes
        exact hinvariant.prefixChildren responseName field fields prefixTail
          hgroup hprefix childDepth runtimeType identity hlt _hincludes
      · exact List.mem_cons_of_mem field hlater
      · intro childDepth runtimeType identity hlt
        have hbaseReady :
            ResponseMergeReady (base childDepth runtimeType identity) := by
          exact visitSubfields_response_ready schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
            [] ResponseMergeReady_empty_object
        have hbaseAbsorbs :
            ResponseAbsorbs (base childDepth runtimeType identity)
              (base childDepth runtimeType identity) :=
          ResponseAbsorbs_refl_of_ready
            (base childDepth runtimeType identity) hbaseReady
        obtain ⟨baseFields, hbaseObject⟩ :=
          visitSubfields_preserves_object schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
            []
        have hbaseFieldsReady :
            ResponseMergeReady (.object baseFields) := by
          rw [← hbaseObject]
          exact hbaseReady
        have hlocal :
            VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet (base childDepth runtimeType identity) := by
          dsimp [base]
          rw [hbaseObject]
          exact
            visitSubfields_local_absorbs_from_ready schema resolvers
              variableValues childDepth runtimeType (.object runtimeType identity)
              later.selectionSet baseFields hbaseFieldsReady
        exact
          visitSubfields_absorbs_from_steps schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (base childDepth runtimeType identity) later.selectionSet
            (base childDepth runtimeType identity)
            (visitSubfields_absorbs_from_local_steps schema resolvers
              variableValues childDepth runtimeType (.object runtimeType identity)
              (base childDepth runtimeType identity)
              later.selectionSet (base childDepth runtimeType identity)
              hbaseReady hbaseAbsorbs hlocal)
      · exact hinvariant.errorNeutral responseName field fields prefixTail
          later hgroup hprefix hlater
      · intro childDepth runtimeType identity hlt _hincludes
        simpa [List.cons_append] using
          hinvariant.prefixChildren responseName field fields
            (prefixTail ++ [later]) hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            childDepth runtimeType identity hlt _hincludes
      · exact
          ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant_from_prefix
            hinvariant responseName field fields (prefixTail ++ [later]) rest
            hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            (by
              intro candidate hcandidate
              exact hremaining candidate (by simp [hcandidate]))

def ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant :
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups) :
    ExecutedFieldAppendPlanState schema resolvers variableValues depth field
      fields [] fields :=
  ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant_from_prefix
    hinvariant responseName field fields [] fields hgroup
    (by intro candidate hmem; simp at hmem)
    (by intro later hlater; exact hlater)

theorem combineVisitStatus_object_append_result
    (leftFields rightFields : List (Name × ResponseValue))
    (leftStatus rightStatus : VisitStatus) :
    (match combineVisitStatus leftStatus rightStatus with
    | .error errors => .error errors
    | .ok (_unit, errors) => .ok (leftFields ++ rightFields, errors)) =
      Result.combine List.append
        (match leftStatus with
        | .error errors => .error errors
        | .ok (_unit, errors) => .ok (leftFields, errors))
        (match rightStatus with
        | .error errors => .error errors
        | .ok (_unit, errors) => .ok (rightFields, errors)) := by
  cases leftStatus <;> cases rightStatus <;>
    simp [combineVisitStatus, GraphQL.Execution.Result.combine]

theorem executeRootSelectionSet_executableFieldSelections_append_fresh_eq_combine
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List ExecutableField)
    (hfresh :
      ∀ leftFields,
        (visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections left) (.object [])).fst =
            .object leftFields ->
        ∀ field, field ∈ right ->
          field.responseName ∉ leftFields.map Prod.fst) :
    executeRootSelectionSet schema resolvers variableValues depth parentType
      source (executableFieldSelections (left ++ right)) =
    Result.combine List.append
      (executeRootSelectionSet schema resolvers variableValues depth parentType
        source (executableFieldSelections left))
      (executeRootSelectionSet schema resolvers variableValues depth parentType
        source (executableFieldSelections right)) := by
  unfold executeRootSelectionSet
  rw [show executableFieldSelections (left ++ right) =
      executableFieldSelections left ++ executableFieldSelections right by
    simp [executableFieldSelections, List.map_append]]
  rw [visitSubfields_append_equivalence]
  obtain ⟨leftFields, hleftFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source (executableFieldSelections left) []
  let leftStatus :=
    (visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections left) (.object [])).snd
  have hleft :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections left) (.object []) =
      (.object leftFields, leftStatus) :=
    Prod.ext hleftFields rfl
  obtain ⟨rightFields, hrightFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source (executableFieldSelections right) []
  let rightStatus :=
    (visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections right) (.object [])).snd
  have hright :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections right) (.object []) =
      (.object rightFields, rightStatus) :=
    Prod.ext hrightFields rfl
  have hrightPrefix :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections right) (.object (leftFields ++ [])) =
      (.object (leftFields ++ rightFields), rightStatus) :=
    visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
      variableValues depth parentType source right leftFields [] rightFields
      rightStatus (hfresh leftFields hleftFields) hright
  have hrightPrefix' :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections right) (.object leftFields) =
      (.object (leftFields ++ rightFields), rightStatus) := by
    simpa using hrightPrefix
  rw [hleft]
  rw [hright]
  simpa [hrightPrefix'] using
    combineVisitStatus_object_append_result leftFields rightFields
      leftStatus rightStatus

namespace ExecutedFieldGroups

theorem fieldsNonempty
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} :
    ∀ {groups : List (Name × List ExecutableField)},
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source groups ->
      CollectedGroupsFieldsNonempty groups
  | [], _hgroups => CollectedGroupsFieldsNonempty_nil
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (ExecutedFieldGroups.no_empty_head hgroups)
  | (groupResponseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        subst candidateFields
        simp
      · exact fieldsNonempty hgroups.2 candidateResponseName candidateFields
          htail

theorem responseName
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} :
    ∀ {groups : List (Name × List ExecutableField)},
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source groups ->
      CollectedGroupsResponseName groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (ExecutedFieldGroups.no_empty_head hgroups)
  | (groupResponseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem candidate hcandidate
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponseName, hfields⟩
        subst candidateResponseName
        subst candidateFields
        exact hgroups.1.responseName_eq candidate hcandidate
      · exact responseName hgroups.2 candidateResponseName candidateFields
          htail candidate hcandidate

theorem parent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} :
    ∀ {groups : List (Name × List ExecutableField)},
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source groups ->
      CollectedGroupsParent parentType groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (responseName, []) :: rest, hgroups =>
      False.elim (ExecutedFieldGroups.no_empty_head hgroups)
  | (responseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem candidate hcandidate
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        subst candidateFields
        exact hgroups.1.parent_eq candidate hcandidate
      · exact parent hgroups.2 candidateResponseName candidateFields htail
          candidate hcandidate

def of_collected_groups_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) :
    ∀ (groups : List (Name × List ExecutableField)),
      CollectedGroupsFieldsNonempty groups ->
      CollectedGroupsResponseName groups ->
      CollectedGroupsParent parentType groups ->
      (∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
            some fieldDefinition) ->
      CollectedGroupsFieldValidationMergeCompatible groups ->
      CollectedGroupsResolveStable resolvers source groups ->
      (∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ExecutedFieldAppendPlanState schema resolvers variableValues depth
            field fields [] fields) ->
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source groups
  | [], _hnonempty, _hresponses, _hparents, _hlookups, _hcompatible, _hstable,
      _hplanStates =>
      ExecutedFieldGroups.nil
  | (responseName, []) :: rest, hnonempty, _hresponses, _hparents,
      _hlookups, _hcompatible, _hstable, _hplanStates => by
      have hhead : ([] : List ExecutableField) ≠ [] :=
        hnonempty responseName [] (by simp)
      exact False.elim (hhead rfl)
  | (responseName, field :: fields) :: rest, hnonempty, hresponses, hparents,
      hlookups, hcompatible, hstable, hplanStates => by
      exact
        ExecutedFieldGroups.cons
          (ExecutedFieldGroup.of_collected_group_state schema resolvers
            variableValues depth parentType source
            ((responseName, field :: fields) :: rest) responseName field
            fields (by simp) hresponses hparents hcompatible hstable
            (hlookups responseName field fields (by simp))
            (hplanStates responseName field fields (by simp)))
          (of_collected_groups_state schema resolvers variableValues depth
            parentType source rest
            (CollectedGroupsFieldsNonempty_tail hnonempty)
            (CollectedGroupsResponseName_tail hresponses)
            (CollectedGroupsParent_tail hparents)
            (by
              intro tailResponseName tailField tailFields hmem
              exact hlookups tailResponseName tailField tailFields
                (by simp [hmem]))
            (CollectedGroupsFieldValidationMergeCompatible_tail hcompatible)
            (CollectedGroupsResolveStable.tail resolvers source
              (responseName, field :: fields) rest hstable)
            (by
              intro tailResponseName tailField tailFields hmem
              exact hplanStates tailResponseName tailField tailFields
                (by simp [hmem])))

def of_collected_groups_appendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hlookups :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
            some fieldDefinition)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant :
      FieldGroupAppendInvariant schema resolvers variableValues depth) :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      groups :=
  of_collected_groups_state schema resolvers variableValues depth parentType
    source groups hnonempty hresponses hparents hlookups hcompatible hstable
    (by
      intro _responseName field fields _hmem
      exact ExecutedFieldAppendPlanState.of_appendInvariant hinvariant field
        fields)

def of_collected_groups_collectedAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hlookups :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
            some fieldDefinition)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant :
      CollectedFieldGroupAppendInvariant schema resolvers variableValues depth
        groups) :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      groups :=
  of_collected_groups_state schema resolvers variableValues depth parentType
    source groups hnonempty hresponses hparents hlookups hcompatible hstable
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedAppendInvariant hinvariant
          responseName field fields hgroup)

def of_collected_groups_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hlookups :
      ∀ responseName field fields,
        (responseName, field :: fields) ∈ groups ->
          ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
            some fieldDefinition)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant :
      CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups) :
    ExecutedFieldGroups schema resolvers variableValues depth parentType source
      groups :=
  of_collected_groups_state schema resolvers variableValues depth parentType
    source groups hnonempty hresponses hparents hlookups hcompatible hstable
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant hinvariant
          responseName field fields hgroup)

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hgroups :
      ExecutedFieldGroups schema resolvers variableValues depth parentType
        source groups)
    (hnodup : PairKeysNodup groups) :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source groups := by
  unfold ExecutableGroupsFlatSpecEquivalent
  unfold ExecutableFieldsFlatSpecEquivalent
  induction groups with
  | nil =>
      simp [collectedExecutableFields, executableFieldSelections,
        executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields,
        GraphQL.Execution.executeCollectedFields, visitSubfields, visitOk]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      cases fields with
      | nil =>
          exact False.elim (ExecutedFieldGroups.no_empty_head hgroups)
      | cons field fieldsTail =>
          have hhead :
              ExecutedFieldGroup schema resolvers variableValues depth
                parentType source responseName field fieldsTail :=
            hgroups.1
          have htail :
              ExecutedFieldGroups schema resolvers variableValues depth
                parentType source rest :=
            hgroups.2
          have htailNodup : PairKeysNodup rest :=
            PairKeysNodup.tail hnodup
          have htailEq := ih htail htailNodup
          unfold ExecutableFieldsFlatSpecEquivalent at htailEq
          have hnonempty :
              CollectedGroupsFieldsNonempty
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroups.fieldsNonempty hgroups
          have hresponses :
              CollectedGroupsResponseName
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroups.responseName hgroups
          have hparents :
              CollectedGroupsParent parentType
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroups.parent hgroups
          have hspec :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues (depth + 1) parentType source
                  (executableFieldSelections
                    (collectedExecutableFields
                      ((responseName, field :: fieldsTail) :: rest))) =
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues (depth + 1) source
                  ((responseName, field :: fieldsTail) :: rest) :=
            specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
              schema resolvers variableValues (depth + 1) parentType source
              ((responseName, field :: fieldsTail) :: rest) hnodup hnonempty
              hresponses hparents
          have htailSpec :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues (depth + 1) parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) =
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues (depth + 1) source rest :=
            specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
              schema resolvers variableValues (depth + 1) parentType source
              rest htailNodup
              (ExecutedFieldGroups.fieldsNonempty htail)
              (ExecutedFieldGroups.responseName htail)
              (ExecutedFieldGroups.parent htail)
          have hheadEq :
              executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
                GraphQL.Execution.executeField schema resolvers variableValues
                  (depth + 1) source responseName (field :: fieldsTail) :=
            hhead.mergedComplete
          have happend :
              executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections
                    ((field :: fieldsTail) ++
                      collectedExecutableFields rest)) =
                Result.combine List.append
                  (executeRootSelectionSet schema resolvers variableValues
                    (depth + 1) parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (executeRootSelectionSet schema resolvers variableValues
                    (depth + 1) parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
            apply
              executeRootSelectionSet_executableFieldSelections_append_fresh_eq_combine
                schema resolvers variableValues (depth + 1) parentType source
                (field :: fieldsTail) (collectedExecutableFields rest)
            intro leftFields hleftFields tailField htailField hmemLeft
            have hleftKey :
                tailField.responseName =
                  responseName := by
              have hcollectKey :
                  tailField.responseName ∈
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source
                      (executableFieldSelections (field :: fieldsTail))).map
                      Prod.fst :=
                visitSubfields_object_empty_key_mem_collectFields schema
                  resolvers variableValues (depth + 1) parentType source
                  (executableFieldSelections (field :: fieldsTail))
                  leftFields tailField.responseName hleftFields hmemLeft
              have hfieldKey :
                  tailField.responseName ∈
                    (field :: fieldsTail).map
                      (fun field => field.responseName) :=
                (collectFields_executableFieldSelections_key_mem_global schema
                  variableValues parentType source (field :: fieldsTail)
                  tailField.responseName).mp hcollectKey
              rcases List.mem_map.mp hfieldKey with
                ⟨headField, hheadField, hkey⟩
              rw [← hkey]
              exact hhead.responseName_eq headField hheadField
            have htailGroupKey :
                tailField.responseName ∈ rest.map Prod.fst := by
              exact
                collectedExecutableFields_responseName_mem rest
                  (ExecutedFieldGroups.responseName htail) tailField
                  htailField
            have hheadNotTail : responseName ∉ rest.map Prod.fst :=
              PairKeysNodup.head_not_mem_tail hnodup
            exact hheadNotTail (by simpa [hleftKey] using htailGroupKey)
          calc
            executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source
                (executableFieldSelections
                  (collectedExecutableFields
                    ((responseName, field :: fieldsTail) :: rest)))
                =
              executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source
                (executableFieldSelections
                  ((field :: fieldsTail) ++ collectedExecutableFields rest)) := by
                simp [collectedExecutableFields]
            _ =
                Result.combine List.append
                (executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections (field :: fieldsTail)))
                (executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest))) :=
                happend
            _ =
              Result.combine List.append
                (GraphQL.Execution.executeField schema resolvers
                  variableValues (depth + 1) source responseName
                  (field :: fieldsTail))
                (GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues (depth + 1) source rest) := by
                rw [hheadEq, htailEq, htailSpec]
            _ =
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues (depth + 1) source
                ((responseName, field :: fieldsTail) :: rest) := by
                simp [GraphQL.Execution.executeCollectedFields]
            _ =
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues (depth + 1) parentType source
                (executableFieldSelections
                  (collectedExecutableFields
                    ((responseName, field :: fieldsTail) :: rest))) :=
                hspec.symm

end ExecutedFieldGroups

end ExecutionUngrouped
end Algorithms

end GraphQL
